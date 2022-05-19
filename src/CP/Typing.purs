module Language.CP.Typing where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Error.Class (throwError)
import Control.Monad.Reader (asks)
import Control.Monad.State (gets, modify_)
import Data.Array (elem, head, notElem, null, unzip)
import Data.Either (Either(..))
import Data.Foldable (all, find, foldr, traverse_)
import Data.List (List(..), filter, last, singleton, sort, zip, (:))
import Data.Map (insert)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set, member)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Context (Checking, LetTrans, Pos(..), TypeError(..), Typing, addSort, addTmBind, addTyBind, fromState, localPos, lookupTmBind, lookupTyBind, runTyping, throwTypeError, toList)
import Language.CP.Desugar (deMP, desugar)
import Language.CP.Subtype.Source (isTopLike, showSubtypeTrace, tyRcd, (<:), (===))
import Language.CP.Syntax.Common (BinOp(..), Label, Name, UnOp(..))
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source (Def(..), Prog(..), Ty(..), intercalate')
import Language.CP.Syntax.Source as S
import Language.CP.Transform (expand, transform, transform', transformTyDef)
import Language.CP.TypeDiff (tyDiff)
import Language.CP.Util (foldr1, unsafeFromJust, (<+>))
import Partial.Unsafe (unsafeCrashWith)

infer :: S.Tm -> Typing (C.Tm /\ S.Ty)
infer (S.TmInt i)    = pure $ C.TmInt i /\ S.TyInt
infer (S.TmDouble d) = pure $ C.TmDouble d /\ S.TyDouble
infer (S.TmString s) = pure $ C.TmString s /\ S.TyString
infer (S.TmBool b)   = pure $ C.TmBool b /\ S.TyBool
infer S.TmUnit       = pure $ C.TmUnit /\ S.TyTop
infer S.TmUndefined  = pure $ C.TmUndefined /\ S.TyBot
-- Int is always prioritized over Double: e.g. -(1.0,2) = -2
infer (S.TmUnary Neg e) = do
  e' /\ t <- infer e
  let core ty ty' = C.TmUnary Neg (C.TmAnno e' ty') /\ ty
  if t <: S.TyInt then pure $ core S.TyInt C.TyInt
  else if t <: S.TyDouble then pure $ core S.TyDouble C.TyDouble
  else throwTypeError $ "Neg is not defined for" <+> show t
infer (S.TmUnary Not e) = do
  e' /\ t <- infer e
  let core = C.TmUnary Not (C.TmAnno e' C.TyBool) /\ S.TyBool
  if t <: S.TyBool then pure core
  else throwTypeError $ "Not is not defined for" <+> show t
infer (S.TmUnary Len e) = do
  e' /\ t <- infer e
  let core = C.TmUnary Len e' /\ S.TyInt
  case t of S.TyArray _ -> pure core
            _ -> throwTypeError $ "Len is not defined for" <+> show t
infer (S.TmBinary (Arith op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core ty ty' = C.TmBinary (Arith op) (C.TmAnno e1' ty') (C.TmAnno e2' ty') /\ ty
  if t1 <: S.TyInt && t2 <: S.TyInt then pure $ core S.TyInt C.TyInt
  else if t1 <: S.TyDouble && t2 <: S.TyDouble then pure $ core S.TyDouble C.TyDouble
  else throwTypeError $
    "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary (Comp op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core ty' = C.TmBinary (Comp op) (C.TmAnno e1' ty') (C.TmAnno e2' ty') /\ S.TyBool
  if t1 <: S.TyInt && t2 <: S.TyInt then pure $ core C.TyInt
  else if t1 <: S.TyDouble && t2 <: S.TyDouble then pure $ core C.TyDouble
  else if t1 <: S.TyString && t2 <: S.TyString then pure $ core C.TyString
  else if t1 <: S.TyBool && t2 <: S.TyBool then pure $ core C.TyBool
  else throwTypeError $
    "CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary (Logic op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core = C.TmBinary (Logic op) (C.TmAnno e1' C.TyBool) (C.TmAnno e2' C.TyBool) /\ S.TyBool
  if t1 <: S.TyBool && t2 <: S.TyBool then pure core
  else throwTypeError $
    "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Append e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  if t1 <: S.TyString && t2 <: S.TyString then
    pure $ C.TmBinary Append (C.TmAnno e1' C.TyString)
                             (C.TmAnno e2' C.TyString) /\ S.TyString
  else case t1, t2 of
    S.TyArray t1', S.TyArray t2' ->
      let core el er ty = C.TmBinary Append el er /\ ty in
      if t1' === t2' then pure $ core e1' e2' t1
      else if t2' <: t1' then do
        t' <- transform t1
        pure $ core e1' (C.TmAnno e2' t') t1
      else if t1' <: t2' then do
        t' <- transform t2
        pure $ core (C.TmAnno e1' t') e2' t2
      else throwTypeError $
        "Append expected two arrays of equivalent types or subtypes," <+>
        "but got" <+> show t1' <+> "and" <+> show t2'
    _, _ -> throwTypeError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Index e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of S.TyArray t1' | t2 <: S.TyInt ->
               pure $ C.TmBinary Index e1' (C.TmAnno e2' C.TyInt) /\ t1'
             _ -> throwTypeError $ "Index is not defined between" <+>
                                   show t1 <+> "and" <+> show t2
-- this unit-coalescing operator is only used for record default values
infer (S.TmBinary Coalesce (S.TmPrj e1 label) e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case selectLabel t1 label true of
    Just t | t2 <: t -> do
      t' <- transform t
      pure $ C.TmBinary Coalesce (C.TmPrj e1' label) (C.TmAnno e2' t') /\ t
    _ -> throwTypeError $
      label <> "'s default value does not match its interface"
infer (S.TmIf e1 e2 e3) = do
  e1' /\ t1 <- infer e1
  if t1 <: S.TyBool then do
    e2' /\ t2 <- infer e2
    e3' /\ t3 <- infer e3
    let core et ef ty = C.TmIf (C.TmAnno e1' C.TyBool) et ef /\ ty
    if t2 === t3 then pure $ core e2' e3' t2
    else if t3 <: t2 then do
      t' <- transform t2
      pure $ core e2' (C.TmAnno e3' t') t2
    else if t2 <: t3 then do
      t' <- transform t3
      pure $ core (C.TmAnno e2' t') e3' t3
    else throwTypeError $
      "if-branches expected two equivalent types or subtypes, but got" <+>
      show t2 <+> "and" <+> show t3
  else throwTypeError $ "if-condition expected Bool, but got" <+> show t1
infer (S.TmVar x) = (C.TmVar x /\ _) <$> lookupTmBind x
infer (S.TmApp e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case app t1 t2 of Just t -> pure $ C.TmApp e1' e2' false /\ t
                    _ -> (C.TmApp e1' e2' true /\ _) <$> distApp t1 (Left t2)
  where app :: S.Ty -> S.Ty -> Maybe S.Ty
        app (S.TyArrow targ tret) t | t === targ = Just tret
        app _ _ = Nothing
infer (S.TmAbs (S.TmParam x (Just targ) : Nil) e) = do
  t1 /\ targ' <- transform' targ
  e' /\ tret <- addTmBind x targ' $ infer e
  t2 <- transform tret
  pure $ C.TmAbs x e' t1 t2 false /\ S.TyArrow targ' tret
infer (S.TmAbs (S.TmParam x Nothing : Nil) _) = throwTypeError $
  "lambda parameter" <+> show x <+> "should be annotated with a type"
infer (S.TmAbs (S.WildCard _ : Nil) _) = throwTypeError $
  "record wildcards should only occur in traits with interfaces implemented"
infer (S.TmAnno e ta) = do
  e' /\ t <- infer e
  t' /\ ta' <- transform' ta
  if t <: ta' then pure $ C.TmAnno e' t' /\ ta'
  else throwTypeError $
    "annotated" <+> show ta <+> "is not a supertype of inferred" <+> show t
infer (S.TmMerge S.Neutral e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1, t2 of
    S.TyTop, _ -> pure $ e2' /\ t2
    _, S.TyTop -> pure $ e1' /\ t1
    S.TyTrait ti1 to1, S.TyTrait ti2 to2 -> do
      disjoint to1 to2
      trait "#self" (C.TmMerge (appToSelf e1') (appToSelf e2')) (S.TyAnd ti1 ti2) (S.TyAnd to1 to2)
    _, _ -> do
      disjoint t1 t2
      pure $ C.TmMerge e1' e2' /\ S.TyAnd t1 t2
  where appToSelf e = C.TmApp e (C.TmVar "#self") true
infer (S.TmMerge S.Leftist e1 e2) =
  infer $ S.TmMerge S.Neutral e1 (S.TmDiff e2 e1)
infer (S.TmMerge S.Rightist e1 e2) =
  infer $ S.TmMerge S.Neutral (S.TmDiff e1 e2) e2
infer (S.TmRcd (S.RcdField _ l Nil (Left e) : Nil)) = do
  e' /\ t <- infer e
  t' <- transform t
  pure $ C.TmRcd l t' e' /\ tyRcd l t false
infer (S.TmPrj e l) = do
  e' /\ t <- infer e
  t' <- transform t
  let r /\ tr = case t of S.TyRec _ _ -> C.TmUnfold t' e' /\ S.unfold t
                          _ -> e' /\ t
  case selectLabel tr l false of
    Just tl -> pure $ C.TmPrj r l /\ tl
    _ -> throwTypeError $ "label" <+> show l <+> "is absent in" <+> show t
infer (S.TmTApp e ta) = do
  e' /\ tf <- infer e
  t' /\ ta' <- transform' ta
  t <- distApp tf (Right ta')
  pure $ C.TmTApp e' t' /\ t 
infer (S.TmTAbs ((a /\ Just td) : Nil) e) = do
  t1 /\ td' <- transform' td
  e' /\ t <- addTyBind a td' $ infer e
  t2 <- addTyBind a td' $ transform t
  pure $ C.TmTAbs a t1 e' t2 false /\ S.TyForall a td' t
infer (S.TmLet x Nil Nil e1 e2) = do
  e1' /\ t1 <- infer e1
  letIn x e1' t1 $ addTmBind x t1 $ infer e2
infer (S.TmLetrec x Nil Nil t e1 e2) = do
  e1' /\ t' /\ t1 <- inferRec x e1 t
  letIn x (C.TmFix x e1' t1) t' $ addTmBind x t' $ infer e2
-- TODO: find a more efficient algorithm
infer (S.TmOpen e1 e2) = do
  e1' /\ t1 <- infer e1
  let ls = foldr (\l s -> (l /\ unsafeFromJust (selectLabel t1 l false)) : s)
           Nil (collectLabels t1)
  let ty = foldr (uncurry addTmBind) (infer e2) ls
  letIn opened e1' t1 $
    foldr (\(l /\ t) -> letIn l (C.TmPrj (C.TmVar opened) l) t) ty ls
  where opened = "#opened"
infer (S.TmUpdate rcd fields) = do
  rcd' /\ t <- infer rcd
  fields' <- for fields \(l /\ e) -> do
    e' /\ t' <- infer e
    t'' <- transform t'
    pure $ C.TmRcd l t'' e' /\ t'
  let t' = S.TyRcd $ rcdTy <$> fields'
  if t <: t' then do
    d <- tyDiff t t'
    d' <- transform d
    let merge = if isTopLike d then identity else C.TmMerge (C.TmAnno rcd' d')
        updating = foldr1 C.TmMerge (fst <$> fields')
    pure $ merge updating /\ t
  else throwTypeError $ "cannot safely update the record" <+> show rcd
  where rcdTy :: C.Tm /\ S.Ty -> S.RcdTy
        rcdTy (C.TmRcd l _ _ /\ t) = S.RcdTy l t false
        rcdTy _ = unsafeCrashWith "CP.Typing.infer (S.TmUpdate): unreachable code"
infer (S.TmTrait (Just (self /\ Just t)) (Just sig) me1 ne2) = do
  t' <- expand t
  sig' <- expand sig
  let e2 = inferFromSig sig' ne2
  ret /\ tret <- case me1 of
    Just e1 -> do
      -- self may be used in e1 (e.g. trait [self:T] inherits f self => ...)
      -- this self has nothing to do with that self in the super-trait
      e1' /\ t1 <- addTmBind self t' $ infer e1
      case t1 of
        S.TyTrait ti to -> do
          if t' <: ti then do
            e2' /\ t2 <-
              addTmBind self t' $ addTmBind "super" to $ infer e2
            let to' = override to e2
            disjoint to' t2
            let tret = S.TyAnd to' t2
            to'' <- transform to'
            letIn "super" (C.TmApp e1' (C.TmVar self) true) to $ pure $
              (C.TmMerge (C.TmAnno (C.TmVar "super") to'') e2') /\ tret
          else throwTypeError $ "self-type" <+> show t <+>
            "is not a subtype of inherited self-type" <+> show ti
        _ -> throwTypeError $ "expected to inherit a trait, but got" <+> show t1
    Nothing -> addTmBind self t' $ infer e2
  case tret `impl` sig' of -- TODO: is this choice really correct?
    Just tret' -> trait self ret t' tret'
    Nothing -> throwTypeError $ "the trait does not implement" <+> show sig <+>
      "because the following subtyping does not hold:\n" <> showSubtypeTrace tret sig'
  where
    -- TODO: inference is not complete
    inferFromSig :: S.Ty -> S.Tm -> S.Tm
    inferFromSig rs@(S.TyAnd _ _) e = inferFromSig (S.TyRcd $ combineRcd rs) e
    inferFromSig s@(S.TyRec _ ty) e = S.TmFold s (inferFromSig ty e)
    inferFromSig s (S.TmPos p e) = S.TmPos p (inferFromSig s e)
    inferFromSig s (S.TmOpen e1 e2) = S.TmOpen e1 (inferFromSig s e2)
    inferFromSig s (S.TmMerge bias e1 e2) =
      S.TmMerge bias (inferFromSig s e1) (inferFromSig s e2)
    inferFromSig (S.TyRcd xs) r@(S.TmRcd (S.RcdField o l Nil (Left e) : Nil)) =
      case last $ filterRcd (_ == l) xs of
        Just (S.RcdTy _ ty _) ->
          S.TmRcd (singleton (S.RcdField o l Nil (Left (inferFromSig ty e))))
        _ -> r
    inferFromSig (S.TyRcd xs)
        (S.TmRcd (S.DefaultPattern pat@(S.MethodPattern _ label _ _) : Nil)) =
      desugar $ S.TmRcd $ filterRcd (_ `notElem` patterns label) xs <#>
        \(S.RcdTy l ty _) ->
          let params /\ ty' = paramsAndInnerTy ty
              e = inferFromSig ty' (desugar (deMP pat)) in
          S.RcdField false l params (Left e)
      where patterns :: Label -> Array Label
            patterns l = patternsFromRcd (S.TmMerge S.Neutral (fromMaybe S.TmUnit me1) ne2) l
            patternsFromRcd :: S.Tm -> Label -> Array Label
            patternsFromRcd (S.TmPos _ e) l = patternsFromRcd e l
            patternsFromRcd (S.TmOpen _ e) l = patternsFromRcd e l
            patternsFromRcd (S.TmMerge _ e1 e2) l =
              patternsFromRcd e1 l <> patternsFromRcd e2 l
            patternsFromRcd (S.TmRcd (S.RcdField _ l' _ (Left e) : Nil)) l =
              if innerLabel e == l then [l'] else []
            patternsFromRcd _ _ = []
            innerLabel :: S.Tm -> Label
            innerLabel (S.TmPos _ e) = innerLabel e
            innerLabel (S.TmOpen _ e) = innerLabel e
            innerLabel (S.TmAbs _ e) = innerLabel e
            innerLabel (S.TmTrait _ _ _ e) = innerLabel e
            innerLabel (S.TmRcd (S.RcdField _ l _ _ : Nil)) = l
            innerLabel _ = "#nothing"
            paramsAndInnerTy :: S.Ty -> S.TmParamList /\ S.Ty
            paramsAndInnerTy (S.TyArrow targ tret) =
              let params /\ ty = paramsAndInnerTy tret in
              (S.TmParam "_" (Just targ) : params) /\ ty
            paramsAndInnerTy ty = Nil /\ ty
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (S.TmParam x mt : Nil) e) =
      S.TmAbs (singleton (S.TmParam x (mt <|> Just targ))) (inferFromSig tret e)
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (S.WildCard defaults : Nil) e)
      -- TODO: better error messages for mismatch
      | defaults `matchOptional` targ =
        S.TmAbs (singleton (S.TmParam wildcardName (Just targ)))
                (open defaults (S.TmOpen wildcardVar (inferFromSig tret e)))
      where wildcardName = "#wildcard"
            wildcardVar = S.TmVar wildcardName
            open fields body = foldr letFieldIn body fields
            letFieldIn (l /\ e1) e2 = S.TmLet l Nil Nil
              (S.TmBinary Coalesce (S.TmPrj wildcardVar l) e1) e2
    inferFromSig (S.TyTrait ti to) (S.TmTrait (Just (self' /\ mt)) sig' e1 e2) =
      let t' = fromMaybe ti mt in
      S.TmTrait (Just (self' /\ Just t')) sig'
                (inferFromSig to <$> e1) (inferFromSig to e2)
    inferFromSig (S.TyForall a td ty) (S.TmTAbs ((a' /\ td') : Nil) e) =
      S.TmTAbs (singleton (a' /\ (td' <|> Just td))) (inferFromSig ty' e)
      where ty' = identity $ S.tySubst a (S.TyVar a') ty
    inferFromSig _ e = e
    combineRcd :: S.Ty -> S.RcdTyList
    combineRcd (S.TyAnd (S.TyRcd xs) (S.TyRcd ys)) = xs <> ys
    combineRcd (S.TyAnd l (S.TyRcd ys)) = combineRcd l <> ys
    combineRcd (S.TyAnd (S.TyRcd xs) r) = xs <> combineRcd r
    combineRcd (S.TyAnd l r) = combineRcd l <> combineRcd r
    combineRcd (S.TyRcd rcd) = rcd
    combineRcd _ = Nil
    filterRcd :: (Label -> Boolean) -> S.RcdTyList -> S.RcdTyList
    filterRcd f = filter \(S.RcdTy l _ _) -> f l
    override :: S.Ty -> S.Tm -> S.Ty
    override ty e = let ls = selectOverride e in
      if null ls then ty else removeOverride ty ls
      where selectOverride :: S.Tm -> Array Label
            selectOverride (S.TmPos _ e0) = selectOverride e0
            selectOverride (S.TmOpen _ e0) = selectOverride e0
            selectOverride (S.TmMerge _ e1 e2) = selectOverride e1 <> selectOverride e2
            -- TODO: only override the inner field if it's a method pattern
            selectOverride (S.TmRcd (S.RcdField true l _ _ : Nil)) = [l]
            selectOverride _ = []
            -- TODO: make sure every field overrides some field in super-trait
            removeOverride :: S.Ty -> Array Label -> S.Ty
            removeOverride (S.TyAnd t1 t2) ls =
              let t1' = removeOverride t1 ls
                  t2' = removeOverride t2 ls in
              case t1', t2' of
                S.TyTop, S.TyTop -> S.TyTop
                S.TyTop, _       -> t2'
                _,       S.TyTop -> t1'
                _,       _       -> S.TyAnd t1' t2'
            removeOverride (S.TyRcd rts) ls
              | all (_ `elem` ls) ((\(S.RcdTy l _ _) -> l) <$> rts) = S.TyTop
            removeOverride typ _ = typ
    matchOptional :: S.DefaultFields -> S.Ty -> Boolean
    matchOptional def ty = sort labels == sort labels' -- identical up to permutation
      where labels = fst <$> def
            labels' = foldr (\(S.RcdTy l _ opt) s -> if opt then l : s else s)
                            Nil (combineRcd ty)
    impl :: S.Ty -> S.Ty -> Maybe S.Ty
    impl t1 t@(S.TyNominal _ _ t2) = if t1 <: t2 then Just t else Nothing
    impl t1 t2 = if t1 <: t2 then Just t1 else Nothing
infer (S.TmTrait (Just (self /\ Nothing)) sig e1 e2) =
  infer $ S.TmTrait (Just (self /\ Just S.TyTop)) sig e1 e2
infer (S.TmNew e) = do
  e' /\ t <- infer e
  case t of
    S.TyTrait ti to ->
      if to <: ti then do
        to' <- transform to
        pure $ C.TmFix "#self" (C.TmApp e' (C.TmVar "#self") true) to' /\ to
      else throwTypeError $ "input type is not a supertype of output type in" <+>
                            "Trait<" <+> show ti <+> "=>" <+> show to <+> ">"
    _ -> throwTypeError $ "new expected a trait, but got" <+> show t
infer (S.TmForward e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of
    S.TyTrait ti to ->
      if t2 <: ti then pure $ C.TmApp e1' e2' true /\ to
      else throwTypeError $ "expected to forward to a subtype of" <+> show ti <>
                            ", but got" <+> show t2
    _ -> throwTypeError $ "expected to forward from a trait, but got" <+> show t1
infer (S.TmExclude e te) = do
  e' /\ t <- infer e
  te' <- expand te
  -- `check` helps to make sure `l` was present in `e` before exclusion,
  -- since the field removal `e \ l` desugars to `e \\ {l : Bot}`
  let check = case te' of S.TyRcd (S.RcdTy l S.TyBot false : Nil) -> checkLabel l
                          _ -> const $ pure unit
  case t of
    S.TyTrait ti to -> do
      check to
      d <- tyDiff to te'
      let t' = S.TyTrait ti d
      t'' <- transform t'
      pure $ C.TmAnno e' t'' /\ t'
    _ -> do
      check t
      d <- tyDiff t te'
      d' <- transform d
      pure $ C.TmAnno e' d' /\ d
  where checkLabel :: Label -> S.Ty -> Typing Unit
        checkLabel l t = if l `member` collectLabels t then pure unit
                         else throwTypeError $ "label" <+> show l <+> "is absent in" <+> show e
infer (S.TmRemoval e l) = do
  infer $ S.TmExclude e (S.TyRcd (singleton (S.RcdTy l S.TyBot false)))
infer (S.TmDiff e1 e2) = do
  e1' /\ t1 <- infer e1
  _ /\ t2 <- infer e2
  case t1, t2 of
    S.TyTrait ti to1, S.TyTrait _ to2 -> do
      d <- tyDiff to1 to2
      d' <- transform d
      trait "#self" (C.TmAnno (C.TmApp e1' (C.TmVar "#self") true) d') ti d
    _, _ -> do
      d <- tyDiff t1 t2
      d' <- transform d
      pure $ C.TmAnno e1' d' /\ d
infer (S.TmRename e old new) = do
  _ /\ t <- infer e
  case t of
    S.TyTrait ti _ ->
      case selectLabel ti old false of
        Just tl -> do
          -- e [old <- new] := trait [self] =>
          --   let super = self [new <- old] in
          --   (e ^ super) [old <- new]
          let super = S.TmRename (S.TmVar "#self") new old
              body = S.TmRename (S.TmForward e super) old new
          tself <- S.TyAnd (tyRcd new tl false) <$> tyDiff ti (tyRcd old S.TyBot false)
          ret /\ tret <- addTmBind "#self" tself $ infer body
          trait "#self" ret tself tret
        Nothing -> do
          -- e [old <- new] := trait [self] => (e ^ self) [old <- new]
          let body = (S.TmRename (S.TmForward e (S.TmVar "#self")) old new)
          ret /\ tret <- addTmBind "#self" ti $ infer body
          trait "#self" ret ti tret
    _ ->
      -- e [old <- new] := e \ old , {new = e.old}
      infer $ S.TmMerge S.Neutral (S.TmRemoval e old)
        (S.TmRcd (singleton (S.RcdField false new Nil (Left (S.TmPrj e old)))))
infer (S.TmFold t e) = do
  t' /\ tr <- transform' t
  ensureTyRec tr
  e' /\ t'' <- infer e
  if t'' <: S.unfold tr then pure $ C.TmFold t' e' /\ tr
  else throwTypeError $ "cannot fold" <+> show e <+> "to" <+> show t
infer (S.TmUnfold t e) = do
  t' /\ tr <- transform' t
  ensureTyRec tr
  e' /\ t'' <- infer e
  if t'' <: tr then pure $ C.TmUnfold t' e' /\ S.unfold tr
  else throwTypeError $ "cannot unfold" <+> show e <+> "to" <+> show t
infer (S.TmToString e) = do
  e' /\ t <- infer e
  if t == S.TyInt || t == S.TyDouble || t == S.TyString || t == S.TyBool
  then pure $ C.TmToString e' /\ S.TyString
  else throwTypeError $ "cannot show" <+> show t
infer (S.TmArray arr) = do
  if null arr then
    pure $ C.TmArray C.TyBot [] /\ S.TyArray S.TyBot
  else do
    ets <- traverse infer arr
    let es /\ ts = unzip ets
        t = unsafeFromJust $ head ts
    t' <- transform t
    if all (_ === t) ts then pure $ C.TmArray t' es /\ S.TyArray t
    else throwTypeError $ "elements of an array should all have the same type" <>
                          ", but got" <+> show (S.TmArray arr)
infer (S.TmDoc doc) = localPos f $ infer doc
  where f (Pos p e _) = Pos p e true
        f UnknownPos = UnknownPos
-- TODO: save original terms instead of desugared ones
infer (S.TmPos p e) = localPos f $ infer e
  where f (Pos _ _ inDoc) = Pos p e inDoc
        f UnknownPos = Pos p e false
infer e = throwTypeError $ "expected a desugared term, but got" <+> show e

inferRec :: Name -> S.Tm -> S.Ty -> Typing (C.Tm /\ S.Ty /\ C.Ty)
inferRec x e t = do
  t'' /\ t' <- transform' t
  e' /\ t1 <- addTmBind x t' $ infer e
  if t1 <: t' then pure $ (if t1 === t' then e' else C.TmAnno e' t'') /\ t' /\ t''
  else throwTypeError $
    "annotated" <+> show t <+> "is not a supertype of inferred" <+> show t1

distApp :: S.Ty -> Either S.Ty S.Ty -> Typing S.Ty
distApp (S.TyArrow targ tret) (Left t) | t <: targ = pure tret
                                       | otherwise = throwTypeError $
  "expected the argument type to be a subtype of the parameter type, but\n" <>
    showSubtypeTrace t targ
distApp (S.TyForall a td t) (Right ta) = disjoint ta td $> S.tySubst a ta t
distApp (S.TyAnd t1 t2) t = do
  t1' <- distApp t1 t
  t2' <- distApp t2 t
  pure $ S.TyAnd t1' t2'
distApp t _ = throwTypeError $ "expected an applicable type, but got" <+> show t

disjoint :: S.Ty -> S.Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (S.TyArrow _ t1) (S.TyArrow _ t2) = disjoint t1 t2
disjoint (S.TyAnd t1 t2) t3 = disjoint t1 t3 *> disjoint t2 t3
disjoint t1 (S.TyAnd t2 t3) = disjoint (S.TyAnd t2 t3) t1
disjoint (S.TyRcd rts1) (S.TyRcd rts2) = traverse_ (uncurry check) $ zip rts1 rts2
  where check (S.RcdTy l1 t1 _) (S.RcdTy l2 t2 _) | l1 == l2  = disjoint t1 t2
                                                  | otherwise = pure unit
disjoint (S.TyVar a) (S.TyVar b) = disjointVar a (S.TyVar b) <|> disjointVar b (S.TyVar a)
disjoint (S.TyVar a) t = disjointVar a t
disjoint t (S.TyVar a) = disjointVar a t
disjoint (S.TyForall a1 td1 t1) (S.TyForall a2 td2 t2) =
  disjointTyBind a1 t1 a2 t2 (S.TyAnd td1 td2)
disjoint (S.TyRec a1 t1) (S.TyRec a2 t2) = disjointTyBind a1 t1 a2 t2 S.TyBot
disjoint t1 t2 | t1 /= t2  = pure unit
               | otherwise = throwTypeError $
  "expected two disjoint types, but got" <+> show t1 <+> "and" <+> show t2

disjointVar :: Name -> S.Ty -> Typing Unit
disjointVar a t = do
  mt' <- lookupTyBind a
  case mt' of
    Just t' -> if t' <: t then pure unit else throwTypeError $
      "type variable" <+> show a <+> "is not disjoint from" <+> show t
    _ -> do
      tyAliasEnv <- asks (_.tyAliasEnv)
      throwTypeError $ "type variable" <+> show a <+> "is undefined\n" <>
        "currently defined type aliases:\n" <> intercalate' "\n"
          ((\(x /\ ty) -> "type" <+> x <+> "=" <+> show ty) <$> toList tyAliasEnv)

disjointTyBind :: Name -> S.Ty -> Name -> S.Ty -> S.Ty -> Typing Unit
disjointTyBind a1 t1 a2 t2 td = addTyBind freshName td $
  disjoint (S.tySubst a1 freshVar t1) (S.tySubst a2 freshVar t2)
  where freshName = a1 <> " or " <> a2
        freshVar = S.TyVar freshName

letIn :: Name -> C.Tm -> S.Ty -> LetTrans
letIn x e1 t1 ty = do
  t1' <- transform t1
  e2 /\ t2 <- ty
  t2' <- transform t2
  pure $ C.TmApp (C.TmAbs x e2 t1' t2' false) e1 false /\ t2

trait :: Name -> C.Tm -> S.Ty -> S.Ty -> Typing (C.Tm /\ S.Ty)
trait x e targ tret = do
  targ' <- transform targ
  tret' <- transform tret
  pure $ C.TmAbs x e targ' tret' false /\ S.TyTrait targ tret

ensureTyRec :: S.Ty -> Typing Unit
ensureTyRec (S.TyRec _ _) = pure unit
ensureTyRec t = throwTypeError $ "fold/unfold expected a recursive type, but got" <+> show t

collectLabels :: S.Ty -> Set Label
collectLabels (S.TyAnd t1 t2) = Set.union (collectLabels t1) (collectLabels t2)
collectLabels (S.TyRcd rts) = Set.fromFoldable $ (\(S.RcdTy l _ _) -> l) <$>
  filter (\(S.RcdTy _ _ opt) -> not opt) rts
collectLabels (S.TyNominal _ _ t) = collectLabels t
collectLabels _ = Set.empty

selectLabel :: S.Ty -> Label -> Boolean -> Maybe S.Ty
selectLabel (S.TyAnd t1 t2) l opt =
  case selectLabel t1 l opt, selectLabel t2 l opt of
    Just t1', Just t2' -> Just (S.TyAnd t1' t2')
    Just t1', Nothing  -> Just t1'
    Nothing,  Just t2' -> Just t2'
    Nothing,  Nothing  -> Nothing
selectLabel (S.TyRcd rts) l opt = (\(S.RcdTy _ t _) -> t) <$>
  find (\(S.RcdTy l' _ opt') -> l' == l && opt' == opt) rts
selectLabel (S.TyNominal _ _ t) l opt = selectLabel t l opt
selectLabel _ _ _ = Nothing

checkDef :: Def -> Checking Unit
checkDef (TyDef isRec a sorts params t) = do
  ctx <- gets fromState
  case runTyping (addRec $ addSorts $ addTyBinds $ transformTyDef t) ctx of
    Left err -> throwError err
    Right t' -> modify_ (\b -> b { tyAliases = insert a (rec (sig t')) b.tyAliases })
  where
    dualSorts :: List (Name /\ Name)
    dualSorts = sorts <#> \sort -> sort /\ ("#" <> sort)
    addSorts :: forall a. Typing a -> Typing a
    addSorts typing = foldr (uncurry addSort) typing dualSorts
    addTyBinds :: forall a. Typing a -> Typing a
    addTyBinds typing = foldr (flip addTyBind S.TyTop) typing params
    sig :: S.Ty -> S.Ty
    sig t' = foldr (uncurry S.TySig) (foldr S.TyAbs t' params) dualSorts
    addRec :: forall a. Typing a -> Typing a
    addRec = if isRec then addTyBind a S.TyTop else identity
    rec :: S.Ty -> S.Ty
    rec = if isRec then S.TyRec a else identity
checkDef (ItDef a rs) = do
  ctx <- gets fromState
  case runTyping (transformTyDef $ TyRcd rs) ctx of
    Left err -> throwError err
    Right t' -> modify_ (\b -> b { tyAliases = insert a (S.TyNominal a Nothing t') b.tyAliases })
checkDef (TmDef x Nil Nil Nothing e) = do
  ctx <- gets fromState
  case runTyping (infer e) ctx of
    Left err -> throwError err
    Right (e' /\ t) -> modify_ (\st ->
      st { tmBindings = st.tmBindings <> singleton (x /\ t /\ letIn x e' t) })
checkDef (TmDef x Nil Nil (Just t) e) = do
  ctx <- gets fromState
  case runTyping (inferRec x e t) ctx of
    Left err -> throwError err
    Right (e' /\ t' /\ t'') -> modify_ (\b -> b { tmBindings = b.tmBindings <>
        singleton (x /\ t' /\ letIn x (C.TmFix x e' t'') t') })
checkDef d = throwError $ TypeError ("expected a desugared def, but got" <+> show d) UnknownPos

checkProg :: Prog -> Checking (C.Tm /\ S.Ty)
checkProg (Prog defs e) = do
  traverse_ checkDef defs
  ctx <- gets fromState
  case runTyping (infer e) ctx of
    Left err -> throwError err
    Right p -> pure p