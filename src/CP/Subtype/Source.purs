module Language.CP.Subtype.Source where

import Prelude

import Control.Alt ((<|>))
import Data.Array ((!!))
import Data.Foldable (any, find, foldl, foldr, intercalate)
import Data.List (List(..), all, length, singleton, zip, (:))
import Data.Maybe (Maybe(..), isNothing)
import Data.String.Utils (repeat)
import Data.Traversable (traverse)
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Language.CP.Context (Typing, lookupTyBind, throwTypeError)
import Language.CP.Syntax.Common (Label, Name)
import Language.CP.Syntax.Source (RcdTy(..), Ty(..), TyConstr(..), intercalate', tySubst)
import Language.CP.Util (foldl1, unsafeFromJust, zipWithIndex, (<+>))
import Partial.Unsafe (unsafeCrashWith)

data STree = SLeaf Ty Ty
           | SNode Ty Ty STree
           | SOr Ty Ty (List STree)

-- Require: expanded types
-- if success, return Nothing
subtype :: Ty -> Ty -> Maybe STree
subtype TyBot _ = Nothing
subtype _ t | isTopLike t = Nothing
subtype t1 t2 | t1 == t2  = Nothing
subtype t1 t2 | Just ts <- split t2 = SNode t1 t2 <$>
  foldl1 (<|>) ((t1 `subtype` _) <$> ts)
subtype t1@(TyArrow targ1 tret1) t2@(TyArrow targ2 tret2) = SNode t1 t2 <$>
  targ2 `subtype` targ1 <|> tret1 `subtype` tret2
subtype t1 t2 | Just ts <- split t1 = SOr t1 t2 <$>
  foldl f (Just Nil) ((_ `subtype` t2) <$> ts)
  where f (Just trees) (Just tree) = Just $ trees <> singleton tree
        f _ _ = Nothing
subtype _ (TyRcd (RcdTy _ _ true : Nil)) = Nothing
subtype t1@(TyRcd (RcdTy a ta false : Nil)) t2@(TyRcd (RcdTy b tb false : Nil))
  | a == b    = SNode t1 t2 <$> ta `subtype` tb
  | otherwise = Just $ SLeaf t1 t2
subtype t1@(TyForall a1 td1 t1') t2@(TyForall a2 td2 t2') = SNode t1 t2 <$>
  td2 `subtype` td1 <|> t1' `subtype` tySubst a2 (TyVar a1) t2'
subtype t1@(TyRec a1 t1') t2@(TyRec a2 t2') = SNode t1 t2 <$>
  tySubst a1 (tyRcd a1 t1' false) t1' `subtype` tySubst a2 (tyRcd a1 t2'' false) t2'
  where t2'' = tySubst a2 (TyVar a1) t2'
subtype t1@(TyArray t1') t2@(TyArray t2') = SNode t1 t2 <$> t1' `subtype` t2'
subtype t1@(TyTrait ti1 to1) t2@(TyTrait ti2 to2) = SNode t1 t2 <$>
  TyArrow ti1 to1 `subtype` TyArrow ti2 to2
subtype t1@(TyNominal _ _) t2@(TyNominal _ _) = SOr t1 t2 <$>
  foldl f (Just Nil) ((_ `subtype` t2) <$> directSupers t1)
  where f (Just trees) (Just tree) = Just $ trees <> singleton tree
        f _ _ = Nothing
subtype t1@(TyNominal _ _) t2 = SNode t1 t2 <$> structuralize t1 `subtype` t2
subtype t1 t2 = Just $ SLeaf t1 t2

directSupers :: Ty -> List Ty
directSupers (TyNominal (TyConstr _ ss _) as) = (\t -> foldr (uncurry tySubst) t as) <$> ss
directSupers _ = Nil

showSubtypeTrace :: Ty -> Ty -> String
showSubtypeTrace t1 t2 = case t1 `subtype` t2 of
  Just tree -> pp 0 "" tree
  Nothing -> "subtyping successful"
  where
    pp :: Int -> String -> STree -> String
    pp k prefix t = unsafeFromJust (repeat k " ") <> prefix <> case t of
      SLeaf tl tr -> show tl <+> "<:" <+> show tr <+> "✗"
      SNode tl tr tree -> show tl <+> "<:" <+> show tr <> "\n" <> pp k "⇐ " tree
      SOr tl tr Nil -> show tl <+> "<:" <+> show tr <+> "✗"
      SOr tl tr (tree : Nil) -> show tl <+> "<:" <+> show tr <> "\n" <> pp k "⇐ " tree
      SOr tl tr trees -> show tl <+> "<:" <+> show tr <> "\n" <> intercalate' "\n"
        ((\(tree /\ i) -> pp (k + 2) ("⇐" <> superscript i <> " ") tree) <$> zipWithIndex trees)
        where 
          superscript i = case ["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"] !! i of
            Just s -> s
            Nothing -> show i

isSubType :: Ty -> Ty -> Boolean
isSubType t1 t2 = isNothing $ t1 `subtype` t2

infix 4 isSubType as <:

tyRcd :: Label -> Ty -> Boolean -> Ty
tyRcd l t b = TyRcd $ RcdTy l t b : Nil

isSupertype :: Ty -> Ty -> Boolean
isSupertype = flip isSubType

infix 4 isSupertype as :>

isTopLike :: Ty -> Boolean
isTopLike TyTop = true
isTopLike (TyArrow _ t) = isTopLike t
isTopLike (TyAnd t1 t2) = isTopLike t1 && isTopLike t2
isTopLike (TyRcd rts) = all (\(RcdTy _ t _) -> isTopLike t) rts
isTopLike (TyForall _ _ t) = isTopLike t
isTopLike (TyRec _ t) = isTopLike t
isTopLike _ = false

split :: Ty -> Maybe (List Ty)
split (TyAnd t1 t2) = Just $ t1 : t2 : Nil
split (TyArrow targ tret) = do
  ts <- split tret
  Just $ TyArrow targ <$> ts
split (TyRcd (RcdTy l t b : Nil)) = do
  ts <- split t
  Just $ (\t' -> tyRcd l t' b) <$> ts
split (TyRcd rts) | length rts > 1 = Just $ (\(RcdTy l t b) -> tyRcd l t b) <$> rts
split (TyForall x s t) = do
  ts <- split t
  Just $ TyForall x s <$> ts
split (TyTrait ti to) = do
  ts <- split to
  Just $ TyTrait ti <$> ts
split _ = Nothing

aeq :: Ty -> Ty -> Boolean
aeq (TyArrow t1 t2) (TyArrow t3 t4) = t1 === t3 && t2 === t4
aeq (TyAnd t1 t2) (TyAnd t3 t4) = t1 === t3 && t2 === t4
aeq (TyRcd rts1) (TyRcd rts2) = length rts1 == length rts2 && all (uncurry eq) (zip rts1 rts2)
  where
    eq :: RcdTy -> RcdTy -> Boolean
    eq (RcdTy l1 t1 opt1) (RcdTy l2 t2 opt2) = l1 == l2 && t1 === t2 && opt1 == opt2
aeq (TyForall a1 td1 t1) (TyForall a2 td2 t2) = td1 === td2 && t1 === tySubst a2 (TyVar a1) t2
aeq (TyRec a1 t1) (TyRec a2 t2) = t1 === tySubst a2 (TyVar a1) t2
aeq (TyArray t1) (TyArray t2) = t1 === t2
aeq t1 t2 | t1 == t2  = true
          | otherwise = false

infix 4 aeq as ===

tyDiff :: Ty -> Ty -> Typing Ty
tyDiff m s = simplify <$> diff m s
  where
    -- this algorithm does not depend on separate definitions of subtyping or disjointness
    diff :: Ty -> Ty -> Typing Ty
    diff t1 t2 | isTopLike t1 || isTopLike t2 = pure t1
    diff t1 t2 | t1 == t2 = pure TyTop
    diff t1 t2 | Just ts <- split t1 = tyMerge t1 <$> traverse (_ `diff` t2) ts
    diff t (TyAnd t1 t2) = (diff t t1 >>= \t' -> diff t' t2) <|>
                           (diff t t2 >>= \t' -> diff t' t1)
    diff TyBot TyBot = pure TyTop
    diff t TyBot = diff t t        -- should not precede left-split
    diff TyBot _ = throwDiffError  -- should not precede right-and
    diff t@(TyArrow targ1 tret1) (TyArrow targ2 tret2) = do
      dret <- diff tret1 tret2
      if dret == tret1 then pure t  -- disjoint (m * s)
      else do darg <- diff targ2 targ1
              if isTopLike darg  -- supertype (m :> s)
              then pure $ TyArrow targ1 dret else throwDiffError
    diff (TyRcd rts1) (TyRcd rts2) = TyRcd <$> traverse exclude rts1
      where 
        exclude r@(RcdTy l t opt) = case find (\(RcdTy l' _ _) -> l' == l) rts2 of
          Just (RcdTy _ t' _) -> RcdTy l <$> diff t t' <@> opt
          Nothing -> pure r
    diff t@(TyForall a1 td1 t1) (TyForall a2 td2 t2) = do
      d <- diff t1 t2'
      if d == t1 then pure t  -- disjoint (m * s)
      else do dd <- diff td2 td1
              if isTopLike dd  -- supertype (m :> s)
              then pure $ TyForall a1 td1 d else throwDiffError
      where t2' = tySubst a2 (TyVar a1) t2
    diff (TyVar a1) (TyVar a2) | a1 == a2 = pure TyTop
    diff (TyVar a) t = disjointVar a t >>=
      if _ then pure $ TyVar a else throwDiffError
    diff t (TyVar a) = disjointVar a t >>=
      if _ then pure t else throwDiffError
    diff (TyArray t1) (TyArray t2) = TyArray <$> diff t1 t2
    -- TODO: recursive type difference
    diff (TyRec _ _) _ = throwDiffError
    diff _ (TyRec _ _) = throwDiffError
    diff t1 _ = pure t1
    disjointVar :: Name -> Ty -> Typing Boolean
    disjointVar a t = lookupTyBind a >>= case _ of
      Just td -> isTopLike <$> diff t td
      _ -> pure false
    throwDiffError :: Typing Ty
    throwDiffError = throwTypeError $ "cannot subtract " <> show s <> " from " <> show m

tyMerge :: Ty -> List Ty -> Ty
tyMerge (TyAnd _ _) ts = foldl1 TyAnd ts
tyMerge t@(TyArrow targ tret) ts = TyArrow targ (tyMerge tret (f <$> ts))
  where f (TyArrow t1 t2) | t1 == targ = t2
        f _ = tyMergeCrash t ts
tyMerge t@(TyRcd rts) ts = TyRcd (f <$> ts)
  where f (TyRcd (RcdTy l' t' b' : Nil))
          | any (\(RcdTy l _ b) -> l' == l && b' == b) rts = RcdTy l' t' b'
        f _ = tyMergeCrash t ts
tyMerge t@(TyForall x s t1) ts = TyForall x s (tyMerge t1 (f <$> ts))
  where f (TyForall y s' t') | y == x && s' == s = t'
        f _ = tyMergeCrash t ts
tyMerge t ts = tyMergeCrash t ts

tyMergeCrash :: forall a. Ty -> List Ty -> a
tyMergeCrash t ts = unsafeCrashWith $ "CP.TypeDiff.tyMerge: " <>
    "cannot merge " <> intercalate ", " (map show ts) <> " according to " <> show t

simplify :: Ty -> Ty
simplify t | isTopLike t = TyTop
simplify t@(TyAnd t1 t2) = case isTopLike t1, isTopLike t2 of
  true,  true  -> TyTop
  true,  false -> simplify t2
  false, true  -> simplify t1
  false, false -> t
simplify (TyArrow targ tret) = TyArrow targ (simplify tret)
simplify (TyRcd rts) = TyRcd $ (\(RcdTy l t b) -> RcdTy l (simplify t) b) <$> rts
simplify (TyForall x s t) = TyForall x s (simplify t)
simplify (TyRec a t) = TyRec a (simplify t)
simplify (TyArray t) = TyArray (simplify t)
simplify t = t

structuralize :: Ty -> Ty
structuralize (TyArrow t1 t2) = TyArrow (structuralize t1) (structuralize t2)
structuralize (TyAnd t1 t2) = TyAnd (structuralize t1) (structuralize t2)
structuralize (TyRcd rts) = TyRcd $ (\(RcdTy l t b) -> RcdTy l (structuralize t) b) <$> rts
structuralize (TyForall a td t) = TyForall a (structuralize td) (structuralize t)
structuralize (TyRec x t) = TyRec x (structuralize t)
structuralize (TyApp t1 t2) = TyApp (structuralize t1) (structuralize t2)
structuralize (TyAbs x k t) = TyAbs x k (structuralize t)
structuralize (TyTrait t1 t2) = TyTrait (structuralize t1) (structuralize t2)
structuralize (TySort t1 t2) = TySort (structuralize t1) (structuralize <$> t2)
structuralize (TySig x y t) = TySig x y (structuralize t)
structuralize (TyArray t) = TyArray (structuralize t)
structuralize (TyDiff t1 t2) = TyDiff (structuralize t1) (structuralize t2)
structuralize t@(TyNominal (TyConstr _ _ rcd) as) = foldl TyAnd (foldr (uncurry tySubst) rcd as) $
  structuralize <$> directSupers t
structuralize t = t