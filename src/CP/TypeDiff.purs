module Language.CP.TypeDiff where

import Prelude

import Control.Alt ((<|>))
import Data.List (List(..), zip, (:))
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (uncurry)
import Language.CP.Context (Typing, lookupTyBind, throwTypeError)
import Language.CP.Subtype.Source (isTopLike, split)
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Source (RcdTy(..), Ty(..), intercalate', tySubst)
import Language.CP.Util (foldl1)
import Partial.Unsafe (unsafeCrashWith)

tyDiff :: Ty -> Ty -> Typing Ty
tyDiff m s = simplify <$> diff m s
  where
    -- this algorithm does not depend on separate definitions of subtyping or disjointness
    diff :: Ty -> Ty -> Typing Ty
    diff t1 t2 | isTopLike t1 || isTopLike t2 = pure t1
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
    diff (TyRcd rts1) (TyRcd rts2) = TyRcd <$> traverse (uncurry f) (zip rts1 rts2)
      where f t@(RcdTy l1 t1 b) (RcdTy l2 t2 _) | l1 == l2  = RcdTy l1 <$> diff t1 t2 <@> b
                                                | otherwise = pure t
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
    diff t1 t2 | t1 == t2  = pure TyTop
               | otherwise = pure t1
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
tyMerge t@(TyRcd (RcdTy l tl b : Nil)) ts = TyRcd (RcdTy l (tyMerge tl (f <$> ts)) b : Nil)
  where f (TyRcd (RcdTy l' t' b' : Nil)) | l' == l && b' == b = t'
        f _ = tyMergeCrash t ts
tyMerge t@(TyForall x s t1) ts = TyForall x s (tyMerge t1 (f <$> ts))
  where f (TyForall y s' t') | y == x && s' == s = t'
        f _ = tyMergeCrash t ts
tyMerge t ts = tyMergeCrash t ts

tyMergeCrash :: Ty -> List Ty -> Ty
tyMergeCrash t ts = unsafeCrashWith $ "CP.TypeDiff.tyMerge: " <>
    "cannot merge " <> intercalate' ", " (map show ts) <> " according to " <> show t

simplify :: Ty -> Ty
simplify t | isTopLike t = TyTop
simplify t@(TyAnd t1 t2) = case isTopLike t1, isTopLike t2 of
  true,  true  -> TyTop
  true,  false -> t2
  false, true  -> t1
  false, false -> t
simplify (TyArrow targ tret) = TyArrow targ (simplify tret)
simplify (TyRcd rts) = TyRcd $ (\(RcdTy l t b) -> RcdTy l (simplify t) b) <$> rts
simplify (TyForall x s t) = TyForall x s (simplify t)
simplify (TyRec a t) = TyRec a (simplify t)
simplify (TyArray t) = TyArray (simplify t)
simplify t = t
