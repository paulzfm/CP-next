module Language.CP.Subtype.Source where

import Prelude

import Data.List (List(..), all, any, (:), length, zip)
import Data.Maybe (Maybe(..))
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Language.CP.Syntax.Common (Label)
import Language.CP.Syntax.Source (RcdTy(..), Ty(..), tySubst)

-- Require: expanded types
subtype :: Ty -> Ty -> Boolean
subtype TyBot _ = true
subtype _ t | isTopLike t = true
subtype t1 t2 | Just ts <- split t2 = all (t1 <: _) ts
subtype (TyArrow targ1 tret1) (TyArrow targ2 tret2) = targ2 <: targ1 && tret1 <: tret2
subtype t1 t2 | Just ts <- split t1 = any (_ <: t2) ts
subtype _ (TyRcd (RcdTy _ _ true : Nil)) = true
subtype (TyRcd (RcdTy l1 t1 false : Nil)) (TyRcd (RcdTy l2 t2 false : Nil)) = l1 == l2 && t1 <: t2
subtype (TyForall ((a1 /\ Just td1) : Nil) t1) (TyForall ((a2 /\ Just td2) : Nil) t2) =
  td2 <: td1 && t1 <: tySubst a2 (TyVar a1) t2
subtype (TyRec a1 t1) (TyRec a2 t2) =
  tySubst a1 (tyRcd a1 t1 false) t1 <: tySubst a2 (tyRcd a1 t2' false) t2
  where t2' = tySubst a2 (TyVar a1) t2
subtype (TyArray t1) (TyArray t2) = t1 <: t2
subtype t (TyNominal a _ _) = canCast t
  where
    canCast :: Ty -> Boolean
    canCast (TyNominal x _ _) | x == a = true
    canCast (TyNominal _ (Just s) _) = canCast s
    canCast _ = false
subtype (TyNominal _ _ t1) t2 = t1 <: t2
subtype t1 t2 | t1 == t2  = true
              | otherwise = false

infix 4 subtype as <:

tyRcd :: Label -> Ty -> Boolean -> Ty
tyRcd l t b = TyRcd $ RcdTy l t b : Nil

supertype :: Ty -> Ty -> Boolean
supertype = flip subtype

infix 4 supertype as :>

isTopLike :: Ty -> Boolean
isTopLike TyTop = true
isTopLike (TyArrow _ t) = isTopLike t
isTopLike (TyAnd t1 t2) = isTopLike t1 && isTopLike t2
isTopLike (TyRcd rts) = all (\(RcdTy _ t _) -> isTopLike t) rts
isTopLike (TyForall _ t) = isTopLike t
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
split (TyForall xs t) = do
  ts <- split t
  Just $ TyForall xs <$> ts
split _ = Nothing

aeq :: Ty -> Ty -> Boolean
aeq (TyArrow t1 t2) (TyArrow t3 t4) = t1 === t3 && t2 === t4
aeq (TyAnd t1 t2) (TyAnd t3 t4) = t1 === t3 && t2 === t4
aeq (TyRcd rts1) (TyRcd rts2) = length rts1 == length rts2 && all (uncurry eq) (zip rts1 rts2)
  where
    eq :: RcdTy -> RcdTy -> Boolean
    eq (RcdTy l1 t1 opt1) (RcdTy l2 t2 opt2) = l1 == l2 && t1 === t2 && opt1 == opt2
aeq (TyForall ((a1 /\ Just td1) : Nil) t1) (TyForall ((a2 /\ Just td2) : Nil) t2) =
  td1 === td2 && t1 === tySubst a2 (TyVar a1) t2
aeq (TyRec a1 t1) (TyRec a2 t2) = t1 === tySubst a2 (TyVar a1) t2
aeq (TyArray t1) (TyArray t2) = t1 === t2
aeq t1 t2 | t1 == t2  = true
          | otherwise = false

infix 4 aeq as ===
