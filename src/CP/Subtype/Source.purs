module Language.CP.Subtype.Source where

import Prelude

import Control.Alt ((<|>))
import Data.Array ((!!))
import Data.Foldable (foldl)
import Data.List (List(..), all, length, singleton, zip, (:))
import Data.Maybe (Maybe(..), isNothing)
import Data.String.Utils (repeat)
import Data.Tuple (uncurry)
import Data.Tuple.Nested ((/\))
import Language.CP.Syntax.Common (Label)
import Language.CP.Syntax.Source (RcdTy(..), Ty(..), intercalate', tySubst)
import Language.CP.Util (foldl1, unsafeFromJust, zipWithIndex, (<+>))

data STree = SLeaf Ty Ty
           | SNode Ty Ty STree
           | SOr Ty Ty (List STree)

-- Require: expanded types
-- if success, return Nothing
subtype :: Ty -> Ty -> Maybe STree
subtype TyBot _ = Nothing
subtype _ t | isTopLike t = Nothing
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
subtype t1 t2@(TyNominal a _ _) = SNode t1 t2 <$> canCast t1
  where canCast (TyNominal x _ _) | x == a = Nothing
        canCast (TyNominal _ (Just s) _) = canCast s
        canCast t = Just $ SLeaf t t2
subtype t1@(TyNominal _ _ t1') t2 = SNode t1 t2 <$> t1' `subtype` t2
subtype t1 t2 | t1 == t2  = Nothing
              | otherwise = Just $ SLeaf t1 t2

showSubtypeTrace :: Ty -> Ty -> String
showSubtypeTrace t1 t2 = case t1 `subtype` t2 of
  Just tree -> pp 0 "" tree
  Nothing -> "subtyping successful"
  where
    pp :: Int -> String -> STree -> String
    pp k prefix t = unsafeFromJust (repeat k " ") <> prefix <> case t of
      SLeaf tl tr -> show tl <+> "<:" <+> show tr <+> "✗"
      SNode tl tr tree -> show tl <+> "<:" <+> show tr <> "\n" <> pp k "⇐ " tree
      SOr tl tr (tree : Nil) -> show tl <+> "<:" <+> show tr <> "\n" <> pp k "⇐ " tree
      SOr tl tr trees -> show tl <+> "<:" <+> show tr <> "\n" <> intercalate' "\n"
        ((\(tree /\ i) -> pp (k + 2) ("⇐" <> superscript i <> " ") tree) <$> zipWithIndex trees)
        where 
          superscript i = case ["₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"] !! i of
            Just s -> s
            Nothing -> show i

isSubType :: Ty -> Ty -> Boolean
isSubType t1 t2 = isNothing $ t1 `subtype` t2
-- subtype TyBot _ = true
-- subtype _ t | isTopLike t = true
-- subtype t1 t2 | Just ts <- split t2 = all (t1 <: _) ts
-- subtype (TyArrow targ1 tret1) (TyArrow targ2 tret2) = targ2 <: targ1 && tret1 <: tret2
-- subtype t1 t2 | Just ts <- split t1 = any (_ <: t2) ts
-- subtype _ (TyRcd (RcdTy _ _ true : Nil)) = true
-- subtype (TyRcd (RcdTy l1 t1 false : Nil)) (TyRcd (RcdTy l2 t2 false : Nil)) = l1 == l2 && t1 <: t2
-- subtype (TyForall a1 td1 t1) (TyForall a2 td2 t2) = td2 <: td1 && t1 <: tySubst a2 (TyVar a1) t2
-- subtype (TyRec a1 t1) (TyRec a2 t2) =
--   tySubst a1 (tyRcd a1 t1 false) t1 <: tySubst a2 (tyRcd a1 t2' false) t2
--   where t2' = tySubst a2 (TyVar a1) t2
-- subtype (TyArray t1) (TyArray t2) = t1 <: t2
-- subtype (TyTrait (Just ti1) to1) (TyTrait (Just ti2) to2) = TyArrow ti1 to1 <: TyArrow ti2 to2
-- subtype t (TyNominal a _ _) = canCast t
--   where
--     canCast :: Ty -> Boolean
--     canCast (TyNominal x _ _) | x == a = true
--     canCast (TyNominal _ (Just s) _) = canCast s
--     canCast _ = false
-- subtype (TyNominal _ _ t1) t2 = t1 <: t2
-- subtype t1 t2 | t1 == t2  = true
--               | otherwise = false

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
