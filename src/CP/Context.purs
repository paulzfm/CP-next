module Language.CP.Context where

import Prelude

import Control.Monad.Except (Except, runExcept, throwError)
import Control.Monad.Reader (ReaderT, asks, local, runReaderT)
import Control.Monad.State (StateT)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.List (List(..), foldr)
import Data.Map (Map, empty, fromFoldable, insert, lookup, toUnfoldable)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source (intercalate')
import Language.CP.Syntax.Source as S
import Language.CP.Util ((<+>))
import Parsing (Position)

type Typing = ReaderT Ctx (Except TypeError)

type Ctx = { tmBindEnv    :: Map Name S.Ty -- typing
           , tyBindEnv    :: Map Name S.Ty -- disjointness
           , tyAliasEnv   :: Map Name S.Ty -- synonym
           , sortEnv      :: Map Name Name -- distinguishing
           , tyConstrEnv  :: Map Name (List S.Ty /\ S.Ty) -- nominal type constr info
           , pos :: Pos
           }

data Pos = UnknownPos
         | Pos Position S.Tm Boolean

emptyCtx :: Ctx
emptyCtx =  { tmBindEnv : empty
            , tyBindEnv : empty
            , tyAliasEnv : empty
            , sortEnv : empty
            , tyConstrEnv : empty
            , pos : UnknownPos
            }

runTyping :: forall a. Typing a -> Ctx -> Either TypeError a
runTyping m ctx = runExcept $ runReaderT m ctx

lookupTmBind :: Name -> Typing S.Ty
lookupTmBind name = do
  env <- asks (_.tmBindEnv)
  case lookup name env of
    Just t -> pure t
    Nothing -> throwTypeError $ "term variable" <+> show name <+> "is undefined"

lookupTyBind :: Name -> Typing (Maybe S.Ty)
lookupTyBind name = lookup name <$> asks (_.tyBindEnv)

lookupTyAlias :: Name -> Typing (Maybe S.Ty)
lookupTyAlias name = lookup name <$> asks (_.tyAliasEnv)

lookupSort :: Name -> Typing (Maybe Name)
lookupSort name = lookup name <$> asks (_.sortEnv)

lookupTyConstr :: Name -> Typing (List S.Ty /\ S.Ty)
lookupTyConstr name = do
  env <- asks (_.tyConstrEnv)
  case lookup name env of
    Just t -> pure t
    Nothing -> throwTypeError $ "type constructor" <+> show name <+> "is undefined"

addToEnv :: forall a b. ((Map Name b -> Map Name b) -> Ctx -> Ctx) ->
                        Name -> b -> Typing a -> Typing a
addToEnv map name ty = if name == "_" then identity
                       else local (map \env -> insert name ty env)

addTmBind :: forall a. Name -> S.Ty -> Typing a -> Typing a
addTmBind = addToEnv \f r -> r { tmBindEnv = f r.tmBindEnv }

addTyBind :: forall a. Name -> S.Ty -> Typing a -> Typing a
addTyBind = addToEnv \f r -> r { tyBindEnv = f r.tyBindEnv }

addTyAlias :: forall a. Name -> S.Ty -> Typing a -> Typing a
addTyAlias = addToEnv \f r -> r { tyAliasEnv = f r.tyAliasEnv }

addSort :: forall a. Name -> Name -> Typing a -> Typing a
addSort = addToEnv \f r -> r { sortEnv = f r.sortEnv }

addTyConstr :: forall a. Name -> (List S.Ty /\ S.Ty) -> Typing a -> Typing a
addTyConstr = addToEnv \f r -> r { tyConstrEnv = f r.tyConstrEnv }

localPos :: forall a. (Pos -> Pos) -> Typing a -> Typing a
localPos f = local \r -> r { pos = f r.pos }

askPos :: Typing Pos
askPos = asks (_.pos)

ppTypeVars :: Ctx -> String
ppTypeVars ctx = intercalate' "\n" (ppTyBinding <$> toList ctx.tyBindEnv) <>
  intercalate' "\n" (ppTyAlias <$> toList ctx.tyAliasEnv) <>
  intercalate' "\n" (ppSort <$> toList ctx.sortEnv)
  where
    ppTyBinding (x /\ t) = x <+> "*" <+> show t
    ppTyAlias (x /\ t) = "type" <+> x <+> "=" <+> show t
    ppSort (i /\ o) = i <+> "=>" <+> o

data TypeError = TypeError String Pos

-- TODO: combine two type errors
instance Semigroup TypeError where
  append = const

throwTypeError :: forall a. String -> Typing a
throwTypeError msg = TypeError msg <$> askPos >>= throwError

type Checking = StateT CompilerState (Except TypeError)

data Mode = SmallStep | StepTrace | BigStep | HOAS | Closure

derive instance Generic Mode _
instance Show Mode where show = genericShow

type LetTrans = Typing (C.Tm /\ S.Ty) -> Typing (C.Tm /\ S.Ty)

type CompilerState =  { mode        :: Mode
                      , timing      :: Boolean
                      , tmBindings  :: List (Name /\ S.Ty /\ LetTrans)
                      , tyAliases   :: Map Name S.Ty
                      , tyConstrs   :: Map Name (List S.Ty /\ S.Ty)
                      }

initState :: CompilerState
initState = { mode       : BigStep
            , timing     : false
            , tmBindings : Nil
            , tyAliases  : empty
            , tyConstrs  : empty
            }

toList :: forall k v. Map k v -> List (k /\ v)
toList = toUnfoldable

ppState :: CompilerState -> String
ppState st = intercalate' "\n" (map ppTmBinding st.tmBindings) <>
  intercalate' "\n" (map ppTyAlias $ toList st.tyAliases)
  where
    ppTmBinding (x /\ t /\ _) = "term" <+> x <+> ":" <+> show t
    ppTyAlias (x /\ t) = "type" <+> x <+> "=" <+> show t

clearEnv :: CompilerState -> CompilerState
clearEnv st = st { tmBindings = Nil, tyAliases = empty, tyConstrs = empty }

fromState :: CompilerState -> Ctx
fromState st =  { tmBindEnv : fromFoldable $ map (\(x /\ t /\ _) -> x /\ t) st.tmBindings
                , tyAliasEnv : st.tyAliases
                , tyConstrEnv : st.tyConstrs
                , tyBindEnv : empty
                , sortEnv : empty
                , pos : UnknownPos
                }

letTrans :: CompilerState -> LetTrans
letTrans st ty = foldr (\f -> \acc -> f acc) ty $ (\(_ /\ _ /\ f) -> f) <$> st.tmBindings

throwCheckError :: forall a. String -> Checking a
throwCheckError msg = throwError $ TypeError msg UnknownPos