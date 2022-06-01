module Language.CP where

import Prelude

import Control.Monad.State (gets)
import Data.Array ((!!))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import Language.CP.Context (Checking, Mode(..), Pos(..), TypeError(..), Typing, emptyCtx, fromState, letTrans, runTyping, throwCheckError, throwTypeError)
import Language.CP.Desugar (desugar, desugarProg)
import Language.CP.Parser (expr, program, subtypeJudgment, ty, whiteSpace)
import Language.CP.Semantics.HOAS as HOAS
import Language.CP.Semantics.NaturalClosure as Closure
import Language.CP.Semantics.NaturalSubst as BigStep
import Language.CP.Semantics.StepTrace as StepTrace
import Language.CP.Semantics.Subst as SmallStep
import Language.CP.Subtype.Source (getSubtypeTrace)
import Language.CP.Syntax.Source (Prog(..), Tm, showDoc)
import Language.CP.Transform (expand, transform')
import Language.CP.Typing (checkProg, infer)
import Parsing (ParseError(..), runParser, Position(..))
import Parsing.String (eof)

inferType :: String -> Typing String
inferType code = case runParser code (whiteSpace *> expr <* eof) of
  Left err -> throwTypeError $ showParseError err code
  Right e -> do
    _ /\ t <- infer $ desugar e
    pure $ show t

transType :: String -> Typing String
transType code = case runParser code (whiteSpace *> ty <* eof) of
  Left err -> throwTypeError $ showParseError err code
  Right t -> do
    t2 /\ t1 <- transform' t
    pure $ show t1 <> "\n(" <> show t2 <> ")"

judgeSubtype :: String -> Typing String
judgeSubtype judgment = case runParser judgment (whiteSpace *> subtypeJudgment <* eof) of
  Left err -> throwTypeError $ showParseError err judgment
  Right (t1 /\ t2) -> do
    t1' <- expand t1
    t2' <- expand t2
    getSubtypeTrace t1' t2'

importDefs :: String -> Checking Unit
importDefs code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throwCheckError $ showParseError err code
  Right prog -> do
    let prog' = desugarProg prog
    _ <- checkProg prog'
    pure unit

interpret :: String -> Checking String
interpret code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throwCheckError $ showParseError err code
  Right prog -> do
    let prog' = desugarProg prog
    let e' = case prog' of Prog _ e -> e
    e /\ t <- checkProg prog'
    f <- gets letTrans
    ctx <- gets fromState
    case runTyping (f $ pure $ e /\ t) ctx of
      Left err -> throwCheckError $ showTypeError err
      Right (e'' /\ _) -> do
        mode <- gets (_.mode)
        pure $ case mode of
          SmallStep -> show (SmallStep.eval e'')
          StepTrace -> let _ /\ s = StepTrace.eval e'' in
            show e <> "\n⇣ Desugar\n" <> show e' <> "\n↯ Elaborate\n" <> s ""
          BigStep -> show (BigStep.eval e'')
          HOAS -> show (HOAS.eval e'')
          Closure -> show (Closure.eval e'')

showPosition :: Position -> String
showPosition (Position { line: line, column: column }) =
  show line <> ":" <> show column

showParseError :: ParseError -> String -> String
showParseError (ParseError _ pos@(Position { line: l, column: c })) source =
  showPosition pos <> ": parse error:\n" <>
  case seek l of Just line -> line <> "\n" <> rep (c-1) " " <> "^"
                 Nothing -> ""
  where
    seek :: Int -> Maybe String
    seek line = (split (Pattern "\n") source) !! (line - 1)
    rep :: Int -> String -> String
    rep n s | n <= 0 = ""
            | otherwise = s <> rep (n-1) s

showTypeError :: TypeError -> String
showTypeError (TypeError msg UnknownPos) = msg
showTypeError (TypeError msg (Pos pos expr inDoc)) =
  showPosition pos <> ": " <> msg <> "\nin the expression: " <>
  (if inDoc then showDoc else show) expr

-- Big-step evaluation used after ANTLR parsing
eval :: Tm -> Effect String
eval e = case runTyping (infer $ desugar e) emptyCtx of
  Left err -> throw $ showTypeError err
  Right (e' /\ _) -> pure $ show (BigStep.eval e')
