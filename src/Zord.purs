module Zord where

import Prelude

import Data.Array ((!!))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.String.CodeUnits (charAt)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Text.Parsing.Parser (ParseError(..), runParser)
import Text.Parsing.Parser.Pos (Position(..))
import Text.Parsing.Parser.String (eof, skipSpaces)
import Zord.Context (Pos(..), TypeError(..), runTyping)
import Zord.Desugar (desugar)
import Zord.Parser (expr)
import Zord.Semantics (eval, runEval)
import Zord.Typing (synthesize)

data Mode = Simple | Verbose

interpret :: Mode -> String -> Effect String
interpret mode input = case runParser input (skipSpaces *> expr <* eof) of
  Left err -> throw $ showParseError err input
  Right e -> case runTyping (synthesize (desugar e)) of
    Left err -> throw $ showTypeError err
    Right (Tuple e' t) -> let Tuple e'' s = runEval (eval e') in case mode of
      Simple  -> pure $ show e''
      Verbose -> pure s

seek :: String -> Int -> Int -> Maybe Char
seek str line column = (split (Pattern "\n") str) !! line' >>= charAt column'
  where line' = line - 1
        column' = column - 1

showPosition :: Position -> String
showPosition (Position { line: line, column: column }) =
  show line <> ":" <> show column

showParseError :: ParseError -> String -> String
showParseError (ParseError msg pos) source =
  showPosition pos <> ": parse error" <> (
    case sought pos of Just char -> " on input " <> show char
                       Nothing -> ""
  )
  where
    sought :: Position -> Maybe Char
    sought (Position { line: line, column: column }) = seek source line column

showTypeError :: TypeError -> String
showTypeError (TypeError msg UnknownPos) = msg
showTypeError (TypeError msg (Pos pos expr)) =
  showPosition pos <> ": " <> msg <> "\nIn the expression: " <> show expr
