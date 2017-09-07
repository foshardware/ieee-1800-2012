{-# LANGUAGE TupleSections #-}

module Language.SystemVerilog.Parser.Writer
  ( module Data.Functor.Identity
  , module Text.Parsec
  , module Text.Parsec.Pos
  , module Language.SystemVerilog.Lexer
  , module Language.SystemVerilog.Syntax
  , (<?>), (<|>), (>>), optional
  , tokenPrim
  , Parser, Result
  , trace, runParser, runResult
  ) where

import qualified Control.Applicative as A
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer
import Data.Functor.Identity
import Data.Text (Text)
import qualified Text.Parsec as P
import Text.Parsec
  (ParsecT, ParseError, uncons, many, many1, choice, try, sepBy, sepBy1, sepEndBy, between)
import Text.Parsec.Pos

import Language.SystemVerilog.Lexer
import Language.SystemVerilog.Syntax

type Parser a = ParsecT [Lexer Token] () Result a

runParser :: Parser a -> String -> [Lexer Token] -> Result (Either ParseError a)
runParser p = P.runParserT p ()

type Result = Writer [String]

runResult :: Result a -> a
runResult = fst . runWriter

trace :: Parser a -> Text -> [String]
trace p = execWriter . runParser p mempty . lexer mempty

optional :: Parser a -> Parser (Maybe a)
optional = A.optional . P.try

(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = P.try p P.<|> q

infixl 3 <|>

(<?>) :: Parser a -> String -> Parser a
p <?> lbl = do
  lift $ tell [lbl]
  (P.<?>) p lbl
infix 0 <?>

tokenPrim
  :: (Lexer Token -> String)
  -> (SourcePos -> Lexer Token -> [Lexer Token] -> SourcePos)
  -> (Lexer Token -> Maybe a)
  -> Parser a
tokenPrim = P.tokenPrim


