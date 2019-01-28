
module Language.SystemVerilog.Alternative.Identity
  ( module Data.Functor.Identity
  , module Text.Parsec
  , module Text.Parsec.Combinator
  , module Text.Parsec.Pos
  , module Language.SystemVerilog.Lexer
  , module Language.SystemVerilog.Syntax
  , (<|>), optional, many
  , Parser, Result
  , runResult
  ) where

import qualified Control.Applicative as A
import Data.Functor.Identity
import Text.Parsec (ParsecT, ParseError, tokenPrim, runParserT, try, uncons, (<?>))
import Text.Parsec.Combinator (sepBy, sepBy1, sepEndBy, between, many1, choice)
import Text.Parsec.Pos

import Language.SystemVerilog.Lexer
import Language.SystemVerilog.Syntax

type Parser = ParsecT [Lexer Token] () Result

type Result = Identity

runResult :: Result a -> a
runResult = runIdentity

(<|>) :: Parser a -> Parser a -> Parser a
x <|> y = try x A.<|> y
infixl 3 <|>

optional :: Parser a -> Parser (Maybe a)
optional = A.optional . try

many :: Parser a -> Parser [a]
many = A.many

