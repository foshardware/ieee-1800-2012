
module Language.SystemVerilog.Namespace
  ( module Text.Parsec
  , module Text.Parsec.Combinator
  , module Text.Parsec.Pos
  , module Language.SystemVerilog.Lexer
  , module Language.SystemVerilog.Syntax
  , (<|>), optional, many
  , Parser
  ) where

import qualified Control.Applicative as A
import Text.Parsec (Parsec, ParseError, token, parse, try, (<?>))
import Text.Parsec.Combinator (sepBy, sepBy1, sepEndBy, between, many1, choice)
import Text.Parsec.Pos

import Language.SystemVerilog.Lexer
import Language.SystemVerilog.Syntax

type Parser = Parsec [Lexer Token] ()

(<|>) :: Parser a -> Parser a -> Parser a
x <|> y = try x A.<|> y
infixl 3 <|>

optional :: Parser a -> Parser (Maybe a)
optional = A.optional . try

many :: Parser a -> Parser [a]
many = A.many

