{-# LANGUAGE TupleSections #-}

module Language.SystemVerilog.Parser.Grammar
  ( module Data.Functor.Identity
  , module Text.Parsec
  , module Text.Parsec.Pos
  , module Language.SystemVerilog.Lexer
  , module Language.SystemVerilog.Syntax
  , (<?>), (>>), optional, many, many1, choice, try
  , between, sepBy, sepBy1, sepEndBy
  , tokenPrim
  , Parser(..), Result
  , runParser, runResult
  , grammar, rules
  , pretty, prettyRules
  , Monoidal(..)
  ) where

import qualified Control.Applicative as A
import Control.Applicative (Alternative, (<|>))
import Control.Monad
import Control.Monad.Trans.State
import Data.Functor.Identity
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Text (Text)
import Text.Parsec (ParsecT, ParseError, uncons)
import Text.Parsec.Pos
import Prelude hiding ((>>))

import Language.SystemVerilog.Lexer
import Language.SystemVerilog.Syntax

-- | A grammar generator
--
newtype Parser a = Parser { unParser :: State (Grammar, (Rules, [Key])) a }

runParser :: Parser a -> String -> [Lexer Token] -> Result (Either ParseError a)
runParser = fail "Grammar Parser"

type Result = Identity

runResult :: Result a -> a
runResult = runIdentity

type Key = String

type Rules = Map Key Grammar

data Grammar
  = SepBy1 Grammar Grammar | SepBy Grammar Grammar | SepEndBy Grammar Grammar
  | Many1 Grammar | Many Grammar
  | Between Grammar Grammar Grammar
  | Optional Grammar
  | Append [Grammar]
  | Choice [Grammar]
  | Label String
  | Empty
  deriving (Eq, Show)

instance Monoid Grammar where
  mempty = Empty
  mappend Empty g = g
  mappend g Empty = g
  mappend (Append g) (Append h) = Append (mappend g h)
  mappend g (Append h) = Append (mappend [g] h)
  mappend (Append g) h = Append (mappend g [h])
  mappend g h = Append [g, h]

cappend :: Grammar -> Grammar -> Grammar
cappend Empty g = g
cappend g Empty = g
cappend (Choice xs) (Choice ys) = Choice (mappend xs ys)
cappend (Choice xs) g = Choice (mappend xs [g])
cappend g (Choice xs) = Choice (mappend [g] xs)
cappend g h = Choice [g, h]


instance Functor Parser where
  fmap f (Parser p) = Parser (fmap f p)

instance Applicative Parser where
  pure = Parser . pure
  Parser mf <*> Parser mx = Parser $ do
    ~(_, r) <- get
    put (mempty, r)
    f <- mf
    ~(h, s) <- get
    put (mempty, s)
    x <- mx
    ~(i, t) <- get
    f x <$ put (mappend h i, t)

instance Alternative Parser where
  empty = pure undefined
  p <|> q = choice [p, q]

instance Monad Parser where
  return = pure
  m >>= k = Parser $ do
    ~(_, r) <- get
    put (mempty, r)
    x <- unParser m
    ~(h, s) <- get
    put (mempty, s)
    y <- unParser (k x)
    ~(i, t) <- get
    y <$ put (mappend h i, t)

-- | Pretty printing
--
prettyRules :: Parser a -> String
prettyRules p = unlines
  [ unwords [x, "\n\t::=", pretty y, "\n"]
  | (x, y) <- Map.assocs $ rules p
  , y /= mempty
  ]

pretty :: Grammar -> String
pretty Empty           = mempty
pretty (Label key)     = key
pretty (Choice xs)     = unwords $ intersperse "\n\t  |" (fmap pretty xs)
pretty (Append xs)     = unwords $ fmap pretty xs
pretty (Many g)        = unwords ["{", pretty g, "}"]
pretty (Many1 g)       = unwords ["{", pretty g, "}"]
pretty (SepBy  g h)    = unwords ["{", pretty g, pretty h, "}"]
pretty (SepBy1 g h)    = unwords [pretty g, "{", pretty h, pretty g, "}"]
pretty (SepEndBy g h)  = unwords ["{", pretty g, pretty h, "}"]
pretty (Optional g)    = unwords ["[", pretty g, "]"]
pretty (Between x y g) = unwords [pretty x, pretty g, pretty y]


grammar :: Parser a -> Grammar
grammar (Parser p) = fst $ execState p mempty

rules :: Parser a -> Rules
rules (Parser p) = fst $ snd $ execState p mempty

-- | Combinators
-- 
optional :: Parser a -> Parser (Maybe a)
optional (Parser p) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* p
  ~(h, s) <- get
  Nothing <$ put (Optional h, s)
  
many :: Parser a -> Parser [a]
many (Parser p) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* p
  ~(h, s) <- get
  mempty <$ put (Many h, s)
  
many1 :: Parser a -> Parser [a]
many1 (Parser p) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* p
  ~(h, s) <- get
  mempty <$ put (Many1 h, s)
  
try :: Parser a -> Parser a
try = id 

choice :: [Parser a] -> Parser a
choice [] = A.empty
choice ps = Parser $ do
  result <- forM ps $ \(Parser p) -> do
    ~(_, r) <- get
    put (mempty, r)
    a <- p
    ~(h, s) <- get
    put (h, s)
    pure (a, h)
  ~(_, r) <- get
  put (foldr cappend mempty (snd <$> result), r)
  pure $ fst . head $ result

between :: Parser a -> Parser b -> Parser c -> Parser c
between (Parser px) (Parser py) (Parser pz) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* px
  ~(h, s) <- get
  put (mempty, s) <* py
  ~(i, t) <- get
  put (mempty, t)
  c <- pz
  ~(j, u) <- get
  c <$ put (Between h i j, u)

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy (Parser p) (Parser q) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* p
  ~(h, s) <- get
  put (mempty, s) <* q
  ~(i, t) <- get
  mempty <$ put (SepBy h i, t)

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 (Parser p) (Parser q) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* p
  ~(h, s) <- get
  put (mempty, s) <* q
  ~(i, t) <- get
  mempty <$ put (SepBy1 h i, t)

sepEndBy :: Parser a -> Parser b -> Parser [a]
sepEndBy (Parser p) (Parser q) = Parser $ do
  ~(_, r) <- get
  put (mempty, r) <* p
  ~(h, s) <- get
  put (mempty, s) <* q
  ~(i, t) <- get
  mempty <$ put (SepEndBy h i, t)

(<?>) :: Parser a -> String -> Parser a
Parser p <?> key = Parser $ do
  ~(_, ~(r, xs)) <- get
  put (mempty, (r, xs))
  a <- p
  ~(h, _) <- get
  if Map.member key r
    then a <$ put (Label key, (r, xs))
    else do
      put (mempty, (Map.insert key h r, key : xs))
      ~(_, s) <- p *> get
      a <$ put (Label key, s)
infixl 0 <?>

tokenPrim
  :: Monoidal a
  => (Lexer Token -> String)
  -> (SourcePos -> Lexer Token -> [Lexer Token] -> SourcePos)
  -> (Lexer Token -> Maybe a)
  -> Parser a
tokenPrim _ _ _ = pure zero

-- | Empty structures
--
class Monoidal a where
  zero :: a

instance Monoidal Token
  where zero = Tok_Null

instance Monoidal ()
  where zero = mempty

instance Monoidal Text
  where zero = mempty


