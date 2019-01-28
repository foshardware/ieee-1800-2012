{-# LANGUAGE ScopedTypeVariables, TupleSections #-}

module Language.SystemVerilog.Alternative.Grammar
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
  , bnf, bnfRules
  , cppTypes
  , Monoidal(..)
  ) where

import qualified Control.Applicative as A
import Control.Applicative (Alternative, (<|>))
import Control.Monad
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Char
import Data.Foldable
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
  | Optional Grammar
  | Append [Grammar]
  | Choice [Grammar]
  | Symbol Key
  | Empty
  deriving (Eq, Show)

instance Semigroup Grammar where
  (<>) = mappend

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


-- | Print BNF
--
bnfRules :: Parser a -> String
bnfRules p = unlines
  [ unwords [x, "\n\t::=", bnf y, "\n"]
  | (x, y) <- Map.assocs $ rules p
  ]

bnf :: Grammar -> String
bnf Empty           = mempty
bnf (Symbol key)    = key
bnf (Choice xs)     = unwords $ intersperse "\n\t  |" (fmap bnf xs)
bnf (Append xs)     = unwords $ fmap bnf xs
bnf (Many g)        = unwords ["{", bnf g, "}"]
bnf (Many1 g)       = unwords [bnf g, "{", bnf g, "}"]
bnf (SepBy  g h)    = unwords ["{", bnf g, bnf h, "}"]
bnf (SepBy1 g h)    = unwords [bnf g, "{", bnf h, bnf g, "}"]
bnf (SepEndBy g h)  = unwords ["{", bnf g, bnf h, "}"]
bnf (Optional g)    = unwords ["[", bnf g, "]"]

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
  c <$ put (h <> j <> i, u)

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
    then a <$ put (Symbol key, (r, xs))
    else do
      put (mempty, (Map.insert key h r, key : xs))
      ~(_, s) <- p *> get
      a <$ put (Symbol key, s)
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


-- | Grammar normalization
--
dnf :: Grammar -> Grammar
dnf (Optional (Append xs))
  | Choice ys <- dnf $ Append xs
  = Choice [dnf $ Optional y | y <- fmap dnf ys]
dnf (Optional (Append xs))
  = Optional $ dnf $ Append xs
dnf (Optional (Choice xs))
  = Choice [dnf $ Optional x | x <- fmap dnf xs]
dnf (Choice xs)
  | any isChoice (fmap dnf xs)
  = dnf $ foldr cappend mempty (fmap dnf xs)
dnf (Append xs)
  | (as, Choice ys : bs) <- break isChoice (fmap dnf xs)
  = dnf $ foldr cappend mempty [dnf $ Append as <> y <> Append bs | y <- ys]
dnf g = g

isChoice :: Grammar -> Bool
isChoice (Optional (Choice _)) = True
isChoice (Choice _) = True
isChoice _ = False

type Builder = Writer String ()

post :: String -> Builder
post s = tell s *> tell "\n"


-- | C++ type definitions
--
cppTypes :: Parser a -> String
cppTypes p = execWriter $ do
  post "#include <optional>"
  post "#include <string>"
  post "#include <tuple>"
  post "#include <boost/variant.hpp>"
  post "#include <boost/mpl/vector.hpp>"
  post "#include <vector>"
  post mempty
  let result = fmap (\(k, g) -> (k, dnf g)) $ Map.assocs $ rules p
  for_ result $ \(k, g) -> do
    cppForward k g
  post mempty
  for_ result $ \(k, g) -> do
    cppType k g

cppType :: Key -> Grammar -> Builder
cppType k Empty | isCaps k = pure ()
cppType k Empty = post $ "typedef std::string "++ uscores k ++";"
cppType _ (Append [ ]) = pure ()
cppType k (Append [x]) = cppType k x
cppType _ (Choice [ ]) = pure ()
cppType k (Choice [x]) = cppType k x
cppType k (Append  xs) | all isToken xs = cppEnum k [x | Symbol x <- xs]
cppType k (Append  xs) = cppClass k $ filter (not . isToken) xs
cppType k (Choice  xs) | all isToken xs = cppEnum k [x | Symbol x <- xs]
cppType k (Choice  xs) = cppUnion k $ filter (not . isToken) xs
cppType k (Symbol lbl) | isCaps lbl = cppEnum k [lbl]
cppType k (Symbol lbl) = cppTypedef k (Symbol lbl)
cppType k (Optional s) = cppTypedef k s
cppType k (Many     s) = cppTypedef k s
cppType k (Many1    s) = cppTypedef k s
cppType k (SepBy    s _) = cppTypedef k s
cppType k (SepBy1   s _) = cppTypedef k s
cppType k (SepEndBy s _) = cppTypedef k s

cppForward :: Key -> Grammar -> Builder
cppForward k Empty | isCaps k = pure ()
cppForward k Empty = post $ "typedef std::string "++ uscores k ++";"
cppForward _ (Append [ ]) = pure ()
cppForward k (Append [x]) = cppForward k x
cppForward _ (Choice [ ]) = pure ()
cppForward k (Choice [x]) = cppForward k x
cppForward k (Append  xs)
  | all isToken xs = post $ "enum class "++ uscores k ++";"
cppForward k (Append   _) = post $ "class "++ uscores k ++";"
cppForward k (Choice  xs)
  | all isToken xs = post $ "enum class "++ uscores k ++" ;"
cppForward k (Choice   _) = post $ "class "++ uscores k ++";"
cppForward k (Symbol lbl) | isCaps lbl = post $ "enum class "++ uscores k ++";"
cppForward k (Symbol lbl) = cppForwardTypedef k (Symbol lbl)
cppForward k (Optional s) = cppForwardTypedef k s
cppForward k (Many     s) = cppForwardTypedef k s
cppForward k (Many1    s) = cppForwardTypedef k s
cppForward k (SepBy    s _) = cppForwardTypedef k s
cppForward k (SepBy1   s _) = cppForwardTypedef k s
cppForward k (SepEndBy s _) = cppForwardTypedef k s

cppTypedef :: Key -> Grammar -> Builder
cppTypedef key g = do
  post $ unwords ["class", uscores key]
  post "{"
  post "public:"
  cppConstructor (uscores key) mempty
  cppConstructor (uscores key) [g]
  post mempty
  cppFields [g]
  post "};"

cppForwardTypedef :: Key -> Grammar -> Builder
cppForwardTypedef key _ = post $ "class "++ uscores key ++";"

cppUnion :: Key -> [Grammar] -> Builder
cppUnion key gs = do
  post $ unwords ["class", uscores key]
  post "{"
  post "\ttypedef boost::mpl::vector<> v0;"
  for_ ([1..] `zip` [g | g <- reverse gs, not $ isToken g]) $ \(i :: Int, g) ->
    post $ "\ttypedef boost::mpl::push_front<v"++ show (i-1) ++", "
         ++ "boost::recursive_wrapper<"++ typeOf g ++ ">>::type v"++ show i ++";"
  post "public:"
  cppConstructor (uscores key) mempty
  post $ "\tboost::make_variant_over<v"++ show (length gs) ++">::type choice;"
  post "};"
  post mempty

cppEnum :: Key -> [String] -> Builder
cppEnum key xs = do
  post $ unwords ["enum", "class", uscores key]
  post "{"
  post $ concat $ "\t" : intersperse ", " (capitalize <$> xs)
  post "};"
  post mempty

cppClass :: Key -> [Grammar] -> Builder
cppClass key gs = do
  post $ unwords ["class", uscores key]
  post "{"
  post "public:"
  cppConstructor (uscores key) mempty
  cppConstructor (uscores key) gs
  post mempty
  cppFields gs
  post "};"
  post mempty

typeOf :: Grammar -> String
typeOf Empty = "std::string"
typeOf (Symbol t) | isCaps t = "int"
typeOf (Symbol t) = uscores t
typeOf (Optional t) = "std::optional<"++ typeOf t ++">"
typeOf (Many  t) = "std::vector<"++ typeOf t ++">"
typeOf (Many1 t) = "std::vector<"++ typeOf t ++">"
typeOf (SepBy    t _) = "std::vector<"++ typeOf t ++">"
typeOf (SepBy1   t _) = "std::vector<"++ typeOf t ++">"
typeOf (SepEndBy t _) = "std::vector<"++ typeOf t ++">"
typeOf (Append [ ]) = mempty
typeOf (Append [x]) = typeOf x
typeOf (Append  xs) | [x] <- filter (not . isToken) xs = typeOf x
typeOf (Append  xs) | all isToken xs = "int"
typeOf (Append  xs) = "std::tuple<"
  ++ concat (intersperse ", " (typeOf <$> filter (not . isToken) xs)) ++">"
typeOf _ = mempty

variable :: Grammar -> String
variable Empty = "value"
variable (Symbol t) = lower (uscores t)
variable (Optional t) = variable t 
variable (Many  t) = variable t
variable (Many1 t) = variable t
variable (SepBy    t _) = variable t
variable (SepBy1   t _) = variable t
variable (SepEndBy t _) = variable t
variable (Append [ ]) = mempty
variable (Append [x]) = variable x
variable (Append  xs) | [x] <- filter (not . isToken) xs = variable x
variable (Append  xs) | all isToken xs = "discard"
variable (Append  xs) = variable $ head $ filter (not . isToken) xs
variable _ = mempty

enumerate :: [Grammar] -> [(Int, Grammar, String)]
enumerate gs =
  [ (i, g, variable g ++ if variable g `elem` du then show i else mempty)
  | (i, g) <- elements
  , let du = [variable h | (j, h) <- elements, j /= i]
  ]
  where elements = zip [0..] gs

cppFields :: [Grammar] -> Builder
cppFields gs = for_ (enumerate gs) $ \(_, g, s) -> do
  post $ "\t"++ typeOf g ++" *"++ s ++";"

cppConstructor :: String -> [Grammar] -> Builder
cppConstructor name gs
  = post
  $ "\t"++ name ++"("++ concat (intersperse ", " $ constArgs <$> enumerate gs) ++") "
  ++"{ "++ concat (constAssign <$> enumerate gs) ++"}"
  where constArgs (_, g, s) = unwords [typeOf g, "*", '_' : s]
        constAssign (_, _, s) = unwords [s, "=", '_' : s ++ "; "]

isToken :: Grammar -> Bool
isToken (Append xs)  = all isToken xs
isToken (Choice xs)  = all isToken xs
isToken (Symbol lbl) = isCaps lbl
isToken (Optional (Symbol lbl)) = isCaps lbl
isToken _ = False

capitalize :: String -> String
capitalize (x : xs) = toUpper x : fmap toLower xs
capitalize [] = []

lower :: String -> String
lower (x : xs) = toLower x : xs
lower [] = []

isCaps :: String -> Bool
isCaps = all $ \x -> x == toUpper x

uscores :: String -> String
uscores (u : us) = toUpper u : go us
  where go ('_' : x : xs) = toUpper x : go xs
        go (x : xs) = x : go xs
        go [] = []
uscores us = us


