{-|
This module defines types and operations for parsing results from SMTLIB2.

It does not depend on the rest of What4 so that it can be used
directly by clients interested in generating SMTLIB without depending
on the What4 formula interface.  All the type constructors are exposed
so that clients can generate new values that are not exposed through
this interface.
-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
module What4.Protocol.SMTLib2.Parse
  ( -- * CheckSatResponse
    CheckSatResponse(..)
  , readCheckSatResponse
    -- * GetModelResonse
  , GetModelResponse
  , readGetModelResponse
  , ModelResponse(..)
  , DefineFun(..)
  , Symbol
    -- ** Sorts
  , Sort(..)
  , pattern Bool
  , pattern Int
  , pattern Real
  , pattern RoundingMode
  , pattern Array
    -- ** Terms
  , Term(..)
  ) where

import           Control.Monad.Reader
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import           Data.Char
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HSet
import           Data.Monoid ((<>))
import           Data.Ratio
import           Data.String
import           Data.Word
import           System.IO

b2c :: Char -> Word8
b2c = fromIntegral . fromEnum

------------------------------------------------------------------------
-- Parser definitions

newtype Parser a = Parser (ReaderT Handle IO a)
  deriving (Functor, Applicative, Monad)

runParser :: Handle -> Parser a -> IO a
runParser h (Parser f) = runReaderT f h

parseChar :: Parser Char
parseChar = Parser $ ReaderT $ hGetChar

peekChar :: Parser Char
peekChar = Parser $ ReaderT $ hLookAhead

dropChar :: Parser ()
dropChar = Parser $ ReaderT $ \h -> hGetChar h *> pure ()

matchChar :: Char -> Parser ()
matchChar expected = do
  c <- parseChar
  if c == expected then
    pure ()
   else if isSpace c then
    matchChar expected
   else
    fail $ "Unexpected input char " ++ show c ++ "(expected " ++ show expected ++ ")"

dropWhitespace :: Parser ()
dropWhitespace = do
  c <- peekChar
  if isSpace c then do
    parseChar >> dropWhitespace
   else
    pure ()

-- | Drop whitespace until we reach the given string.
matchString :: BS.ByteString -> Parser ()
matchString expected = do
  dropWhitespace
  found <- Parser $ ReaderT $ \h -> BS.hGet h (BS.length expected)
  when (found /= expected) $ do
    fail $ "Unexpected string " ++ show found ++ "(expected " ++ show expected ++ ")"

parseUntilCloseParen' :: [a] -> Parser a -> Parser [a]
parseUntilCloseParen' prev p = do
  c <- peekChar
  if isSpace c then
    parseChar >> parseUntilCloseParen' prev p
   else if c == ')' then
    pure $ reverse prev
   else do
    p >>= \n -> parseUntilCloseParen' (n:prev) p

parseUntilCloseParen :: Parser a -> Parser [a]
parseUntilCloseParen = parseUntilCloseParen' []


-- | @takeChars' p prev h@ prepends characters read from @h@ to @prev@
-- until @p@ is false, and returns the resulting string.
takeChars' :: (Char -> Bool) -> [Word8] -> Parser [Word8]
takeChars' p prev = do
  c <- peekChar
  if p c then do
    _ <- parseChar
    takeChars' p (b2c c:prev)
   else do
    pure $! prev

-- | @takeChars p@ returns the bytestring formed by reading
-- characters until @p@ is false.
takeChars :: (Char -> Bool) -> Parser BS.ByteString
takeChars p = do
  l <- takeChars' p []
  pure $! BS.pack (reverse l)


instance IsString (Parser ()) where
  fromString = matchString . fromString

$(pure [])

class CanParse a where
  parse :: Parser a

  -- | Read the given
  readFromHandle :: Handle -> IO a
  readFromHandle h = runParser h parse


------------------------------------------------------------------------
-- Parse check-sat definitions

-- | Result of check-sat and check-sat-assuming
data CheckSatResponse
   = SatResponse
   | UnsatResponse
   | UnknownResponse
   | CheckSatUnsupported
   | CheckSatError !String

parseQuotedString :: Parser String
parseQuotedString = do
  dropWhitespace
  matchChar '"'
  l <- takeChars (/= '"')
  matchChar '"'
  pure $ UTF8.toString l

instance CanParse CheckSatResponse where
  parse = do
    isParen <- checkParen
    if isParen then do
      matchString "error"
      msg <- parseQuotedString
      closeParen
      pure (CheckSatError msg)
     else
      matchApp [ ("sat",     pure SatResponse)
               , ("unsat",   pure UnsatResponse)
               , ("unknown", pure UnknownResponse)
               , ("unsupported", pure CheckSatUnsupported)
               ]

readCheckSatResponse :: Handle -> IO CheckSatResponse
readCheckSatResponse = readFromHandle

------------------------------------------------------------------------
-- Parse get-model definitions

newtype Symbol = Symbol BS.ByteString
  deriving (Eq)

instance Show Symbol where
  show (Symbol s) = show s

instance IsString Symbol where
  fromString = Symbol . fromString

symbolCharSet :: HashSet Char
symbolCharSet = HSet.fromList
  $  ['A'..'Z']
  ++ ['a'..'z']
  ++ ['0'..'9']
  ++ ['~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/']

initialSymbolCharSet :: HashSet Char
initialSymbolCharSet = symbolCharSet `HSet.difference` (HSet.fromList ['0'..'9'])

generalReservedWords :: HashSet BS.ByteString
generalReservedWords = HSet.fromList $
  [ "!"
  , "_"
  , "as"
  , "BINARY"
  , "DECIMAL"
  , "exists"
  , "HEXADECIMAL"
  , "forall"
  , "let"
  , "match"
  , "NUMERAL"
  , "par"
  , "STRING"
  ]

commandNames :: HashSet BS.ByteString
commandNames = HSet.fromList $
  [ "assert"
  , "check-sat"
  , "check-sat-assuming"
  , "declare-const"
  , "declare-datatype"
  , "declare-datatypes"
  , "declare-fun"
  , "declare-sort"
  , "define-fun"
  , "define-fun-rec"
  , "define-sort"
  , "echo"
  , "exit"
  , "get-assertions"
  , "get-assignment"
  , "get-info"
  , "get-model"
  , "get-option"
  , "get-proof"
  , "get-unsat-assumptions"
  , "get-unsat-core"
  , "get-value"
  , "pop"
  , "push"
  , "reset"
  , "reset-assertions"
  , "set-info"
  , "set-logic"
  , "set-option"
  ]

reservedWords :: HashSet BS.ByteString
reservedWords = HSet.union generalReservedWords commandNames

instance CanParse Symbol where
  parse = do
    dropWhitespace
    c0 <- peekChar
    if c0 == '|' then do
      r <- takeChars' (`notElem` ['|', '/']) [b2c c0]
      ce <- peekChar
      when (ce /= '|') $ do
        fail $ "Unexpected character " ++ show ce ++ " inside symbol."
      pure $! Symbol (BS.pack $ reverse (b2c ce:r))
     else if HSet.member c0 initialSymbolCharSet then do
      r <- BS.pack . reverse <$> takeChars' (`HSet.member` symbolCharSet) [b2c c0]
      when (HSet.member r reservedWords) $ do
        fail $ "Symbol cannot be reserved word " ++ show r
      pure $! Symbol r
     else do
      fail $ "Unexpected character " ++ show c0 ++ " starting symbol."

matchApp :: [(BS.ByteString, Parser a)] -> Parser a
matchApp actions = do
  dropWhitespace
  w <- takeChars (\c -> 'a' <= c && c <= 'z' || c == '-')
  case filter (\(m,_p) -> m == w) actions of
    [] -> do
      w' <- takeChars (\c -> c `notElem` ['\r', '\n'])
      fail $ "Unsupported keyword: " ++ UTF8.toString (w <> w')
    [(_,p)] -> p
    _:_:_ -> fail $ "internal error: Duplicate keywords " ++ show w


openParen :: Parser ()
openParen = matchChar '('

closeParen :: Parser ()
closeParen = matchChar ')'

checkParen :: Parser Bool
checkParen = do
  c <- peekChar
  if c == '(' then
    dropChar >> pure True
   else if isSpace c then
    parseChar >> checkParen
   else
    pure False

data Sort
  = Sort Symbol [Sort]
  | BitVec !Integer
  | FloatingPoint !Integer !Integer
    -- ^ floating point with exponent bits followed by significand bit.

pattern Bool :: Sort
pattern Bool = Sort "Bool" []

pattern Int :: Sort
pattern Int = Sort "Int" []

pattern Real :: Sort
pattern Real = Sort "Real" []

pattern RoundingMode :: Sort
pattern RoundingMode = Sort "RoundingMode" []

pattern Array :: Sort -> Sort -> Sort
pattern Array x y = Sort "Array" [x,y]

parseDecimal' :: Integer -> Parser Integer
parseDecimal' cur = do
  c <- peekChar
  if '0' <= c && c <= '9' then do
    dropChar
    parseDecimal' $! 10 * cur + toInteger (fromEnum c - fromEnum '0')
   else
    pure cur

-- | Parse the next characters as a decimal number.
--
-- Note. No whitespace may proceed the number.
parseDecimal ::Parser Integer
parseDecimal = parseDecimal' 0

instance CanParse Integer where
  parse = dropWhitespace *> parseDecimal

instance CanParse Sort where
  parse = do
    isParen <- checkParen
    if isParen then do
      sym <- parse
      if sym == "_" then do
        r <- matchApp [ (,) "BitVec" (BitVec <$> parse)
                      , (,) "FloatingPoint" (FloatingPoint <$> parse <*> parse)
                      ]
        closeParen
        pure r
       else
        Sort sym <$> parseUntilCloseParen parse
     else do
      sym <- parse
      pure $! Sort sym []

data Term
   = SymbolTerm !Symbol
   | AsConst !Sort !Term
   | BVTerm !Integer !Integer
   | IntTerm !Integer
     -- ^ @IntTerm v@ denotes the SMTLIB expression @v@ if @v >= 0@ and @(- `(negate v))
     -- otherwise.
   | RatTerm !Rational
     -- ^ @RatTerm r@ denotes the SMTLIB expression @(/ `(numerator r) `(denomator r))@.
   | StoreTerm !Term !Term !Term
     -- ^ @StoreTerm a i v@ denotes the SMTLIB expression @(store a i v)@.
   | IfEqTerm !Symbol !Term !Term !Term
     -- ^ @IfEqTerm v c t f@ denotes the SMTLIB expression @(ite (= v c) t f)@.

parseIntegerTerm :: Parser Integer
parseIntegerTerm = do
  isParen <- checkParen
  if isParen then do
    matchString "-"
    r <- parse
    closeParen
    pure $! negate r
   else do
    parse

parseEq :: Parser (Symbol, Term)
parseEq = do
  openParen
  matchString "="
  var <- parse
  val <- parse
  closeParen
  pure (var,val)

parseTermApp :: Parser Term
parseTermApp = do
  dropWhitespace
  -- Look for (as const tp) as argument
  isParen <- checkParen
  if isParen then do
    matchString "as"
    matchString "const"
    r <- AsConst <$> parse <*> parse
    closeParen
    pure $! r
   else do
    op <- parse :: Parser Symbol
    case op of
      "_" -> do
        matchString "bv"
        BVTerm <$> parseDecimal <*> parse
      "/" -> do
        num <- parseIntegerTerm
        den <- parse
        when (den == 0) $ fail $ "Model contains divide-by-zero"
        pure $ RatTerm (num % den)
      "-" -> do
        IntTerm . negate <$> parse
      "store" ->
        StoreTerm <$> parse <*> parse <*> parse
      "ite" -> do
        (var,val) <- parseEq
        t <- parse
        f <- parse
        pure $ IfEqTerm var val t f
      _ -> do
        fail $ "Unsupported operator symbol " ++ show op

instance CanParse Term where
  parse = do
    dropWhitespace
    c <- peekChar
    if c == '(' then do
      t <- parseTermApp
      closeParen
      pure $! t
     else if isDigit c then
      IntTerm <$> parseDecimal
     else if c == '@' then
      SymbolTerm <$> parse
     else
      fail $ "Could not parse term"

data DefineFun = DefineFun { funSymbol :: !Symbol
                     , funArgs :: ![(Symbol, Sort)]
                     , funResultType :: !Sort
                     , funDef :: !Term
                     }

-- | A line in the model response
data ModelResponse
   = DeclareSortResponse !Symbol !Integer
   | DefineFunResponse !DefineFun

parseSortedVar :: Parser (Symbol, Sort)
parseSortedVar = openParen *> ((,) <$> parse <*> parse) <* closeParen

-- | Parses ⟨symbol⟩ ( ⟨sorted_var⟩∗ ) ⟨sort⟩ ⟨term⟩
parseDefineFun :: Parser DefineFun
parseDefineFun = do
  sym <- parse
  args <- openParen *> parseUntilCloseParen parseSortedVar
  res <- parse
  def <- parse
  pure $! DefineFun { funSymbol = sym
                    , funArgs = args
                    , funResultType = res
                    , funDef = def
                    }

instance CanParse ModelResponse where
  parse = do
    openParen
    r <- matchApp [ (,) "declare-sort"    $ DeclareSortResponse <$> parse <*> parse
                  , (,) "define-fun"      $ DefineFunResponse <$> parseDefineFun
                  , (,) "define-fun-rec"  $ fail "Do not yet support define-fun-rec"
                  , (,) "define-funs-rec" $ fail "Do not yet support define-funs-rec"
                  ]
    closeParen
    pure $! r

type GetModelResponse = [ModelResponse]


readGetModelResponse :: Handle -> IO GetModelResponse
readGetModelResponse h =
  runParser h $
    openParen *> parseUntilCloseParen parse
