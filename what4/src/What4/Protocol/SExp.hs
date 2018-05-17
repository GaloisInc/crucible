{-
Module           : What4.Protocol.SExp
Copyright        : (c) Galois, Inc 2014
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Provides an interface for parsing simple SExpressions
returned by SMT solvers.
-}
module What4.Protocol.SExp
  ( SExp(..)
  , parseSExp
  , stringToSExp
  , parseNextWord
  ) where

import           Control.Applicative
import           Control.Monad (msum)
import           Data.Attoparsec.ByteString.Char8
import qualified Data.ByteString.UTF8 as UTF8
import           Data.Char hiding (isSpace)
import           Data.Monoid
import           Data.String
import           Prelude hiding (takeWhile)

skipSpaceOrNewline :: Parser ()
skipSpaceOrNewline = skipWhile f
  where f c = isSpace c || c == '\r' || c == '\n'

-- | Read next contiguous sequence of numbers or letters.
parseNextWord :: Parser String
parseNextWord = do
  skipSpaceOrNewline
  UTF8.toString <$> mappend (takeWhile1 isAlphaNum) (fail "Unexpected end of stream.")

data SExp = SAtom String
          | SApp [SExp]
  deriving (Eq, Ord, Show)

instance IsString SExp where
  fromString = SAtom

isTokenChar :: Char -> Bool
isTokenChar '(' = False
isTokenChar ')' = False
isTokenChar c = not (isSpace c)

readToken :: Parser String
readToken = UTF8.toString <$> takeWhile1 isTokenChar

parseSExp :: Parser SExp
parseSExp = do
  skipSpaceOrNewline
  msum [ char '(' *> (SApp <$> many parseSExp) <* char ')'
       , SAtom <$> readToken
       ]

stringToSExp :: Monad m => String -> m [SExp]
stringToSExp s = do
  let parseSExpList = many parseSExp <* skipSpace <* endOfInput
  case parseOnly parseSExpList (UTF8.fromString s) of
    Left e -> fail $ "stringToSExpr error: " ++ e
    Right v -> return v
