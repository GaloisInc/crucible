{-
Module           : What4.Protocol.SExp
Copyright        : (c) Galois, Inc 2014
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Provides an interface for parsing simple SExpressions
returned by SMT solvers.
-}
{-# LANGUAGE OverloadedStrings #-}
module What4.Protocol.SExp
  ( SExp(..)
  , parseSExp
  , stringToSExp
  , parseNextWord
  , asAtomList
  , asNegAtomList
  , skipSpaceOrNewline
  ) where

import           Control.Applicative
import           Control.Monad (msum)
import           Data.Attoparsec.Text
import           Data.Char
import           Data.Monoid
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Prelude hiding (takeWhile)

skipSpaceOrNewline :: Parser ()
skipSpaceOrNewline = skipWhile f
  where f c = isSpace c || c == '\r' || c == '\n'

-- | Read next contiguous sequence of numbers or letters.
parseNextWord :: Parser Text
parseNextWord = do
  skipSpaceOrNewline
  mappend (takeWhile1 isAlphaNum) (fail "Unexpected end of stream.")

data SExp = SAtom Text
          | SString Text
          | SApp [SExp]
  deriving (Eq, Ord, Show)

instance IsString SExp where
  fromString = SAtom . Text.pack

isTokenChar :: Char -> Bool
isTokenChar '(' = False
isTokenChar ')' = False
isTokenChar '"' = False
isTokenChar c = not (isSpace c)

isStringChar :: Char -> Bool
isStringChar '"'  = False
isStringChar '\\' = False
isStringChar _c   = True

readToken :: Parser Text
readToken = takeWhile1 isTokenChar

readString :: Parser Text
readString = takeWhile1 isStringChar

parseSExp :: Parser SExp
parseSExp = do
  skipSpaceOrNewline
  msum [ char '(' *> skipSpaceOrNewline *> (SApp <$> many parseSExp) <* skipSpaceOrNewline <* char ')'
       , char '"' *> (SString <$> readString) <* char '"'
       , SAtom <$> readToken
       ]

stringToSExp :: Monad m => String -> m [SExp]
stringToSExp s = do
  let parseSExpList = many parseSExp <* skipSpace <* endOfInput
  case parseOnly parseSExpList (Text.pack s) of
    Left e -> fail $ "stringToSExpr error: " ++ e
    Right v -> return v

asNegAtomList :: SExp -> Maybe [(Bool,Text)]
asNegAtomList (SApp xs) = go xs
  where
  go [] = Just []
  go (SAtom a : ys) = ((True,a):) <$> go ys
  go (SApp [SAtom "not", SAtom a] : ys) = ((False,a):) <$> go ys
  go _ = Nothing
asNegAtomList _ = Nothing

asAtomList :: SExp -> Maybe [Text]
asAtomList (SApp xs) = go xs
  where
  go [] = Just []
  go (SAtom a:ys) = (a:) <$> go ys
  go _ = Nothing
asAtomList _ = Nothing
