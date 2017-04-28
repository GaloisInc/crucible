{-
Module           : Lang.Crucible.Utils.SExp
Copyright        : (c) Galois, Inc 2014
License          : BSD3
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Provides a function for reading decimal numbers returned
by Z3 or Yices.
-}
{-# LANGUAGE PatternGuards #-}
module Lang.Crucible.Solver.SimpleBackend.ReadDecimal
  ( readDecimal
  ) where

import Control.Lens (over, _1)
import Data.Ratio

-- | Read decimal number, returning rational and rest of string, or a failure
-- message if first character is not a digit.
--
-- A decimal number has the form (-)([0..9])+([0..9])+'.'([0.9]'*('?')?
readDecimal :: Monad m => String -> m (Rational, String)
readDecimal ('-':c:r) | Just i <- asDigit c =
  return $! over _1 negate $ readDecimal' (toRational i) r
readDecimal (c:r) | Just i <- asDigit c =
  return $ readDecimal' (toRational i) r
readDecimal _ = fail "Could not parse string."

readDecimal' :: Rational -- ^ Value so far
             -> String -- ^ String so far
             -> (Rational, String)
readDecimal' v (c:r) | Just i <- asDigit c =
  let v' = 10 * v + toRational i
   in readDecimal' v' r
readDecimal' v ('.':r) = readDigits v r 10
readDecimal' v d = (v,d)

readDigits :: Rational
           -> String
           -> Integer -- ^ Value to divide next digit by.
           -> (Rational, String)
readDigits v (c:r) d
  | Just i <- asDigit c =
     let v' = v + (toInteger i%d)
      in readDigits v' r (10*d)
readDigits v ('?':r) _ = (v,r)
readDigits v r _ = (v,r)

asDigit :: Char -> Maybe Int
asDigit c | fromEnum '0' <= i && i <= fromEnum '9' = Just (i - fromEnum '0')
          | otherwise = Nothing
  where i = fromEnum c
