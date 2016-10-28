------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.Arithmetic
-- Description      : Utility functions for execution of LLVM Symbolic
--                    programs.
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
-- License          : BSD3
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
module Lang.Crucible.Utils.Arithmetic
  ( -- * Arithmetic utilities
    isPow2
  , lg
  , lgCeil
  , nextMultiple
  , nextPow2Multiple
  , tryIntSqrt
  , tryRationalSqrt
  , roundAway
  ) where

import Control.Exception (assert)
import Data.Bits (Bits(..))
import Data.Ratio

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

-- | Returns true if number is a power of two.
isPow2 :: (Bits a, Num a) => a -> Bool
isPow2 x = x .&. (x-1) == 0

-- | Returns floor of log base 2.
lg :: (Bits a, Num a, Ord a) => a -> Int
lg i0 | i0 > 0 = go 0 (i0 `shiftR` 1)
      | otherwise = error "lg given number that is not positive."
  where go r 0 = r
        go r n = go (r+1) (n `shiftR` 1)

-- | Returns ceil of log base 2.
lgCeil :: (Bits a, Num a, Ord a) => a -> Int
lgCeil 1 = 0
lgCeil i | i > 1 = 1 + lg (i-1)
         | otherwise = error "lgCeil given number that is not positive."

-- | @nextMultiple x y@ computes the next multiple m of x s.t. m >= y.  E.g.,
-- nextMultiple 4 8 = 8 since 8 is a multiple of 8; nextMultiple 4 7 = 8;
-- nextMultiple 8 6 = 8.
nextMultiple :: Integral a => a -> a -> a
nextMultiple x y = ((y + x - 1) `div` x) * x

-- | @nextPow2Multiple x n@ returns the smallest multiple of @2^n@
-- not less than @x@.
nextPow2Multiple :: (Bits a, Integral a) => a -> Int -> a
nextPow2Multiple x n | x >= 0 && n >= 0 = ((x+2^n -1) `shiftR` n) `shiftL` n
                     | otherwise = error "nextPow2Multiple given negative value."

------------------------------------------------------------------------
-- Sqrt operators.

-- | This returns the sqrt of an integer if it is well-defined.
tryIntSqrt :: Integer -> Maybe Integer
tryIntSqrt 0 = return 0
tryIntSqrt 1 = return 1
tryIntSqrt 2 = Nothing
tryIntSqrt 3 = Nothing
tryIntSqrt n = assert (n >= 4) $ go (n `shiftR` 1)
  where go x | x2 < n  = Nothing   -- Guess is below sqrt, so we quit.
             | x2 == n = return x' -- We have found sqrt
             | True    = go x'     -- Guess is still too large, so try again.
          where -- Next guess is floor(avg(x, n/x))
                x' = (x + n `div` x) `div` 2
                x2 = x' * x'

-- | Return the rational sqrt of a
tryRationalSqrt :: Rational -> Maybe Rational
tryRationalSqrt r = do
  (%) <$> tryIntSqrt (numerator   r)
      <*> tryIntSqrt (denominator r)

------------------------------------------------------------------------
-- Conversion

-- | Evaluate a real to an integer with rounding away from zero.
roundAway :: (RealFrac a) => a -> Integer
roundAway r = truncate (r + signum r * 0.5)
