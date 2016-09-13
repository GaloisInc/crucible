-----------------------------------------------------------------------
-- |
-- Module           : Lang.MATLAB.MatlabChar
-- Description      : This module defines a character typed use in Matlab
--                    expressions.  It is a newtype for a Word16.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines a character typed use in Matlab
-- expressions.  It is a synonym for a Word16.
------------------------------------------------------------------------
module Lang.MATLAB.MatlabChar
  ( MatlabChar(..)
  , matlabChar
  ) where

import Data.Word

-- | A matlab character is an unsigned 16-bit word.
newtype MatlabChar = MatlabChar Word16
 deriving (Eq,Ord)

instance Bounded MatlabChar where
  minBound = MatlabChar minBound
  maxBound = MatlabChar maxBound

instance Enum MatlabChar where
  toEnum i = MatlabChar (fromIntegral i)
  fromEnum (MatlabChar w) = fromIntegral w

-- | Create a MatlabChar from a regular char.
matlabChar :: Char -> MatlabChar
matlabChar c | 0 <= i && i < 2^(16::Int) = toEnum i
             | otherwise = error $ "matlabChar: " ++ show c ++ " is out of range."
  where i = fromEnum c


instance Show MatlabChar where
  show (MatlabChar w) = "0x" ++ show w
