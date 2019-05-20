-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Bytes
-- Description      : A type representing numbers of bytes.
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lang.Crucible.LLVM.Bytes
  ( -- * Bytes
    Bytes(..)
  , Addr
  , Offset
  , bytesToBits
  , bytesToNatural
  , bytesToInteger
  , toBytes
  , bitsToBytes
  , multBytes
  , divModBytes
  , divBytes
  )  where

import Numeric.Natural

-- | A newtype for expressing numbers of bytes.
--   This newtype is explicitly introduced to avoid confusion
--   between widths expressed as numbers of bits vs numbers of bytes.
newtype Bytes = Bytes { unBytes :: Natural }
  deriving (Eq, Ord, Num, Enum, Real, Integral)

instance Show Bytes where
  show (Bytes n) = show n

bytesToBits :: Bytes -> Natural
bytesToBits (Bytes n) = 8 * n

bytesToNatural :: Bytes -> Natural
bytesToNatural (Bytes n) = n

bytesToInteger :: Bytes -> Integer
bytesToInteger (Bytes n) = toInteger n

toBytes :: Integral a => a -> Bytes
toBytes = Bytes . fromIntegral

bitsToBytes :: Integral a => a -> Bytes
bitsToBytes n = Bytes ( (fromIntegral n + 7) `div` 8 )

multBytes :: Natural -> Bytes -> Bytes
multBytes x (Bytes y) = Bytes (x*y)

divModBytes :: Bytes -> Bytes -> (Natural, Bytes)
divModBytes (Bytes x) (Bytes y) = (d, Bytes m)
  where (d,m) = divMod x y

divBytes :: Bytes -> Bytes -> Natural
divBytes (Bytes x) (Bytes y) = x `div` y

type Addr = Bytes
type Offset = Bytes
