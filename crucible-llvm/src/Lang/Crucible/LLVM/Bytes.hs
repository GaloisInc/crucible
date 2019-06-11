-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Bytes
-- Description      : A type representing numbers of bytes.
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
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
  )  where

import Data.Data (Data)
import GHC.Generics (Generic)
import Numeric.Natural

-- | A newtype for expressing numbers of bytes.
--   This newtype is explicitly introduced to avoid confusion
--   between widths expressed as numbers of bits vs numbers of bytes.
newtype Bytes = Bytes { unBytes :: Integer }
  deriving (Data, Eq, Generic, Ord, Num, Enum, Real, Integral)

instance Show Bytes where
  show (Bytes n) = show n

bytesToBits :: Bytes -> Natural
bytesToBits (Bytes n) = 8 * fromIntegral n

bytesToNatural :: Bytes -> Natural
bytesToNatural (Bytes n) = fromIntegral n

bytesToInteger :: Bytes -> Integer
bytesToInteger (Bytes n) = n

toBytes :: Integral a => a -> Bytes
toBytes = Bytes . fromIntegral

bitsToBytes :: Integral a => a -> Bytes
bitsToBytes n = Bytes ( (fromIntegral n + 7) `div` 8 )

type Addr = Bytes
type Offset = Bytes
