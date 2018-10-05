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
  , bytesToInteger
  , toBytes
  , bitsToBytes
  )  where

import Data.Word

-- | A newtype for expressing numbers of bytes.
--   This newtype is explicitly introduced to avoid confusion
--   between widths expressed as numbers of bits vs numbers of bytes.
newtype Bytes = Bytes { unBytes :: Word64 }
  deriving (Eq, Ord, Num)

instance Show Bytes where
  show (Bytes n) = show n

bytesToBits :: Bytes -> Integer
bytesToBits (Bytes n) = 8 * toInteger n

bytesToInteger :: Bytes -> Integer
bytesToInteger (Bytes n) = toInteger n

toBytes :: Integral a => a -> Bytes
toBytes = Bytes . fromIntegral

bitsToBytes :: Integral a => a -> Bytes
bitsToBytes n = Bytes ( (fromIntegral n + 7) `div` 8 )

type Addr = Bytes
type Offset = Bytes
