------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.BitSet
-- Description      : Encode a set of enumerable elements using the bit-positions
--                    in an Integer
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides a simple bitset datastructure
-- built on top of GHC-native Integers.
------------------------------------------------------------------------
module Lang.Crucible.Utils.BitSet
( BitSet
, getBits
, empty
, null
, singleton
, insert
, remove
, size
, member
, isSubsetOf
, difference
, intersection
, union
, toList
, foldr
, foldl
, foldl'
) where

import Data.Bits
import Data.Word
import Data.Hashable
import qualified Data.List as List
import Prelude hiding (null, foldr, foldl, foldl')

newtype BitSet a = BitSet { getBits :: Integer }
 deriving (Show, Eq, Ord)

instance Hashable (BitSet a) where
  hashWithSalt s (BitSet x) = hashWithSalt s x

empty :: BitSet a
empty = BitSet zeroBits

null :: BitSet a -> Bool
null = (0 ==) . getBits

singleton :: Enum a => a -> BitSet a
singleton a = BitSet (bit (fromEnum a))

insert :: Enum a => a -> BitSet a -> BitSet a
insert a (BitSet x) = BitSet (setBit x (fromEnum a))

remove :: Enum a => a -> BitSet a -> BitSet a
remove a (BitSet x) = BitSet (clearBit x (fromEnum a))

union :: BitSet a -> BitSet a -> BitSet a
union (BitSet x) (BitSet y) = BitSet (x .|. y)

intersection :: BitSet a -> BitSet a -> BitSet a
intersection (BitSet x) (BitSet y) = BitSet (x .&. y)

difference :: BitSet a -> BitSet a -> BitSet a
difference (BitSet x) (BitSet y) = BitSet (x .&. complement y)

isSubsetOf :: BitSet a -> BitSet a -> Bool
isSubsetOf (BitSet x) (BitSet y) = x .|. y == y

member :: Enum a => a -> BitSet a -> Bool
member a (BitSet x) = testBit x (fromEnum a)

size :: BitSet a -> Int
size (BitSet x) = popCount x

toList :: Enum a => BitSet a -> [a]
toList (BitSet bs) = go bs 0
  where go :: Enum a => Integer -> Int -> [a]
        go 0 _ = []
        go x i
           | y .&. 0xffffffff == 0 = go (shiftR x 32) $! (i + 32)
           | y .&. 0x0000ffff == 0 = go (shiftR x 16) $! (i + 16)
           | y .&. 0x000000ff == 0 = go (shiftR x  8) $! (i + 8)
           | otherwise = concat
               [ if testBit y 0 then [toEnum (i + 0)] else []
               , if testBit y 1 then [toEnum (i + 1)] else []
               , if testBit y 2 then [toEnum (i + 2)] else []
               , if testBit y 3 then [toEnum (i + 3)] else []
               , if testBit y 4 then [toEnum (i + 4)] else []
               , if testBit y 5 then [toEnum (i + 5)] else []
               , if testBit y 6 then [toEnum (i + 6)] else []
               , if testBit y 7 then [toEnum (i + 7)] else []
               , go (shiftR x 8) $! (i + 8)
               ]

          where y :: Word32
                y = fromInteger x

foldl' :: Enum a => (b -> a -> b) -> b -> BitSet a -> b
foldl' f z = List.foldl' f z . toList

foldl :: Enum a => (b -> a -> b) -> b -> BitSet a -> b
foldl f z = List.foldl f z . toList

foldr :: Enum a => (a -> b -> b) -> b -> BitSet a -> b
foldr f z = List.foldr f z . toList
