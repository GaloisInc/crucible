{-|
Module      : What4.Utils.IncrHash
Copyright   : (c) Galois Inc, 2019
License     : BSD3
Maintainer  : rdockins@galois.com

A basic datatype for incremental hashing which
supports a monoid instance.  Currently this is
simply implemented as bitwise xor for simplicity.

If we later wish to experiment with other incremenal hash
algorithms, this module abstracts over the implementation
details.
-}

module What4.Utils.IncrHash
( IncrHash
, mkIncrHash
, toIncrHash
, toIncrHashWithSalt
) where

import Data.Bits
import Data.Hashable

newtype IncrHash = IncrHash Int
 deriving (Eq,Ord)

instance Semigroup IncrHash where
  IncrHash x <> IncrHash y = IncrHash (x `xor` y)

instance Monoid IncrHash where
  mempty = IncrHash 0
  mappend = (<>)

mkIncrHash :: Int -> IncrHash
mkIncrHash = IncrHash

toIncrHash :: Hashable a => a -> IncrHash
toIncrHash = IncrHash . hash

toIncrHashWithSalt :: Hashable a => Int -> a -> IncrHash
toIncrHashWithSalt s a = IncrHash (hashWithSalt s a)

instance Hashable IncrHash where
  hashWithSalt s (IncrHash h) = hashWithSalt s h
