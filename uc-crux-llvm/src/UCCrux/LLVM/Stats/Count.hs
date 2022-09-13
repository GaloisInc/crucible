{-
Module       : UCCrux.LLVM.Stats.Count
Description  : Unbounded unsigned integers with limited arithmetic operations.
Copyright    : (c) Galois, Inc 2022
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

Intended to be imported qualified as @Count@.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module UCCrux.LLVM.Stats.Count
  ( Count
  , fromNat
  , toNat
  , zero
  , one
  , inc
  , plus
  , absDiff
  , div
  , divNat
  )
where

import           Prelude hiding (div, log)
import qualified Prelude as Pre
import           Numeric.Natural (Natural)

-- | Type of unbounded unsigned integers with limited arithmetic operations.
--
-- Semantically intended to count stuff.
--
-- Comparison to other types:
--
-- * 'Word' has different semantic connotations - the name implies it is just a
--   bitvector of machine-word size. It is bounded, which may lead to over- and
--   under-flow.
-- * 'Natural' supports operations that can throw exceptions such as @-@.
-- * 'Int' is signed.
newtype Count = Count { getCount :: Natural }
  deriving (Eq, Enum, Ord, Show)

fromNat :: Natural -> Count
fromNat = Count

toNat :: Count -> Natural
toNat = getCount

-- | @zero == 'fromNat' 0@.
zero :: Count
zero = Count 0

-- | @one == 'fromNat' 1@.
one :: Count
one = Count 1

-- | @inc == 'plus' 'one'@.
inc :: Count -> Count
inc = Count . (+1) . getCount

-- | @'plus' c d == 'fromNat' ('toNat' c + 'toNat' d)@.
plus :: Count -> Count -> Count
plus c d = Count (getCount c + getCount d)

-- | Absolute value of the difference between two 'Count'.
absDiff :: Count -> Count -> Natural
absDiff (Count c1) (Count c2) = max c1 c2 - min c1 c2

-- | Integer (truncating) division
div :: Count -> Count -> Count
div c1 c2 = Count (getCount c1 `Pre.div` getCount c2)

-- | Integer (truncating) division by a 'Natural'
divNat :: Count -> Natural -> Count
divNat c w = c `div` Count w
