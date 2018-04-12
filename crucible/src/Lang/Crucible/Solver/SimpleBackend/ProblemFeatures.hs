------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
-- Description : Descriptions of the "features" that can occur in queries
-- Copyright   : (c) Galois, Inc 2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lang.Crucible.Solver.SimpleBackend.ProblemFeatures
  ( ProblemFeatures
  , noFeatures
  , useLinearArithmetic
  , useNonlinearArithmetic
  , useComputableReals
  , useIntegerArithmetic
  , useBitvectors
  , useExistForall
  , useQuantifiers
  , useSymbolicArrays
  , useComplexArithmetic
  , useStructs
  , useStrings
  , hasProblemFeature
  ) where

import Data.Bits
import Data.Word

-- | Allowed features represents features that the constraint solver
-- will need to support to solve the problem.
newtype ProblemFeatures = ProblemFeatures Word64
  deriving (Eq, Bits)

-- ProblemFeatures uses bit mask to represent the features.  The bits are:
-- Bits
--  0 : Uses linear arithmetic
--  1 : Uses non-linear arithmetic, i.e. multiplication (should also set bit 0)
--  2 : Uses computational reals (should also set bits 0 & 1)
--  3 : Uses integer variables (should also set bit 0)
--  4 : Uses bitvectors
--  5 : Uses exists-forall.
--  6 : Uses quantifiers (should also set bit 4)
--  7 : Uses symbolic arrays or complex numbers.
--  8 : Uses structs
--  9 : Uses strings

noFeatures :: ProblemFeatures
noFeatures = ProblemFeatures 0

-- | Indicates whether the problem uses linear arithmetic.
useLinearArithmetic :: ProblemFeatures
useLinearArithmetic = ProblemFeatures 0x01

-- | Indicates whether the problem uses non-linear arithmetic.
useNonlinearArithmetic :: ProblemFeatures
useNonlinearArithmetic = ProblemFeatures 0x03

-- | Indicates whether the problem uses computable real functions.
useComputableReals :: ProblemFeatures
useComputableReals = ProblemFeatures 0x04 .|. useNonlinearArithmetic

-- | Indicates the problem contains integer variables.
useIntegerArithmetic :: ProblemFeatures
useIntegerArithmetic = ProblemFeatures 0x08 .|. useLinearArithmetic

-- | Indicates whether the problem uses bitvectors.
useBitvectors :: ProblemFeatures
useBitvectors = ProblemFeatures 0x10

-- | Indicates whether the problem needs exists-forall support.
useExistForall :: ProblemFeatures
useExistForall = ProblemFeatures 0x20

-- | Has general quantifier support.
useQuantifiers :: ProblemFeatures
useQuantifiers = ProblemFeatures 0x60

-- | Indicates whether the problem uses complex arithmetic.
--
-- This is encoded as a symbolic array or struct depending on
-- what features the solver supports.
useComplexArithmetic :: ProblemFeatures
useComplexArithmetic = ProblemFeatures 0x80

-- | Indicates whether the problem uses symbolic arrays.
useSymbolicArrays :: ProblemFeatures
useSymbolicArrays = ProblemFeatures 0x180

-- | Indicates whether the problem uses structs
--
-- Structs are modeled using constructors in CVC4/Z3, and tuples
-- in Yices.
useStructs :: ProblemFeatures
useStructs = ProblemFeatures 0x280

-- | Indicates whether the problem uses strings
--
--   Strings have some symbolic support in CVC4 and Z3.
useStrings :: ProblemFeatures
useStrings = ProblemFeatures 0x200

hasProblemFeature :: ProblemFeatures -> ProblemFeatures -> Bool
hasProblemFeature x y = (x .&. y) == y
