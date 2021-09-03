{-
Module       : UCCrux.LLVM.Equivalence.Config
Description  : Configuration for crash-equivalence checking
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Equivalence.Config
  ( OrderOrEquivalence(..),
    EquivalenceConfig(..)
  )
where

import UCCrux.LLVM.Newtypes.FunctionName (FunctionName)

-- | Check for crash ordering or crash equivalence? Ordering asserts that one
-- function\'s undefined behaviors are a subset of the other\'s, equivalence
-- asserts that two functions have the exact same set of undefined behaviors.
data OrderOrEquivalence
  = Order
  | Equivalence
  deriving (Bounded, Eq, Enum, Ord, Show)

data EquivalenceConfig
  = EquivalenceConfig
      { equivModule :: FilePath,
        -- | Entry points. If empty, check functions that are in both modules.
        equivEntryPoints :: [FunctionName],
        -- | See comment on 'OrderOrEquivalence'
        equivOrOrder :: OrderOrEquivalence
      }
  deriving (Eq, Ord, Show)
