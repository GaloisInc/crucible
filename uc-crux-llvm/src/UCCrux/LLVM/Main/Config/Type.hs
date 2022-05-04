{-
Module       : UCCrux.LLVM.Config.Type
Description  : Top-level configuration for UC-Crux-LLVM
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

The functions/types in this module aren't necessarily appropriate for using
UC-Crux-LLVM as a library: 'TopLevelConfig' selects among a wide variety of
functionality, a choice that is likely statically known for most library
use-cases. Moreover, these functions/types aren't needed (or used) by the rest
of the library outside of the "UCCrux.LLVM.Main" module.
-}

module UCCrux.LLVM.Main.Config.Type
  ( RunConfig (..),
    TopLevelConfig (..),
  )
where

import           Data.List.NonEmpty (NonEmpty)

import           Crux.LLVM.Config (LLVMOptions)

import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName)
import qualified UCCrux.LLVM.Equivalence.Config as EqConfig
import qualified UCCrux.LLVM.Run.Explore.Config as ExConfig

data RunConfig
  = Explore ExConfig.ExploreConfig
  -- | The 'Bool' is whether or not to check contracts from callers
  | RunOn (NonEmpty FunctionName) [FunctionName] Bool
  | CrashEquivalence EqConfig.EquivalenceConfig
  deriving (Eq, Ord, Show)

data TopLevelConfig = TopLevelConfig
  { ucLLVMOptions :: LLVMOptions,
    runConfig :: RunConfig
  }
