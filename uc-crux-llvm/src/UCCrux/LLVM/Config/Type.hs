{-
Module       : UCCrux.LLVM.Config.Type
Description  : Top-level configuration for UC-Crux-LLVM
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Config.Type
  ( RunConfig (..),
    TopLevelConfig (..),
  )
where

import           Data.List.NonEmpty (NonEmpty)

import           Crux.LLVM.Config (LLVMOptions)

import           UCCrux.LLVM.Config.FunctionName (FunctionName)
import qualified UCCrux.LLVM.Equivalence.Config as EqConfig
import qualified UCCrux.LLVM.Run.Explore.Config as ExConfig

data RunConfig
  = Explore ExConfig.ExploreConfig
  | RunOn (NonEmpty FunctionName)
  | CrashEquivalence EqConfig.EquivalenceConfig
  deriving (Eq, Ord, Show)

data TopLevelConfig = TopLevelConfig
  { ucLLVMOptions :: LLVMOptions,
    runConfig :: RunConfig
  }

