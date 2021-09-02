{-
Module       : UCCrux.LLVM.Run.Explore.Config
Description  : Configuration for exploration
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Run.Explore.Config
  ( ExploreConfig (..),
  )
where

import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName)

data ExploreConfig = ExploreConfig
  { exploreAgain :: Bool,
    exploreBudget :: Int,
    exploreTimeout :: Int,
    exploreParallel :: Bool,
    exploreSkipFunctions :: [FunctionName]
  }
  deriving (Eq, Ord, Show)
