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

data ExploreConfig = ExploreConfig
  { exploreAgain :: Bool,
    exploreBudget :: Int,
    exploreTimeout :: Int,
    exploreParallel :: Bool,
    exploreSkipFunctions :: [String]
  }
  deriving (Eq, Ord, Show)
