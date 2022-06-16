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
import           UCCrux.LLVM.Newtypes.Seconds (Seconds)
import Data.Map (Map)
import UCCrux.LLVM.View.Specs (SpecsView)

data ExploreConfig = ExploreConfig
  { -- | Explore functions that already have a log present in the log directory
    exploreAgain :: Bool,
    -- | Number of functions to explore
    exploreBudget :: Int,
    exploreTimeout :: Seconds,
    exploreParallel :: Bool,
    exploreSkipFunctions :: [FunctionName],
    exploreSpecs :: Map FunctionName SpecsView
  }
  deriving (Eq, Ord, Show)
