{-
Module       : UCCrux.LLVM.Config.Type
Description  : Top-level configuration for UC-Crux-LLVM
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

The data types in this module are constructed from CLI/configuration files
passed to the UC-Crux-LLVM CLI. The idea is to "parse, not validate" from the
CLI options to these types. The documentation on these types refers to the
CLI/config options from which they are derived, see
"UCCrux.LLVM.Main.Config.FromEnv" (or run UC-Crux-LLVM with @--help@) for
descriptions of their intended effects, which are implemented in
"UCCrux.LLVM.Main".

The functions/types in this module aren't necessarily appropriate for using
UC-Crux-LLVM as a library: 'TopLevelConfig' selects among a wide variety of
functionality, a choice that is likely statically known for most library
use-cases. Moreover, these functions/types aren't needed (or used) by the rest
of the library outside of the "UCCrux.LLVM.Main" module.
-}

module UCCrux.LLVM.Main.Config.Type
  ( AnalyzeConfig(..),
    RunConfig (..),
    TopLevelConfig (..),
  )
where

import           Data.List.NonEmpty (NonEmpty)
import           Data.Map (Map)

import           Crux.LLVM.Config (LLVMOptions)

import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName)
import qualified UCCrux.LLVM.Equivalence.Config as EqConfig
import qualified UCCrux.LLVM.Run.Explore.Config as ExConfig
import           UCCrux.LLVM.View.Specs (SpecsView)

data AnalyzeConfig
  = AnalyzeConfig
      { -- | @--entry-points@
        entryPoints :: NonEmpty FunctionName
        -- | @--check-from@
      , checkFrom :: [FunctionName]
        -- | @--check-from-callers@
      , checkFromCallers :: Bool
        -- | @--specs-path@
      , specs :: Map FunctionName SpecsView
      }
  deriving (Eq, Ord, Show)

data RunConfig
  = -- | @--explore@
    Explore ExConfig.ExploreConfig
    -- | No corresponding CLI option, occurs when @--explore@ and
    -- @--crash-equivalence@ are not used.
  | Analyze AnalyzeConfig
    -- | @--crash-equivalence@
  | CrashEquivalence EqConfig.EquivalenceConfig
  deriving (Eq, Ord, Show)

data TopLevelConfig = TopLevelConfig
  { ucLLVMOptions :: LLVMOptions,
    runConfig :: RunConfig
  }
