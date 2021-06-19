{-
Module       : UCCrux.LLVM.Config
Description  : CLI, environment, and config file options
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE OverloadedStrings #-}

module UCCrux.LLVM.Config
  ( UCCruxLLVMOptions (..),
    ucCruxLLVMConfig,
    processUCCruxLLVMOptions,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Applicative ((<|>))
import           Control.Lens (Lens', lens)
import           Control.Monad (when)
import           Data.Word (Word64)
import           Data.Text (Text)
import qualified Data.Text as Text
import           System.Exit (die)

import qualified Crux.Config as Crux
import           Crux.Config.Common (CruxOptions, loopBound, recursionBound)
import           Crux.LLVM.Config (LLVMOptions, llvmCruxConfig)
import           CruxLLVMMain (processLLVMOptions)

import           UCCrux.LLVM.Logging (verbosityFromInt)
import           UCCrux.LLVM.Context.App (AppContext, makeAppContext)
{- ORMOLU_ENABLE -}

data UCCruxLLVMOptions = UCCruxLLVMOptions
  { ucLLVMOptions :: LLVMOptions,
    crashEquivalence :: FilePath,
    crashEquivalenceStrict :: Bool,
    doExplore :: Bool,
    reExplore :: Bool,
    exploreBudget :: Int,
    exploreTimeout :: Int,
    exploreParallel :: Bool,
    entryPoints :: [String],
    skipFunctions :: [String],
    verbosity :: Int
  }

ucCruxLLVMOptionsToLLVMOptions :: Lens' UCCruxLLVMOptions LLVMOptions
ucCruxLLVMOptionsToLLVMOptions = lens ucLLVMOptions (\uc llvm -> uc {ucLLVMOptions = llvm})

-- | Crucible will infinitely loop when it encounters unbounded program loops,
-- so we cap the iterations here if the user doesn't provide a bound explicitly.
suggestedLoopBound :: Word64
suggestedLoopBound = 8

suggestedRecursionBound :: Word64
suggestedRecursionBound = 8

processUCCruxLLVMOptions ::
  (CruxOptions, UCCruxLLVMOptions) -> IO (AppContext, CruxOptions, UCCruxLLVMOptions)
processUCCruxLLVMOptions (initCOpts, initUCOpts) =
  do
    let appCtx = makeAppContext (verbosityFromInt (verbosity initUCOpts))
    when (not (doExplore initUCOpts) && null (entryPoints initUCOpts)) $
      die "At least one entry point (--entry-points) is required (or try --explore)"
    (finalCOpts, finalLLOpts) <-
      processLLVMOptions
        ( initCOpts
            { loopBound = loopBound initCOpts <|> Just suggestedLoopBound,
              recursionBound = recursionBound initCOpts <|> Just suggestedRecursionBound
            },
          ucLLVMOptions initUCOpts
        )
    pure (appCtx, finalCOpts, initUCOpts {ucLLVMOptions = finalLLOpts})

crashEquivalenceDoc :: Text
crashEquivalenceDoc = "Check crash-equivalence with another LLVM bitcode module"

crashEquivalenceStrictDoc :: Text
crashEquivalenceStrictDoc = "Check for strict crash equivalence"

exploreDoc :: Text
exploreDoc = "Run in exploration mode"

reExploreDoc :: Text
reExploreDoc = "Re-explore functions that have already been explored (i.e., have logs)"

exploreBudgetDoc :: Text
exploreBudgetDoc = "Budget for exploration mode (number of functions)"

exploreTimeoutDoc :: Text
exploreTimeoutDoc = "Hard timeout for exploration of a single function (seconds)"

exploreParallelDoc :: Text
exploreParallelDoc = "Explore different functions in parallel"

entryPointsDoc :: Text
entryPointsDoc = "Comma-separated list of functions to examine."

skipDoc :: Text
skipDoc = "List of functions to skip during exploration"

verbDoc :: Text
verbDoc = "Verbosity of logging. (0: minimal, 1: informational, 2: debug)"

ucCruxLLVMConfig :: IO (Crux.Config UCCruxLLVMOptions)
ucCruxLLVMConfig = do
  llvmOpts <- llvmCruxConfig
  return
    Crux.Config
      { Crux.cfgFile =
          UCCruxLLVMOptions
            <$> Crux.cfgFile llvmOpts
            <*> Crux.section "crash-equivalence" Crux.fileSpec "" crashEquivalenceDoc
            <*> Crux.section "strict-crash-equivalence" Crux.yesOrNoSpec False crashEquivalenceStrictDoc
            <*> Crux.section "explore" Crux.yesOrNoSpec False exploreDoc
            <*> Crux.section "re-explore" Crux.yesOrNoSpec False reExploreDoc
            <*> Crux.section "explore-budget" Crux.numSpec 8 exploreBudgetDoc
            <*> Crux.section "explore-timeout" Crux.numSpec 5 exploreTimeoutDoc
            <*> Crux.section "explore-parallel" Crux.yesOrNoSpec False exploreParallelDoc
            <*> Crux.section "entry-points" (Crux.listSpec Crux.stringSpec) [] entryPointsDoc
            <*> Crux.section "skip-functions" (Crux.listSpec Crux.stringSpec) [] skipDoc
            <*> Crux.section "verbosity" Crux.numSpec 0 verbDoc,
        Crux.cfgEnv =
          Crux.liftEnvDescr ucCruxLLVMOptionsToLLVMOptions <$> Crux.cfgEnv llvmOpts,
        Crux.cfgCmdLineFlag =
          (Crux.liftOptDescr ucCruxLLVMOptionsToLLVMOptions <$> Crux.cfgCmdLineFlag llvmOpts)
            ++ [ Crux.Option
                   []
                   ["crash-equivalence"]
                   (Text.unpack crashEquivalenceDoc)
                   $ Crux.ReqArg "LLVMMODULE" $
                     \v opts -> Right opts {crashEquivalence = v},
                 Crux.Option
                   []
                   ["strict-crash-equivalence"]
                   (Text.unpack crashEquivalenceStrictDoc)
                   $ Crux.NoArg $
                     \opts -> Right opts {crashEquivalenceStrict = True},
                 Crux.Option
                   []
                   ["explore"]
                   (Text.unpack exploreDoc)
                   $ Crux.NoArg $
                     \opts -> Right opts {doExplore = True},
                 Crux.Option
                   []
                   ["re-explore"]
                   (Text.unpack reExploreDoc)
                   $ Crux.NoArg $
                     \opts -> Right opts {reExplore = True},
                 Crux.Option
                   []
                   ["explore-budget"]
                   (Text.unpack exploreBudgetDoc)
                   $ Crux.ReqArg
                     "INT"
                     $ Crux.parsePosNum
                       "INT"
                       $ \v opts -> opts {exploreBudget = v},
                 Crux.Option
                   []
                   ["explore-timeout"]
                   (Text.unpack exploreTimeoutDoc)
                   $ Crux.ReqArg
                     "INT"
                     $ Crux.parsePosNum
                       "INT"
                       $ \v opts -> opts {exploreTimeout = v},
                 Crux.Option
                   []
                   ["explore-parallel"]
                   (Text.unpack exploreParallelDoc)
                   $ Crux.NoArg $
                     \opts -> Right opts {exploreParallel = True},
                 Crux.Option
                   []
                   ["entry-points"]
                   (Text.unpack entryPointsDoc)
                   $ Crux.ReqArg "FUN" $
                     \v opts -> Right opts {entryPoints = v : entryPoints opts},
                 Crux.Option
                   []
                   ["skip-functions"]
                   (Text.unpack skipDoc)
                   $ Crux.ReqArg "FUN" $
                     \v opts -> Right opts {skipFunctions = v : skipFunctions opts},
                 Crux.Option
                   ['v']
                   ["verbosity"]
                   (Text.unpack verbDoc)
                   $ Crux.ReqArg "LEVEL" $
                     Crux.parsePosNum
                       "LEVEL"
                       $ \v opts ->
                         opts {verbosity = v}
               ]
      }
