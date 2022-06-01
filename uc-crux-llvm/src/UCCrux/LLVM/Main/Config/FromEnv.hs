{-
Module       : UCCrux.LLVM.Config.FromEnv
Description  : Grab configuration from CLI, environment variables, and config file
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

The functions/types in this module aren't necessarily appropriate for using
UC-Crux-LLVM as a library: Some of them are impure, and they can throw
exceptions. Moreover, 'UCCruxLLVMOptions' is a monolithic datatype that combines
configuration options for a wide variety of functionality, which is probably
unnecessary for most library use-cases. Moreover, these functions/types aren't
needed (or used) by the rest of the library outside of the "UCCrux.LLVM.Main"
module.
-}
{-# LANGUAGE OverloadedStrings #-}

module UCCrux.LLVM.Main.Config.FromEnv
  ( UCCruxLLVMOptions (..),
    ucCruxLLVMConfig,
    processUCCruxLLVMOptions,
  )
where

{- ORMOLU_DISABLE -}
import           Control.Applicative ((<|>))
import           Control.Lens (Lens', lens)
import           Control.Monad (when)
import           Data.List.NonEmpty (NonEmpty, nonEmpty)
import           Data.Word (Word64)
import           Data.Text (Text)
import qualified Data.Text as Text
import           System.Exit (die)

import qualified Crux.Config as Crux
import           Crux.Config.Common (CruxOptions, loopBound, recursionBound)
import           Crux.LLVM.Config (LLVMOptions, llvmCruxConfig)
import           CruxLLVMMain (processLLVMOptions)

import           UCCrux.LLVM.Context.App (AppContext, makeAppContext)
import qualified UCCrux.LLVM.Equivalence.Config as EqConfig
import qualified UCCrux.LLVM.Run.Explore.Config as ExConfig
import           UCCrux.LLVM.Logging (verbosityFromInt)
import           UCCrux.LLVM.Main.Config.Type (TopLevelConfig)
import qualified UCCrux.LLVM.Main.Config.Type as Config
import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName, functionNameFromString)
import           UCCrux.LLVM.Newtypes.Seconds (Seconds, secondsFromInt)
{- ORMOLU_ENABLE -}

-- | Options as obtained from the Crux command-line and config file machinery.
--
-- Processed into a 'TopLevelConfig'.
data UCCruxLLVMOptions = UCCruxLLVMOptions
  { ucLLVMOptions :: LLVMOptions,
    checkFrom :: [FunctionName],
    checkFromCallers :: Bool,
    crashOrder :: FilePath,
    crashEquivalence :: Bool,
    doExplore :: Bool,
    reExplore :: Bool,
    exploreBudget :: Int,
    exploreTimeout :: Seconds,
    exploreParallel :: Bool,
    entryPoints :: [FunctionName],
    skipFunctions :: [FunctionName],
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

-- | Parse (as in \"parse, don\'t validate\") options gathered by Crux
-- ('UCCruxLLVMOptions') into an 'AppContext' and a 'TopLevelConfig'.
processUCCruxLLVMOptions ::
  (CruxOptions, UCCruxLLVMOptions) -> IO (AppContext, CruxOptions, TopLevelConfig)
processUCCruxLLVMOptions (initCOpts, initUCOpts) =
  do
    let appCtx = makeAppContext (verbosityFromInt (verbosity initUCOpts))
    let doCrashOrder = crashOrder initUCOpts /= ""

    -- Figure out the entry points. If exploration mode is selected, the
    -- specified entry points are irrelevant. If crash ordering is selected,
    -- then entry points may or may not be specified. If neither is selected,
    -- then entry points must be provided.
    let makeEntries :: UCCruxLLVMOptions -> IO (Maybe (NonEmpty FunctionName))
        makeEntries uco
          | doExplore uco = pure Nothing
          | crashOrder uco /= "" = pure (nonEmpty (entryPoints uco))
          | otherwise =
              Just <$>
                maybe
                  (die
                    (unwords
                      [ "At least one entry point (--entry-points) is required",
                        "(or try --explore or --crash-order)"
                      ]))
                  pure
                  (nonEmpty (entryPoints uco))

    entries <- makeEntries initUCOpts

    when (doExplore initUCOpts && doCrashOrder) $
      die "Can't specify both --explore and --crash-order"
    (finalCOpts, finalLLOpts) <-
      processLLVMOptions
        ( initCOpts
            { loopBound = loopBound initCOpts <|> Just suggestedLoopBound,
              recursionBound = recursionBound initCOpts <|> Just suggestedRecursionBound
            },
          ucLLVMOptions initUCOpts
        )

    let topConf =
          Config.TopLevelConfig
            { Config.ucLLVMOptions = finalLLOpts,
              Config.runConfig =
                case entries of
                  Just ents ->
                    Config.Analyze $
                      Config.AnalyzeConfig
                        { Config.entryPoints = ents
                        , Config.checkFrom = checkFrom initUCOpts
                        , Config.checkFromCallers = checkFromCallers initUCOpts
                        }
                  Nothing ->
                    if doExplore initUCOpts
                    then
                      Config.Explore
                        (ExConfig.ExploreConfig
                          { ExConfig.exploreAgain = reExplore initUCOpts,
                            ExConfig.exploreBudget = exploreBudget initUCOpts,
                            ExConfig.exploreTimeout = exploreTimeout initUCOpts,
                            ExConfig.exploreParallel = exploreParallel initUCOpts,
                            ExConfig.exploreSkipFunctions = skipFunctions initUCOpts
                          })
                    else
                      Config.CrashEquivalence
                        (EqConfig.EquivalenceConfig
                          { EqConfig.equivOrOrder =
                              if crashEquivalence initUCOpts
                              then EqConfig.Equivalence
                              else EqConfig.Order,
                            EqConfig.equivModule = crashOrder initUCOpts,
                            EqConfig.equivEntryPoints = entryPoints initUCOpts
                          })
            }

    return (appCtx, finalCOpts, topConf)

checkFromDoc :: Text
checkFromDoc = "Check inferred contracts by symbolically executing from this function"

checkFromCallersDoc :: Text
checkFromCallersDoc = "Check inferred contracts by symbolically executing from callers"

crashOrderDoc :: Text
crashOrderDoc = "Check crash-ordering with another LLVM bitcode module"

crashEquivalenceDoc :: Text
crashEquivalenceDoc = "Check for crash equivalence, rather than just ordering"

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
            <*>
              (map functionNameFromString <$>
                Crux.section "check-from" (Crux.listSpec Crux.stringSpec) [] checkFromDoc)
            <*> Crux.section "check-from-callers" Crux.yesOrNoSpec False checkFromDoc
            <*> Crux.section "crash-order" Crux.fileSpec "" crashOrderDoc
            <*> Crux.section "crash-equivalence" Crux.yesOrNoSpec False crashEquivalenceDoc
            <*> Crux.section "explore" Crux.yesOrNoSpec False exploreDoc
            <*> Crux.section "re-explore" Crux.yesOrNoSpec False reExploreDoc
            <*> Crux.section "explore-budget" Crux.numSpec 8 exploreBudgetDoc
            <*>
              (secondsFromInt <$>
                Crux.section "explore-timeout" Crux.numSpec 5 exploreTimeoutDoc)
            <*> Crux.section "explore-parallel" Crux.yesOrNoSpec False exploreParallelDoc
            <*>
              (map functionNameFromString <$>
                Crux.section "entry-points" (Crux.listSpec Crux.stringSpec) [] entryPointsDoc)
            <*>
              (map functionNameFromString <$>
                Crux.section "skip-functions" (Crux.listSpec Crux.stringSpec) [] skipDoc)
            <*> Crux.section "verbosity" Crux.numSpec 0 verbDoc,
        Crux.cfgEnv =
          Crux.liftEnvDescr ucCruxLLVMOptionsToLLVMOptions <$> Crux.cfgEnv llvmOpts,
        Crux.cfgCmdLineFlag =
          (Crux.liftOptDescr ucCruxLLVMOptionsToLLVMOptions <$> Crux.cfgCmdLineFlag llvmOpts)
            ++ [ Crux.Option
                   []
                   ["check-from"]
                   (Text.unpack checkFromDoc)
                   $ Crux.ReqArg "FUN" $
                     \v opts ->
                       Right
                         opts
                         { checkFrom =
                            functionNameFromString v : checkFrom opts
                         },
                 Crux.Option
                   []
                   ["check-from-callers"]
                   (Text.unpack checkFromCallersDoc)
                   $ Crux.NoArg $
                     \opts -> Right opts {checkFromCallers = True},
                 Crux.Option
                   []
                   ["crash-order"]
                   (Text.unpack crashOrderDoc)
                   $ Crux.ReqArg "LLVMMODULE" $
                     \v opts -> Right opts {crashOrder = v},
                 Crux.Option
                   []
                   ["crash-equivalence"]
                   (Text.unpack crashEquivalenceDoc)
                   $ Crux.NoArg $
                     \opts -> Right opts {crashEquivalence = True},
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
                     \v opts ->
                       Right
                         opts
                         { entryPoints =
                            functionNameFromString v : entryPoints opts
                         },
                 Crux.Option
                   []
                   ["skip-functions"]
                   (Text.unpack skipDoc)
                   $ Crux.ReqArg "FUN" $
                     \v opts ->
                       Right
                         opts
                         { skipFunctions =
                             functionNameFromString v : skipFunctions opts
                         },
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
