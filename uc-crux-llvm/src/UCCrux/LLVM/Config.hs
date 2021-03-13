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
import           Control.Monad (when)
import           Data.Functor ((<&>))

import qualified Crux.Config as Crux
import           Crux.Config.Common (CruxOptions, loopBound, recursionBound)
import           Crux.LLVM.Config (LLVMOptions, llvmCruxConfig)
import           CruxLLVMMain (processLLVMOptions)

import           UCCrux.LLVM.Logging (verbosityFromInt)
import           UCCrux.LLVM.Context.App (AppContext, makeAppContext)
{- ORMOLU_ENABLE -}

data UCCruxLLVMOptions = UCCruxLLVMOptions
  { ucLLVMOptions :: LLVMOptions,
    doExplore :: Bool,
    reExplore :: Bool,
    entryPoints :: [String],
    exploreBudget :: Int,
    skipFunctions :: [String],
    verbosity :: Int
  }

processUCCruxLLVMOptions ::
  (CruxOptions, UCCruxLLVMOptions) -> IO (AppContext, CruxOptions, UCCruxLLVMOptions)
processUCCruxLLVMOptions (initCOpts, initUCOpts) =
  do
    let appCtx = makeAppContext (verbosityFromInt (verbosity initUCOpts))
    when (not (doExplore initUCOpts) && null (entryPoints initUCOpts)) $
      fail "At least one entry point (--entry-points) is required (or try --explore)"
    (finalCOpts, finalLLOpts) <-
      processLLVMOptions
        ( initCOpts
            { loopBound = loopBound initCOpts <|> Just 8,
              recursionBound = recursionBound initCOpts <|> Just 8
            },
          ucLLVMOptions initUCOpts
        )
    pure (appCtx, finalCOpts, initUCOpts {ucLLVMOptions = finalLLOpts})

ucCruxLLVMConfig :: IO (Crux.Config UCCruxLLVMOptions)
ucCruxLLVMConfig = do
  llvmOpts <- llvmCruxConfig
  return
    Crux.Config
      { Crux.cfgFile =
          UCCruxLLVMOptions
            <$> Crux.cfgFile llvmOpts
            <*> Crux.section
              "explore"
              Crux.yesOrNoSpec
              False
              "Run in exploration mode"
            <*> Crux.section
              "re-explore"
              Crux.yesOrNoSpec
              False
              "Re-explore functions that have already been explored (i.e., have logs)"
            <*> Crux.section
              "entry-points"
              (Crux.listSpec Crux.stringSpec)
              []
              "Comma-separated list of functions to examine."
            <*> Crux.section
              "explore-budget"
              Crux.numSpec
              8
              "Budget for exploration mode"
            <*> Crux.section
              "skip-functions"
              (Crux.listSpec Crux.stringSpec)
              []
              "List of functions to skip during exploration"
            <*> Crux.section
              "verbosity"
              Crux.numSpec
              0
              "Verbosity of logging. (0: minimal, 1: informational, 2: debug)",
        Crux.cfgEnv =
          map
            ( \envDescr ->
                envDescr
                  { Crux.evValue =
                      \v opts ->
                        Crux.evValue envDescr v (ucLLVMOptions opts)
                          <&> \llOpts -> opts {ucLLVMOptions = llOpts}
                  }
            )
            (Crux.cfgEnv llvmOpts)
            ++ [],
        Crux.cfgCmdLineFlag =
          map
            ( \optDescr ->
                optDescr
                  { Crux.optArgument =
                      case Crux.optArgument optDescr of
                        Crux.NoArg setter ->
                          Crux.NoArg $
                            \opts ->
                              setter (ucLLVMOptions opts)
                                <&> \llOpts -> opts {ucLLVMOptions = llOpts}
                        Crux.ReqArg desc setter ->
                          Crux.ReqArg desc $
                            \v opts ->
                              setter v (ucLLVMOptions opts)
                                <&> \llOpts -> opts {ucLLVMOptions = llOpts}
                        Crux.OptArg desc setter ->
                          Crux.OptArg desc $
                            \v opts ->
                              setter v (ucLLVMOptions opts)
                                <&> \llOpts -> opts {ucLLVMOptions = llOpts}
                  }
            )
            (Crux.cfgCmdLineFlag llvmOpts)
            ++ [ Crux.Option
                   []
                   ["entry-points"]
                   "List of functions to examine."
                   $ Crux.ReqArg "FUN" $
                     \v opts -> Right opts {entryPoints = v : entryPoints opts},
                 Crux.Option
                   ['v']
                   ["verbosity"]
                   "Verbosity of logging. (0: minimal, 1: informational, 2: debug)"
                   $ Crux.ReqArg "LEVEL" $
                     Crux.parsePosNum
                       "LEVEL"
                       $ \v opts ->
                         opts {verbosity = v},
                 Crux.Option
                   []
                   ["explore-budget"]
                   "Budget for exploration mode"
                   $ Crux.ReqArg
                     "INT"
                     $ Crux.parsePosNum
                       "INT"
                       $ \v opts -> opts {exploreBudget = v},
                 Crux.Option
                   []
                   ["skip-functions"]
                   "List of functions to skip during exploration"
                   $ Crux.ReqArg "FUN" $
                     \v opts -> Right opts {skipFunctions = v : skipFunctions opts},
                 Crux.Option
                   []
                   ["explore"]
                   "Run in exploration mode"
                   $ Crux.NoArg $
                     \opts -> Right opts {doExplore = True},
                 Crux.Option
                   []
                   ["re-explore"]
                   "Re-explore functions that have already been explored (i.e., have logs)"
                   $ Crux.NoArg $
                     \opts -> Right opts {reExplore = True}
               ]
      }
