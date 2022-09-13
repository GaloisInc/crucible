{-
Module       : UCCrux.LLVM.Run.Explore
Description  : Explore a program
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module UCCrux.LLVM.Run.Explore
  ( explore,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log, writeFile)

import           Control.Lens ((.~), (^.), to)
import           Control.Concurrent (threadDelay)
import           Control.Concurrent.Async (race)
import           Control.Scheduler (Comp(Par), traverseConcurrently)
import           Control.Exception (displayException)
import           Data.Function ((&))
import           Data.Map (Map)
import           Data.Text.IO (writeFile)
import qualified Data.Text as Text
import           Data.Traversable (for)
import           Panic (panicComponent)
import           System.Directory (doesPathExist, createDirectoryIfMissing)
import           System.FilePath ((</>), (-<.>), takeFileName)

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

import qualified Text.LLVM.AST as L

-- crucible
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crux
import Crux.Config.Common (CruxOptions, bldDir)
import Crux.Log as Crux

 -- crux-llvm
import Crux.LLVM.Config (LLVMOptions)
import Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Newtypes.FunctionName (functionNameToString)
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleFilePath, defnTypes)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Module (DefnSymbol, getDefnSymbol, makeDefnSymbol, getModule, FuncSymbol)
import           UCCrux.LLVM.Logging (Verbosity(Low, Med, Hi))
import           UCCrux.LLVM.Newtypes.Seconds (secondsToMicroseconds)
import           UCCrux.LLVM.Run.Explore.Config (ExploreConfig)
import qualified UCCrux.LLVM.Run.Explore.Config as ExConfig
import           UCCrux.LLVM.Run.Result (SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Loop (loopOnFunction)
import           UCCrux.LLVM.Specs.Type (SomeSpecs)
import           UCCrux.LLVM.Stats (Stats(unimplementedFreq), getStats, ppStats)
import qualified UCCrux.LLVM.Stats.Freq as Freq
{- ORMOLU_ENABLE -}

withTimeout :: Int -> IO a -> IO (Either () a)
withTimeout timeout action = race (threadDelay timeout) action

exploreOne ::
  ArchOk arch =>
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  CruxOptions ->
  LLVMOptions ->
  ExploreConfig ->
  Crucible.HandleAllocator ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  FilePath ->
  DefnSymbol m ->
  IO Stats
exploreOne appCtx modCtx cruxOpts llOpts exOpts halloc specs dir defnSym =
  do
    let L.Symbol func = getDefnSymbol defnSym
    let logFilePath = dir </> func -<.> ".summary.log"
    logExists <- doesPathExist logFilePath
    if -- If a log exists, then this function has already been
       -- explored/simulated. Don't explore it again unless the user/client
       -- specifically requests it. This is useful when exploring a large
       -- program bit-by-bit.
       not logExists || ExConfig.exploreAgain exOpts
      then do
        (appCtx ^. log) Hi $ "Exploring " <> Text.pack func
        maybeResult <-
          withTimeout
            (secondsToMicroseconds (ExConfig.exploreTimeout exOpts))
            (loopOnFunction appCtx modCtx halloc cruxOpts llOpts specs defnSym)
        case maybeResult of
          Right (Right (SomeBugfindingResult _types result _trace)) ->
            do
              writeFile logFilePath (Result.printFunctionSummary (Result.summary result))
              pure (getStats result)
          Right (Left unin) ->
            do
              (appCtx ^. log) Hi $ "Hit unimplemented feature in " <> Text.pack func
              writeFile logFilePath (Text.pack (displayException unin))
              pure
                ( mempty
                    { unimplementedFreq = Freq.singleton (panicComponent unin)
                    }
                )
          Left () ->
            do
              (appCtx ^. log) Hi $ "Hit timeout in " <> Text.pack func
              writeFile logFilePath (Text.pack "Timeout - likely solver or Crucible bug")
              pure mempty -- TODO Record timeout
      else do
        (appCtx ^. log) Med $ "Skipping already-explored function " <> Text.pack func
        pure mempty

-- | Explore arbitrary functions in this module, trying to find some bugs.
--
-- The strategy/order is exceedingly naive right now, it literally just applies
-- @take@ to the list of 'L.Define' in the module and explores those functions.
explore ::
  ArchOk arch =>
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  AppContext ->
  ModuleContext m arch ->
  CruxOptions ->
  LLVMOptions ->
  ExploreConfig ->
  Crucible.HandleAllocator ->
  -- | Specifications for (usually external) functions
  Map (FuncSymbol m) (SomeSpecs m) ->
  IO ()
explore appCtx modCtx cruxOpts llOpts exOpts halloc specs =
  do
    (appCtx ^. log) Hi $ "Exploring with budget: " <> Text.pack (show (ExConfig.exploreBudget exOpts))
    -- TODO choose randomly
    let ppShow = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
    let functions =
          map
            ((\(L.Symbol f) -> f) . L.defName)
            (take
              (ExConfig.exploreBudget exOpts)
              (L.modDefines (modCtx ^. llvmModule . to getModule)))
    let dir = bldDir cruxOpts </> takeFileName (modCtx ^. moduleFilePath) -<.> ""
    createDirectoryIfMissing True dir
    let toSkip = map functionNameToString (ExConfig.exploreSkipFunctions exOpts)
    let funcsToExplore = filter (`notElem` toSkip) functions
    let defnsToExplore =
          map
            (\func ->
                case makeDefnSymbol (L.Symbol func) (modCtx ^. defnTypes) of
                  Just symb -> symb
                  Nothing ->
                    -- NB: This can't happen because this function name was
                    -- taken from the modDefines of this same modCtx just above.
                    panic "explore" ["Function not found in module :" ++ func])
            funcsToExplore
    let doExplore ac = exploreOne ac modCtx cruxOpts llOpts exOpts halloc specs dir
    stats <-
      if ExConfig.exploreParallel exOpts
        then
          traverseConcurrently
            Par
            -- Disable logging during parallel exploration
            (doExplore (appCtx & log .~ (\_ _ -> pure ())))
            defnsToExplore
        else for defnsToExplore (doExplore appCtx)
    (appCtx ^. log) Low $ ppShow (ppStats (mconcat stats))
