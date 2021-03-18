{-
Module       : UCCrux.LLVM.Run.Explore
Description  : Explore a program
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module UCCrux.LLVM.Run.Explore
  ( explore,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log, writeFile)

import           Control.Exception (displayException)
import           Control.Lens ((^.))
import qualified Data.Map.Strict as Map
import           Data.Traversable (for)
import           Data.Text.IO (writeFile)
import qualified Data.Text as Text
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
import Crux.Log (OutputConfig(..))

 -- crux-llvm
import Crux.LLVM.Overrides (ArchOk)

import           UCCrux.LLVM.Config (UCCruxLLVMOptions)
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Module (ModuleContext, llvmModule, moduleFilePath)
import           UCCrux.LLVM.Logging (Verbosity(Low, Med, Hi))
import           UCCrux.LLVM.Run.Result (SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Loop (loopOnFunction)
import           UCCrux.LLVM.Stats (Stats(unimplementedFreq), getStats, ppStats)
{- ORMOLU_ENABLE -}

-- | Explore arbitrary functions in this module, trying to find some bugs.
--
-- The strategy/order is exceedingly naive right now, it literally just applies
-- @take@ to the list of 'L.Define' in the module and explores those functions.
explore ::
  ( ?outputConfig :: OutputConfig,
    ArchOk arch
  ) =>
  AppContext ->
  ModuleContext arch ->
  CruxOptions ->
  UCCruxLLVMOptions ->
  Crucible.HandleAllocator ->
  IO ()
explore appCtx modCtx cruxOpts ucOpts halloc =
  do
    (appCtx ^. log) Hi $ "Exploring with budget: " <> Text.pack (show (Config.exploreBudget ucOpts))
    -- TODO choose randomly
    let ppShow = PP.renderStrict . PP.layoutPretty PP.defaultLayoutOptions
    let functions =
          map
            ((\(L.Symbol f) -> f) . L.defName)
            (take (Config.exploreBudget ucOpts) (L.modDefines (modCtx ^. llvmModule)))
    let dir = bldDir cruxOpts </> takeFileName (modCtx ^. moduleFilePath) -<.> ""
    createDirectoryIfMissing True dir
    stats <-
      for (filter (`notElem` Config.skipFunctions ucOpts) functions) $
        \func ->
          do
            let logFilePath = dir </> func -<.> ".summary.log"
            logExists <- doesPathExist logFilePath
            if not logExists || Config.reExplore ucOpts
              then do
                (appCtx ^. log) Hi $ "Exploring " <> Text.pack func
                maybeResult <- loopOnFunction appCtx modCtx halloc cruxOpts ucOpts func
                case maybeResult of
                  Right (SomeBugfindingResult result) ->
                    do
                      writeFile logFilePath (Result.printFunctionSummary (Result.summary result))
                      pure (getStats result)
                  Left unin ->
                    do
                      writeFile logFilePath (Text.pack (displayException unin))
                      pure
                        ( mempty
                            { unimplementedFreq = Map.singleton (panicComponent unin) 1
                            }
                        )
              else do
                (appCtx ^. log) Med $ "Skipping already-explored function " <> Text.pack func
                pure mempty
    (appCtx ^. log) Low $ ppShow (ppStats (mconcat stats))
