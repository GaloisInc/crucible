{-
Module       : UCCrux.LLVM.Main
Description  : Main interface
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module UCCrux.LLVM.Main
  ( mainWithOutputTo,
    mainWithOutputConfig,
    defaultOutputConfig,
    loopOnFunctions,
    translate,
    Result.SomeBugfindingResult (..),
    Result.FunctionSummary (..),
    Result.printFunctionSummary,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Exception (throw)
import           Control.Lens ((^.))
import           Control.Monad (void)
import           Data.Traversable (for)
import           System.Exit (ExitCode(..))
import           System.IO (Handle)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

import           Data.Parameterized.Some (Some(..))

-- crucible
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crucible-llvm
import Lang.Crucible.LLVM.MemModel (withPtrWidth)
import Lang.Crucible.LLVM.Translation
        ( translateModule
        , transContext
        , llvmPtrWidth)

-- crux
import qualified Crux

import Crux.Config.Common
import Crux.Log (say, OutputConfig(..), defaultOutputConfig)

 -- local
import Crux.LLVM.Config
import Crux.LLVM.Compile (genBitCode)
import Crux.LLVM.Simulate (parseLLVM)

import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Config (UCCruxLLVMOptions)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, makeModuleContext, moduleTranslation)
import           UCCrux.LLVM.Run.Explore (explore)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Loop (loopOnFunction)
{- ORMOLU_ENABLE -}

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig (OutputConfig False h h False)

mainWithOutputConfig :: OutputConfig -> IO ExitCode
mainWithOutputConfig outCfg =
  do
    conf <- Config.ucCruxLLVMConfig
    Crux.loadOptions outCfg "uc-crux-llvm" "0.1" conf $ \opts ->
      do
        (appCtx, cruxOpts, ucOpts) <- Config.processUCCruxLLVMOptions opts
        path <- genBitCode cruxOpts (Config.ucLLVMOptions ucOpts)
        halloc <- Crucible.newHandleAllocator
        Some modCtx <- translate ucOpts halloc path
        if Config.doExplore ucOpts
          then do
            llvmPtrWidth
              (modCtx ^. moduleTranslation . transContext)
              ( \ptrW ->
                  withPtrWidth
                    ptrW
                    ( explore
                        appCtx
                        modCtx
                        cruxOpts
                        ucOpts
                        halloc
                    )
              )
          else do
            results <- loopOnFunctions appCtx modCtx halloc cruxOpts ucOpts
            void $
              flip Map.traverseWithKey results $
                \func (SomeBugfindingResult result) ->
                  do
                    say "Crux" ("Results for " <> func)
                    say "Crux" $ Text.unpack (Result.printFunctionSummary (summary result))
        return ExitSuccess

translate ::
  UCCruxLLVMOptions ->
  Crucible.HandleAllocator ->
  FilePath ->
  IO (Some ModuleContext)
translate ucOpts halloc moduleFilePath =
  do
    llvmMod <- parseLLVM moduleFilePath
    let llvmOpts = Config.ucLLVMOptions ucOpts
    Some trans <-
      let ?laxArith = laxArithmetic llvmOpts
          ?optLoopMerge = loopMerge llvmOpts
       in translateModule halloc llvmMod
    pure $ Some (makeModuleContext moduleFilePath llvmMod trans)

-- | Postcondition: The keys of the returned map are exactly the entryPoints of
-- the 'UCCruxLLVMOptions'.
loopOnFunctions ::
  (?outputConfig :: OutputConfig) =>
  AppContext ->
  ModuleContext arch ->
  Crucible.HandleAllocator ->
  CruxOptions ->
  UCCruxLLVMOptions ->
  IO (Map.Map String SomeBugfindingResult)
loopOnFunctions appCtx modCtx halloc cruxOpts ucOpts =
  Map.fromList
    <$> llvmPtrWidth
      (modCtx ^. moduleTranslation . transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( for (Config.entryPoints ucOpts) $
                \entry ->
                  (entry,) . either throw id
                    <$> loopOnFunction appCtx modCtx halloc cruxOpts ucOpts entry
            )
      )
