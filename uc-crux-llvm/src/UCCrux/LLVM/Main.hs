{-
Module       : UCCrux.LLVM.Main
Description  : Main interface
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.Main
  ( mainWithOutputTo,
    mainWithOutputConfig,
    defaultOutputConfig,
    loopOnFunctions,
    translateLLVMModule,
    translateFile,
    SomeModuleContext' (..),
    Result.SomeBugfindingResult (..),
    Result.FunctionSummary (..),
    Result.printFunctionSummary,
    UCCruxLLVMLogging (..),
    ucCruxLLVMLoggingToSayWhat,
    withUCCruxLLVMLogging,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.))
import           Control.Monad (void)
import           Data.Aeson (ToJSON)
import           GHC.Generics (Generic)
import           System.Exit (ExitCode(..))
import           System.IO (Handle)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Some (Some(..))

-- crucible
import           Lang.Crucible.Simulator (GlobalVar)
import qualified Lang.Crucible.FunctionHandle as Crucible

-- crucible-llvm
import Lang.Crucible.LLVM.MemModel (Mem, mkMemVar, withPtrWidth)
import Lang.Crucible.LLVM.Translation
        ( translateModule
        , transContext
        , llvmPtrWidth)

-- crux
import qualified Crux
import qualified Crux.Log as Log
import Crux.Config.Common

-- local
import           Crux.LLVM.Config
import           Crux.LLVM.Compile (genBitCode)
import qualified Crux.LLVM.Log as Log
import           Crux.LLVM.Simulate (parseLLVM)

import           Paths_uc_crux_llvm (version)
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Config (UCCruxLLVMOptions)
import           UCCrux.LLVM.Context.Module (ModuleContext, SomeModuleContext(..), makeModuleContext, moduleTranslation)
import           UCCrux.LLVM.Equivalence (checkEquiv)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.Translation (ppTypeTranslationError)
import qualified UCCrux.LLVM.Logging as Log
import           UCCrux.LLVM.Run.Explore (explore)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Loop (loopOnFunctions)
{- ORMOLU_ENABLE -}

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h =
  mainWithOutputConfig $
    Crux.mkOutputConfig False h h ucCruxLLVMLoggingToSayWhat

defaultOutputConfig :: Maybe CruxOptions -> Log.OutputConfig UCCruxLLVMLogging
defaultOutputConfig opts = Crux.defaultOutputConfig ucCruxLLVMLoggingToSayWhat opts

data UCCruxLLVMLogging
  = LoggingCrux Log.CruxLogMessage
  | LoggingCruxLLVM Log.CruxLLVMLogMessage
  | LoggingUCCruxLLVM Log.UCCruxLLVMLogMessage
  deriving (Generic, ToJSON)

ucCruxLLVMLoggingToSayWhat :: UCCruxLLVMLogging -> Log.SayWhat
ucCruxLLVMLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
ucCruxLLVMLoggingToSayWhat (LoggingCruxLLVM msg) = Log.cruxLLVMLogMessageToSayWhat msg
ucCruxLLVMLoggingToSayWhat (LoggingUCCruxLLVM msg) = Log.ucCruxLLVMLogMessageToSayWhat msg

withUCCruxLLVMLogging ::
  ( ( Log.SupportsCruxLogMessage UCCruxLLVMLogging,
      Log.SupportsCruxLLVMLogMessage UCCruxLLVMLogging,
      Log.SupportsUCCruxLLVMLogMessage UCCruxLLVMLogging
    ) =>
    computation
  ) ->
  computation
withUCCruxLLVMLogging computation =
  let ?injectCruxLogMessage = LoggingCrux
      ?injectCruxLLVMLogMessage = LoggingCruxLLVM
      ?injectUCCruxLLVMLogMessage = LoggingUCCruxLLVM
   in computation

mainWithOutputConfig ::
  (Maybe CruxOptions -> Crux.OutputConfig UCCruxLLVMLogging) -> IO ExitCode
mainWithOutputConfig mkOutCfg =
  withUCCruxLLVMLogging $ do
    conf <- Config.ucCruxLLVMConfig
    Crux.loadOptions mkOutCfg "uc-crux-llvm" version conf $ \opts ->
      do
        (appCtx, cruxOpts, ucOpts) <- Config.processUCCruxLLVMOptions opts
        path <- genBitCode cruxOpts (Config.ucLLVMOptions ucOpts)
        halloc <- Crucible.newHandleAllocator
        memVar <- mkMemVar "uc-crux-llvm:llvm_memory" halloc
        SomeModuleContext' modCtx <- translateFile ucOpts halloc memVar path
        let checkEquivalenceWith = Config.crashEquivalence ucOpts
        if checkEquivalenceWith /= ""
          then do
            path' <-
              genBitCode
                (cruxOpts {inputFiles = [checkEquivalenceWith]})
                (Config.ucLLVMOptions ucOpts)
            memVar' <- mkMemVar "uc-crux-llvm:llvm_memory'" halloc
            SomeModuleContext' modCtx' <- translateFile ucOpts halloc memVar' path'
            void $ checkEquiv appCtx modCtx modCtx' halloc cruxOpts ucOpts
          else
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
                    \func (SomeBugfindingResult result _) ->
                      Log.sayUCCruxLLVM
                        ( Log.Results
                            (Text.pack func)
                            (Result.printFunctionSummary (summary result))
                        )
        return ExitSuccess

translateLLVMModule ::
  UCCruxLLVMOptions ->
  Crucible.HandleAllocator ->
  GlobalVar Mem ->
  FilePath ->
  L.Module ->
  IO SomeModuleContext'
translateLLVMModule ucOpts halloc memVar moduleFilePath llvmMod =
  do
    let llvmOpts = Config.ucLLVMOptions ucOpts
    Some trans <-
      let ?transOpts = transOpts llvmOpts
       in translateModule halloc memVar llvmMod
    llvmPtrWidth
      (trans ^. transContext)
      ( \ptrW ->
          withPtrWidth
            ptrW
            ( case makeModuleContext moduleFilePath llvmMod trans of
                Left err ->
                  panic
                    "translateLLVMModule"
                    [ "Type translation failed",
                      ppTypeTranslationError err
                    ]
                Right (SomeModuleContext modCtx) ->
                  pure (SomeModuleContext' modCtx)
            )
      )

data SomeModuleContext'
  = forall m arch. SomeModuleContext' (ModuleContext m arch)

translateFile ::
  UCCruxLLVMOptions ->
  Crucible.HandleAllocator ->
  GlobalVar Mem ->
  FilePath ->
  IO SomeModuleContext'
translateFile ucOpts halloc memVar moduleFilePath =
  translateLLVMModule ucOpts halloc memVar moduleFilePath =<< parseLLVM moduleFilePath
