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
import           Control.Monad (forM_, void)
import           Data.Aeson (ToJSON)
import           Data.Foldable (for_)
import qualified Data.List.NonEmpty as NonEmpty
import           GHC.Generics (Generic)
import           System.Exit (ExitCode(..))
import           System.IO (Handle)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO

import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PP

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
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, SomeModuleContext(..), makeModuleContext, defnTypes, withModulePtrWidth)
import           UCCrux.LLVM.Equivalence (checkEquiv)
import qualified UCCrux.LLVM.Equivalence.Config as EqConfig
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.Translation (ppTypeTranslationError)
import qualified UCCrux.LLVM.Logging as Log
import qualified UCCrux.LLVM.Main.Config.FromEnv as Config.FromEnv
import           UCCrux.LLVM.Main.Config.Type (TopLevelConfig)
import qualified UCCrux.LLVM.Main.Config.Type as Config
import           UCCrux.LLVM.Module (defnSymbolToString)
import           UCCrux.LLVM.Run.Check (inferThenCheck, ppSomeCheckResult)
import           UCCrux.LLVM.Run.EntryPoints (makeEntryPointsOrThrow)
import           UCCrux.LLVM.Run.Explore (explore)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Loop (loopOnFunctions)
{- ORMOLU_ENABLE -}

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h =
  mainWithOutputConfig $
    Crux.mkOutputConfig (h, False) (h, False) ucCruxLLVMLoggingToSayWhat

defaultOutputConfig :: IO (Maybe OutputOptions -> Log.OutputConfig UCCruxLLVMLogging)
defaultOutputConfig = Crux.defaultOutputConfig ucCruxLLVMLoggingToSayWhat

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

-- | Gather configuration options from the environment and pass them to
-- 'mainWithConfigs'.
mainWithOutputConfig ::
  (Maybe OutputOptions -> Crux.OutputConfig UCCruxLLVMLogging) -> IO ExitCode
mainWithOutputConfig mkOutCfg =
  do conf <- Config.FromEnv.ucCruxLLVMConfig
     withUCCruxLLVMLogging $
       Crux.loadOptions mkOutCfg "uc-crux-llvm" version conf $ \opts ->
         do (appCtx, cruxOpts, topConf) <-
              Config.FromEnv.processUCCruxLLVMOptions opts
            mainWithConfigs appCtx cruxOpts topConf

mainWithConfigs ::
  Crux.Logs msgs =>
  Crux.SupportsCruxLogMessage msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  Log.SupportsUCCruxLLVMLogMessage msgs =>
  AppContext ->
  CruxOptions ->
  TopLevelConfig ->
  IO ExitCode
mainWithConfigs appCtx cruxOpts topConf =
  do
    let llOpts = Config.ucLLVMOptions topConf
    path <- genBitCode cruxOpts llOpts
    halloc <- Crucible.newHandleAllocator
    memVar <- mkMemVar "uc-crux-llvm:llvm_memory" halloc
    SomeModuleContext' modCtx <- translateFile llOpts halloc memVar path
    case Config.runConfig topConf of
      Config.Explore exConfig ->
        withModulePtrWidth
          modCtx
          (explore appCtx modCtx cruxOpts llOpts exConfig halloc)
      Config.RunOn ents checkFrom ->
        do entries <-
             makeEntryPointsOrThrow
               (modCtx ^. defnTypes)
               (NonEmpty.toList ents)
           let printResult results =
                 forM_ (Map.toList results) $
                   \(func, SomeBugfindingResult _types result _trace) ->
                     Log.sayUCCruxLLVM
                       ( Log.Results
                           (Text.pack (defnSymbolToString func))
                           (Result.printFunctionSummary (summary result))
                       )
           case checkFrom of
             [] ->
               printResult =<<
                 loopOnFunctions appCtx modCtx halloc cruxOpts llOpts entries
             _ ->
               withModulePtrWidth
                 modCtx
                 ( do checkFromEntries <-
                        makeEntryPointsOrThrow
                          (modCtx ^. defnTypes)
                          checkFrom
                      (result, checkResult) <-
                        inferThenCheck appCtx modCtx halloc cruxOpts llOpts entries checkFromEntries
                      printResult result
                      for_ (Map.toList checkResult) $
                        \(checkedFunc, checkedResult) ->
                          Text.IO.putStrLn .
                            PP.renderStrict .
                              PP.layoutPretty PP.defaultLayoutOptions =<<
                                ppSomeCheckResult appCtx checkedFunc checkedResult
                 )
      Config.CrashEquivalence eqConfig ->
        do path' <-
             genBitCode
               (cruxOpts {inputFiles = [EqConfig.equivModule eqConfig]})
               llOpts
           memVar' <- mkMemVar "uc-crux-llvm:llvm_memory'" halloc
           SomeModuleContext' modCtx' <- translateFile llOpts halloc memVar' path'
           void $
             checkEquiv
               appCtx
               modCtx
               modCtx'
               halloc
               cruxOpts
               llOpts
               (EqConfig.equivOrOrder eqConfig)
               (EqConfig.equivEntryPoints eqConfig)
    return ExitSuccess

translateLLVMModule ::
  LLVMOptions ->
  Crucible.HandleAllocator ->
  GlobalVar Mem ->
  FilePath ->
  L.Module ->
  IO SomeModuleContext'
translateLLVMModule llOpts halloc memVar moduleFilePath llvmMod =
  do
    (Some trans, _warns) <- -- TODO? should we do something with these warnings?
      let ?transOpts = transOpts llOpts
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
  LLVMOptions ->
  Crucible.HandleAllocator ->
  GlobalVar Mem ->
  FilePath ->
  IO SomeModuleContext'
translateFile llOpts halloc memVar moduleFilePath =
  translateLLVMModule llOpts halloc memVar moduleFilePath =<< parseLLVM moduleFilePath
