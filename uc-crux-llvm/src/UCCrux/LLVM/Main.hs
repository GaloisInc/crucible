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
    Crux.defaultOutputConfig,
    loopOnFunctions,
    translateLLVMModule,
    translateFile,
    SomeModuleContext' (..),
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
import Crux.Config.Common

 -- local
import Crux.LLVM.Config
import Crux.LLVM.Compile (genBitCode)
import Crux.LLVM.Simulate (parseLLVM)

import           Paths_uc_crux_llvm (version)
import qualified UCCrux.LLVM.Config as Config
import           UCCrux.LLVM.Config (UCCruxLLVMOptions)
import           UCCrux.LLVM.Context.App (AppContext)
import           UCCrux.LLVM.Context.Module (ModuleContext, SomeModuleContext(..), makeModuleContext, moduleTranslation)
import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.Translation (ppTypeTranslationError)
import           UCCrux.LLVM.Run.Explore (explore)
import           UCCrux.LLVM.Run.Result (BugfindingResult(..), SomeBugfindingResult(..))
import qualified UCCrux.LLVM.Run.Result as Result
import           UCCrux.LLVM.Run.Loop (loopOnFunction)
{- ORMOLU_ENABLE -}

mainWithOutputTo :: Handle -> IO ExitCode
mainWithOutputTo h = mainWithOutputConfig $ Crux.mkOutputConfig False h h

mainWithOutputConfig :: (Maybe CruxOptions -> Crux.OutputConfig) -> IO ExitCode
mainWithOutputConfig mkOutCfg =
  do
    conf <- Config.ucCruxLLVMConfig
    Crux.loadOptions mkOutCfg "uc-crux-llvm" version conf $ \opts ->
      do
        (appCtx, cruxOpts, ucOpts) <- Config.processUCCruxLLVMOptions opts
        path <- genBitCode cruxOpts (Config.ucLLVMOptions ucOpts)
        halloc <- Crucible.newHandleAllocator
        memVar <- mkMemVar "uc-crux-llvm:llvm_memory" halloc
        SomeModuleContext' modCtx <- translateFile ucOpts halloc memVar path
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
                    Crux.say Crux.Simply "Crux" ("Results for " <> Text.pack func)
                    Crux.say Crux.Simply "Crux"
                      $ Result.printFunctionSummary (summary result)
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
      let ?laxArith = laxArithmetic llvmOpts
          ?optLoopMerge = loopMerge llvmOpts
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

-- | Postcondition: The keys of the returned map are exactly the entryPoints of
-- the 'UCCruxLLVMOptions'.
loopOnFunctions ::
  Crux.Logs =>
  AppContext ->
  ModuleContext m arch ->
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
