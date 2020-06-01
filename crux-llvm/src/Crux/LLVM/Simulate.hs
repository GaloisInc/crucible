{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Crux.LLVM.Simulate where

import Data.String (fromString)
import qualified Data.Map as Map
import Data.IORef
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad.State(liftIO)
import Data.Text (Text)

import System.FilePath( (</>) )
import System.IO (stdout)

import Data.Parameterized.Some (Some(..))
import Data.Parameterized.Context (pattern Empty)

import Text.LLVM.AST (Module)
import Data.LLVM.BitCode (parseBitCodeFromFile)
import qualified Text.LLVM as LLVM

-- crucible
import Lang.Crucible.Backend
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator
  ( emptyRegMap
  , fnBindingsFromList, runOverrideSim, callCFG
  , initSimContext, profilingMetrics
  , ExecState( InitialState )
  , SimState, defaultAbortHandler, printHandle
  )
import Lang.Crucible.Simulator.ExecutionTree ( stateGlobals )
import Lang.Crucible.Simulator.GlobalState ( lookupGlobal )
import Lang.Crucible.Simulator.Profiling ( Metric(Metric) )


-- crucible-llvm
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals, registerModuleFn )
import Lang.Crucible.LLVM.Globals
        ( initializeAllMemory, populateAllGlobals )
import Lang.Crucible.LLVM.MemModel
        ( MemImpl, withPtrWidth, memAllocCount, memWriteCount
        , MemOptions(..), HasLLVMAnn, LLVMAnnMap
        )
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, globalInitMap
        , transContext, cfgMap
        , LLVMContext, llvmMemVar, ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )
import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, register_llvm_overrides)

import Lang.Crucible.LLVM.Extension(LLVM)

-- crux
import qualified Crux

import Crux.Types
import Crux.Model
import Crux.Log
import Crux.Config.Common

import Crux.LLVM.Config
import Crux.LLVM.Overrides

-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  HandleAllocator ->
  sym ->
  MemOptions ->
  LLVMContext arch ->
  SimCtxt sym (LLVM arch)
setupSimCtxt halloc sym mo llvmCtxt =
  initSimContext sym
                 llvmIntrinsicTypes
                 halloc
                 stdout
                 (fnBindingsFromList [])
                 (llvmExtensionImpl mo)
                 emptyModel
    & profilingMetrics %~ Map.union (llvmMetrics llvmCtxt)


-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do ok <- parseBitCodeFromFile file
     case ok of
       Left err -> throwCError (LLVMParseError err)
       Right m  -> return m

registerFunctions ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  LLVM.Module ->
  ModuleTranslation arch ->
  OverM sym (LLVM arch) ()
registerFunctions llvm_module mtrans =
  do let llvm_ctx = mtrans ^. transContext
     let ?lc = llvm_ctx ^. llvmTypeCtx

     -- register the callable override functions
     register_llvm_overrides llvm_module [] (cruxLLVMOverrides++svCompOverrides++cbmcOverrides) llvm_ctx

     -- register all the functions defined in the LLVM module
     mapM_ (registerModuleFn llvm_ctx) $ Map.elems $ cfgMap mtrans

simulateLLVM :: CruxOptions -> LLVMOptions -> Crux.SimulatorCallback
simulateLLVM cruxOpts llvmOpts = Crux.SimulatorCallback $ \sym _maybeOnline ->
 do llvm_mod   <- parseLLVM (Crux.outDir cruxOpts </> "combined.bc")
    halloc     <- newHandleAllocator
    let ?laxArith = laxArithmetic llvmOpts
    Some trans <- translateModule halloc llvm_mod
    let llvmCtxt = trans ^. transContext

    llvmPtrWidth llvmCtxt $ \ptrW ->
      withPtrWidth ptrW $
        do bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
           let ?lc = llvmCtxt^.llvmTypeCtx
           -- shrug... some weird interaction between do notation and implicit parameters here...
           -- not sure why I have to let/in this expression...
           let ?badBehaviorMap = bbMapRef in
             do let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) llvmCtxt)
                               { printHandle = view outputHandle ?outputConfig }
                mem <- populateAllGlobals sym (globalInitMap trans)
                          =<< initializeAllMemory sym llvmCtxt llvm_mod

                let globSt = llvmGlobals llvmCtxt mem

                let initSt = InitialState simctx globSt defaultAbortHandler UnitRepr $
                         runOverrideSim UnitRepr $
                           do registerFunctions llvm_mod trans
                              checkFun (entryPoint llvmOpts) (cfgMap trans)

                return $ Crux.RunnableState initSt


checkFun ::
  (ArchOk arch, Logs) =>
  String -> ModuleCFGMap arch -> OverM sym (LLVM arch) ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwCError BadFun
    Nothing -> throwCError (MissingFun nm)

---------------------------------------------------------------------
-- Profiling

llvmMetrics :: forall arch p sym ext
             . LLVMContext arch
            -> Map.Map Text (Metric p sym ext)
llvmMetrics llvmCtxt = Map.fromList [ ("LLVM.allocs", allocs)
                                    , ("LLVM.writes", writes)
                                    ]
  where
    allocs = Metric $ measureMemBy memAllocCount
    writes = Metric $ measureMemBy memWriteCount

    measureMemBy :: (MemImpl sym -> Int)
                 -> SimState p sym ext r f args
                 -> IO Integer
    measureMemBy f st = do
      let globals = st ^. stateGlobals
      case lookupGlobal (llvmMemVar llvmCtxt) globals of
        Just mem -> return $ toInteger (f mem)
        Nothing -> fail "Memory missing from global vars"

