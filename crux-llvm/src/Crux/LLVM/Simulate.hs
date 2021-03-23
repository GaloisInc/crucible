{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}

module Crux.LLVM.Simulate where

import Data.String (fromString)
import qualified Data.Map.Strict as Map
import Data.IORef
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad.State(liftIO)
import Data.Text (Text)
import GHC.Exts ( proxy# )

import System.IO (stdout)

import Data.Parameterized.Some (Some(..))
import Data.Parameterized.Context (pattern Empty)

import Data.LLVM.BitCode (parseBitCodeFromFile)
import qualified Text.LLVM as LLVM
import Prettyprinter

-- what4

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
  , ppSimError
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
        , explainCex, CexExplanation(..)
        )
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, globalInitMap
        , transContext, cfgMap
        , LLVMContext, llvmMemVar, ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )
import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, register_llvm_overrides)

import Lang.Crucible.LLVM.Errors( ppBB )
import Lang.Crucible.LLVM.Extension( LLVM )

-- crux
import qualified Crux

import Crux.Types
import Crux.Model
import Crux.Log

import Crux.LLVM.Config
import Crux.LLVM.Overrides

-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  HandleAllocator ->
  sym ->
  MemOptions ->
  LLVMContext arch ->
  SimCtxt Model sym LLVM
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
parseLLVM :: FilePath -> IO LLVM.Module
parseLLVM file =
  do ok <- parseBitCodeFromFile file
     case ok of
       Left err -> throwCError (LLVMParseError err)
       Right m  -> return m

registerFunctions ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  LLVM.Module ->
  ModuleTranslation arch ->
  OverM Model sym LLVM ()
registerFunctions llvm_module mtrans =
  do let llvm_ctx = mtrans ^. transContext
     let ?lc = llvm_ctx ^. llvmTypeCtx

     -- register the callable override functions
     register_llvm_overrides llvm_module []
       (concat [ cruxLLVMOverrides proxy#
               , svCompOverrides
               , cbmcOverrides proxy#
               ])
       llvm_ctx

     -- register all the functions defined in the LLVM module
     mapM_ (registerModuleFn llvm_ctx) $ Map.elems $ cfgMap mtrans

simulateLLVMFile :: FilePath -> LLVMOptions -> Crux.SimulatorCallback
simulateLLVMFile llvm_file llvmOpts = Crux.SimulatorCallback $ \sym _maybeOnline ->
  do llvm_mod   <- parseLLVM llvm_file
     halloc     <- newHandleAllocator
     let ?laxArith = laxArithmetic llvmOpts
     let ?optLoopMerge = loopMerge llvmOpts
     Some trans <- translateModule halloc llvm_mod
     let llvmCtxt = trans ^. transContext

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
         do liftIO $ say "Crux" $ unwords ["Using pointer width:", show ptrW]
            bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
            let ?lc = llvmCtxt^.llvmTypeCtx
            -- shrug... some weird interaction between do notation and implicit parameters here...
            -- not sure why I have to let/in this expression...
            let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb) in
              do let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) llvmCtxt)
                                { printHandle = view outputHandle ?outputConfig }
                 mem <- populateAllGlobals sym (globalInitMap trans)
                           =<< initializeAllMemory sym llvmCtxt llvm_mod

                 let globSt = llvmGlobals llvmCtxt mem

                 let initSt = InitialState simctx globSt defaultAbortHandler UnitRepr $
                          runOverrideSim UnitRepr $
                            do registerFunctions llvm_mod trans
                               checkFun (entryPoint llvmOpts) (cfgMap trans)

                 -- arbitrary, we should probabl make this limit configurable
                 let detailLimit = 10

                 let explainFailure evalFn gl =
                       do bb <- readIORef bbMapRef
                          ex <- explainCex sym bb evalFn >>= \f -> f (gl ^. labeledPred)
                          let details = case ex of
                                NoExplanation -> mempty
                                DisjOfFailures xs ->
                                  case map ppBB xs of
                                    []  -> mempty
                                    [x] -> indent 2 x
                                    xs' | length xs' <= detailLimit
                                        -> "All of the following conditions failed:" <> line <> indent 2 (vcat xs')
                                        | otherwise
                                        -> "All of the following conditions failed (and other conditions have been elided to reduce output): "
                                               <> line <> indent 2 (vcat (take detailLimit xs'))

                          return $ vcat [ ppSimError (gl^.labeledPredMsg), details ]

                 return (Crux.RunnableState initSt, explainFailure)


checkFun ::
  (Logs) =>
  String -> ModuleCFGMap -> OverM personality sym LLVM ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ say "Crux" ("Simulating function " ++ show nm)
             (callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwCError BadFun  -- TODO(lb): Suggest uc-crux-llvm?
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
