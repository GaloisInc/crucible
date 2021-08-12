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
import qualified Data.List as List
import Data.Maybe ( fromMaybe )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Traversable as T
import Control.Lens ((&), (%~), (^.), view)
import Control.Monad.State(liftIO)
import Data.Text as Text (Text, pack)
import GHC.Exts ( proxy# )

import System.IO (stdout)

import Data.Parameterized.Some (Some(..))
import Data.Parameterized.Context (pattern Empty)

import Data.LLVM.BitCode (parseBitCodeFromFile)
import qualified Text.LLVM as LLVM
import Prettyprinter

-- what4
import qualified What4.Expr.Builder as WEB

-- crucible
import Lang.Crucible.Backend
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle(newHandleAllocator,HandleAllocator)
import Lang.Crucible.Simulator
  ( emptyRegMap
  , fnBindingsFromList, runOverrideSim, callCFG
  , initSimContext, profilingMetrics
  , ExecState( InitialState ), GlobalVar
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
        ( Mem, MemImpl, mkMemVar, withPtrWidth, memAllocCount, memWriteCount
        , MemOptions(..), HasLLVMAnn, LLVMAnnMap
        , explainCex, CexExplanation(..)
        )
import Lang.Crucible.LLVM.Translation
        ( translateModule, ModuleTranslation, globalInitMap
        , transContext, cfgMap, ModuleCFGMap
        , llvmPtrWidth, llvmTypeCtx
        )
import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, register_llvm_overrides )

import Lang.Crucible.LLVM.Errors( ppBB )
import Lang.Crucible.LLVM.Extension( LLVM, ArchWidth )
import Lang.Crucible.LLVM.SymIO
       ( LLVMFileSystem, llvmSymIOIntrinsicTypes, symio_overrides, initialLLVMFileSystem, SomeOverrideSim(..) )
import qualified Lang.Crucible.SymIO as SymIO
import qualified Lang.Crucible.SymIO.Loader as SymIO.Loader

-- crux
import qualified Crux

import Crux.Types
import Crux.Log ( outputHandle )

import Crux.LLVM.Config
import qualified Crux.LLVM.Log as Log
import Crux.LLVM.Overrides

-- | Create a simulator context for the given architecture.
setupSimCtxt ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  HandleAllocator ->
  sym ->
  MemOptions ->
  GlobalVar Mem ->
  SimCtxt Crux sym LLVM
setupSimCtxt halloc sym mo memVar =
  initSimContext sym
                 (MapF.union llvmIntrinsicTypes llvmSymIOIntrinsicTypes)
                 halloc
                 stdout
                 (fnBindingsFromList [])
                 (llvmExtensionImpl mo)
                 CruxPersonality
    & profilingMetrics %~ Map.union (memMetrics memVar)

-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO LLVM.Module
parseLLVM file =
  do ok <- parseBitCodeFromFile file
     case ok of
       Left err -> throwCError (LLVMParseError err)
       Right m  -> return m

registerFunctions ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym, ptrW ~ ArchWidth arch) =>
  LLVMOptions ->
  LLVM.Module ->
  ModuleTranslation arch ->
  Maybe (LLVMFileSystem ptrW) ->
  OverM Crux sym LLVM ()
registerFunctions llvmOpts llvm_module mtrans fs0 =
  do let llvm_ctx = mtrans ^. transContext
     let ?lc = llvm_ctx ^. llvmTypeCtx
         ?intrinsicsOpts = intrinsicsOpts llvmOpts
         ?memOpts = memOpts llvmOpts

     -- register the callable override functions
     register_llvm_overrides llvm_module []
       (concat [ cruxLLVMOverrides proxy#
               , svCompOverrides
               , cbmcOverrides proxy#
               , maybe [] symio_overrides fs0
               ])
       llvm_ctx

     -- register all the functions defined in the LLVM module
     mapM_ (registerModuleFn llvm_ctx) $ Map.elems $ cfgMap mtrans

simulateLLVMFile ::
  Crux.Logs msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  FilePath -> LLVMOptions -> Crux.SimulatorCallback msgs
simulateLLVMFile llvm_file llvmOpts = do
  Crux.SimulatorCallback $ \sym maybeOnline -> do
    halloc <- newHandleAllocator
    bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
    let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
    runnableState <- setupFileSim halloc llvm_file llvmOpts sym maybeOnline
    return (runnableState, explainFailure sym bbMapRef)

setupFileSim :: Crux.Logs msgs
             => Log.SupportsCruxLLVMLogMessage msgs
             => IsSymInterface sym
             => sym ~ WEB.ExprBuilder t st fs
             => HasLLVMAnn sym
             => HandleAllocator
             -> FilePath
             -> LLVMOptions
             -> sym -> Maybe (Crux.SomeOnlineSolver sym)
             -> IO (Crux.RunnableState sym)
setupFileSim halloc llvm_file llvmOpts sym _maybeOnline =
  do memVar <- mkMemVar "crux:llvm_memory" halloc

     let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) memVar)
                  { printHandle = view outputHandle ?outputConfig }

     prepped <- prepLLVMModule llvmOpts halloc sym llvm_file memVar

     let globSt = llvmGlobals memVar (prepMem prepped)

     Some trans <- return $ prepSomeTrans prepped
     llvmPtrWidth (trans ^. transContext) $ \ptrW -> withPtrWidth ptrW $ do
       mContents <- T.traverse (SymIO.Loader.loadInitialFiles sym) (symFSRoot llvmOpts)
       -- We modify the defaults, which are extremely conservative.  Unless the
       -- user directs otherwise, we default to connecting stdin, stdout, and stderr.
       let defaultFileContents = SymIO.emptyInitialFileSystemContents
                                 { SymIO.useStderr = True
                                 , SymIO.useStdout = True
                                 , SymIO.concreteFiles = Map.fromList [(SymIO.StdinTarget, mempty)]
                                 }
       let fsContents = fromMaybe defaultFileContents mContents
       let mirroredOutputs = [ (SymIO.StdoutTarget, ?outputConfig ^. Crux.outputHandle)
                             , (SymIO.StderrTarget, ?outputConfig ^. Crux.outputHandle)
                             ]
       (fs0, globSt', SomeOverrideSim initFSOverride) <- initialLLVMFileSystem halloc sym ptrW fsContents mirroredOutputs globSt
       return $ Crux.RunnableState $
         InitialState simctx globSt' defaultAbortHandler UnitRepr $
           runOverrideSim UnitRepr $
             withPtrWidth ptrW $
                do registerFunctions llvmOpts (prepLLVMMod prepped) trans (Just fs0)
                   initFSOverride
                   checkFun (entryPoint llvmOpts) (cfgMap trans)


data PreppedLLVM sym = PreppedLLVM { prepLLVMMod :: LLVM.Module
                                   , prepSomeTrans :: Some ModuleTranslation
                                   , prepMemVar :: GlobalVar Mem
                                   , prepMem :: MemImpl sym
                                   }

-- | Given an LLVM Bitcode file, and a GlobalVar memory, translate the
-- file into the Crucible representation and add the globals and
-- definitions from the file to the GlobalVar memory.

prepLLVMModule :: IsSymInterface sym
               => HasLLVMAnn sym
               => Crux.Logs msgs
               => Log.SupportsCruxLLVMLogMessage msgs
               => LLVMOptions
               -> HandleAllocator
               -> sym
               -> FilePath  -- for the LLVM bitcode file
               -> GlobalVar Mem
               -> IO (PreppedLLVM sym)
prepLLVMModule llvmOpts halloc sym bcFile memVar = do
    llvmMod <- parseLLVM bcFile
    Some trans <- let ?transOpts = transOpts llvmOpts
                  in translateModule halloc memVar llvmMod
    mem <- let llvmCtxt = trans ^. transContext in
             let ?lc = llvmCtxt ^. llvmTypeCtx
                 ?memOpts = memOpts llvmOpts
             in llvmPtrWidth llvmCtxt $ \ptrW ->
               withPtrWidth ptrW $ do
               Log.sayCruxLLVM (Log.UsingPointerWidthForFile (intValue ptrW) (Text.pack bcFile))
               populateAllGlobals sym (globalInitMap trans)
                 =<< initializeAllMemory sym llvmCtxt llvmMod
    return $ PreppedLLVM llvmMod (Some trans) memVar mem


checkFun ::
  Crux.Logs msgs =>
  Log.SupportsCruxLLVMLogMessage msgs =>
  String -> ModuleCFGMap -> OverM personality sym LLVM ()
checkFun nm mp =
  case Map.lookup (fromString nm) mp of
    Just (_, AnyCFG anyCfg) ->
      case cfgArgTypes anyCfg of
        Empty ->
          do liftIO $ Log.sayCruxLLVM (Log.SimulatingFunction (Text.pack nm))
             (callCFG anyCfg emptyRegMap) >> return ()
        _     -> throwCError BadFun  -- TODO(lb): Suggest uc-crux-llvm?
    Nothing -> throwCError (MissingFun nm)

---------------------------------------------------------------------
-- Profiling

memMetrics :: forall p sym ext
             . GlobalVar Mem
            -> Map.Map Text (Metric p sym ext)
memMetrics memVar = Map.fromList
                    -- Note: These map keys are used by profile.js in
                    -- https://github.com/GaloisInc/sympro-ui and must
                    -- match the names there.
                    [ ("LLVM.allocs", allocs)
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
      case lookupGlobal memVar globals of
        Just mem -> return $ toInteger (f mem)
        Nothing -> fail "Memory missing from global vars"

----------------------------------------------------------------------

-- arbitrary, we should probably make this limit configurable
detailLimit :: Int
detailLimit = 10

explainFailure :: IsSymInterface sym
               => sym ~ WEB.ExprBuilder t st fs
               => sym
               -> IORef (LLVMAnnMap sym)
               -> Crux.Explainer sym t ann
explainFailure sym bbMapRef evalFn gl =
  do bb <- readIORef bbMapRef
     ex <- explainCex sym bb evalFn >>= \f -> f (gl ^. labeledPred)
     let details =
           case ex of
             NoExplanation -> mempty
             DisjOfFailures xs ->
               case ppBB <$> xs of
                 []  -> mempty
                 [x] -> indent 2 x
                 xs' ->
                   let xs'' = List.take detailLimit xs'
                       xs'l = length xs'
                       msg1 = "Failing conditions::"
                       msg2 = if xs'l > detailLimit
                              then "[only displaying the first"
                                   <+> pretty detailLimit
                                   <+> "of" <+> pretty xs'l
                                   <+> "failed conditions]"
                              else "Total failed conditions:" <+> pretty xs'l
                   in nest 2 $ vcat $ msg1 : xs'' <> [msg2]
     return $ vcat [ ppSimError (gl^. labeledPredMsg), details ]
