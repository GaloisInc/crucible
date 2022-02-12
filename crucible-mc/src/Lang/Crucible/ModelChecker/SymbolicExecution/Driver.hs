{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.SymbolicExecution.Driver
-- Description      : Symbolic simulation of Crucible blocks to gather @BlockInfo@s
-- Copyright        : (c) Galois, Inc 2020-2022
-- License          : BSD3
-- Maintainer       : Valentin Robert <val@galois.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SymbolicExecution.Driver
  ( analyzeBlocks,
    natOfBlockID,
  )
where

import qualified Control.Lens as L
import Control.Monad (forM, void, when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader, asks, runReaderT)
import Crux.LLVM.Overrides
import Crux.LLVM.Simulate
import Crux.Types
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.LLVM
import Lang.Crucible.LLVM.DataLayout (noAlignment)
import Lang.Crucible.LLVM.Intrinsics (IntrinsicsOptions, defaultIntrinsicsOptions)
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.ModelChecker.Fresh
import Lang.Crucible.ModelChecker.GlobalInfo
import Lang.Crucible.ModelChecker.NamingConventions
import Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
import Lang.Crucible.ModelChecker.SymbolicExecution.Debugging
import Lang.Crucible.ModelChecker.SymbolicExecution.PrettyPrinting
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState (lookupGlobal)
import qualified Text.LLVM as LLVM

-- TODO: turn these flags into command-line options

-- whether to print the current execution state as we step through the symbolic
-- execution
debugExecState :: Bool
debugExecState = False

-- whether to dump the whole memory at every step (verbose!)
debugMemory :: Bool
debugMemory = False

-- whether to print the assumptions and obligations at every step
debugPredicates :: Bool
debugPredicates = False

-- whether to dump the CFG before starting the symbolic execution
dumpCFG :: Bool
dumpCFG = False

-- when @False@, waits for a line entered between each step
stepManually :: Bool
stepManually = False

doDebugExecState ::
  MonadIO m =>
  MonadReader (RunBlockReader sym bak globCtx arch ext blocks ret block) m =>
  Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  LLVMContext arch ->
  ExecState p sym ext (RegEntry sym rtp) ->
  m ()
doDebugExecState llvmCtx execState =
  do
    currentBlock <- asks runBlockBlock
    liftIO $ do
      when (debugExecState || debugMemory || debugPredicates) $ putStrLn (replicate 80 '=')
      when debugExecState $ putStrLn ("[Block " ++ show (Core.blockID currentBlock) ++ "] " ++ show (ppExecState execState))
      when debugMemory $ dumpMemory llvmCtx execState
      when debugPredicates $ do
        dumpAssumptions execState
        dumpObligations execState
      when stepManually (void getLine)

data RunBlockReader sym bak globCtx arch ext blocks ret block = RunBlockReader
  { runBlockBlock :: Core.Block ext blocks ret block,
    runBlockGlobalContext :: Ctx.Assignment (GlobalInfo sym) globCtx,
    runBlockLLVMContext :: LLVMContext arch,
    runBlockSize :: Ctx.Size block,
    runBlockBak :: bak,
    runBlockSym :: sym
  }

getMemory ::
  LLVMContext arch ->
  ExecState p sym ext rtp ->
  IO (MemImpl sym)
getMemory llvmCtx execState =
  do
    case execStateSimState execState of
      Nothing -> error "getMemory: no simulation state"
      Just (SomeSimState simState) ->
        do
          let var = llvmMemVar llvmCtx
          let gs = L.view stateGlobals simState
          case lookupGlobal var gs of
            Nothing -> error "getMemory: LLVM memory not initialized"
            Just m -> pure m

gatherGlobals ::
  Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  HasLLVMAnn sym =>
  HasPtrWidth w =>
  bak ->
  LLVMContext arch ->
  ExecState p sym ext rtp ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  IO (Ctx.Assignment (RegEntry sym) globCtx)
gatherGlobals bak llvmCtx execState globInfos =
  do
    mem <- getMemory llvmCtx execState
    traverseFC (gatherGlobal bak mem) globInfos

gatherGlobal ::
  Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  HasLLVMAnn sym =>
  HasPtrWidth w =>
  bak ->
  MemImpl sym ->
  GlobalInfo sym tp ->
  IO (RegEntry sym tp)
gatherGlobal bak mem (GlobalInfo {..}) =
  do
    resolved <- doResolveGlobal bak mem globalSymbol
    storageType <- toStorableType globalMemType
    regValue <- doLoad bak mem resolved storageType globalTypeRepr noAlignment
    return $ RegEntry {regType = globalTypeRepr, regValue}

-- | @endBlock@ gathers the last information we need about the basic block that
-- was just explored, and finalizes the computed @BlockInfo@.
endBlock ::
  Backend.IsSymBackend sym bak =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  HasLLVMAnn sym =>
  HasPtrWidth w =>
  MonadIO m =>
  MonadReader (RunBlockReader sym bak globCtx arch ext blocks ret block) m =>
  ExecState p sym ext rtp ->
  BlockEnd sym ->
  m (BlockInfo sym globCtx block)
endBlock execState blockEnd =
  do
    bak <- asks runBlockBak
    let sym = Backend.backendGetSym bak
    blockID <- asks (integerOfBlockID . Core.blockID . runBlockBlock)
    globalInfos <- asks runBlockGlobalContext
    llvmCtx <- asks runBlockLLVMContext
    globals <- liftIO $ gatherGlobals bak llvmCtx execState globalInfos
    assumptionsPreds <- liftIO $ Backend.getPathCondition bak
    obligationsPreds <- liftIO $ do
      obligations <- maybe [] Backend.goalsToList <$> Backend.getProofObligations bak
      forM obligations (proofGoalExpr sym)
    blockInfoSize <- asks runBlockSize
    return $
      BlockInfo
        { blockInfoEnd = blockEnd,
          blockInfoGlobals = globals,
          blockInfoID = blockID,
          blockInfoAssumptions = [assumptionsPreds],
          blockInfoObligations = obligationsPreds,
          blockInfoSize
        }

runBlock ::
  ArchOk arch =>
  HasLLVMAnn sym =>
  -- Backend.IsBoolSolver sym =>
  Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  IsSyntaxExtension ext =>
  MonadIO m =>
  MonadReader (RunBlockReader sym bak globCtx arch ext blocks ret block) m =>
  ExecState p sym ext (RegEntry sym ret) ->
  m (BlockInfo sym globCtx block)
runBlock es =
  do
    llvmCtx <- asks runBlockLLVMContext
    doDebugExecState llvmCtx es
    case es of
      AbortState {} -> endBlock es BlockEndAborts
      ControlTransferState controlResumption _ ->
        endBlock es $ BlockEndJumps (resumptionTarget controlResumption)
      SymbolicBranchState truePred (PausedFrame _ trueControlResumption _) (PausedFrame _ falseControlResumption _) _ _ ->
        endBlock es $ BlockEndBranches truePred (resumptionTarget trueControlResumption) (resumptionTarget falseControlResumption)
      -- most execution states must simply be stepped forward
      BranchMergeState {} -> liftIO (singleStepCrucible 0 es) >>= runBlock
      CallState {} -> liftIO (singleStepCrucible 0 es) >>= runBlock
      InitialState {} -> liftIO (singleStepCrucible 0 es) >>= runBlock
      OverrideState {} -> liftIO (singleStepCrucible 0 es) >>= runBlock
      RunningState {} -> liftIO (singleStepCrucible 0 es) >>= runBlock
      -- some @ReturnState@s indicate the end of the block, others don't
      -- as long as we see @VFVCall@, we are returning within the bounds of our
      -- function (e.g. from a function or override call), so keep running
      ReturnState _ (VFVCall _ _ _) _ _ -> liftIO (singleStepCrucible 0 es) >>= runBlock
      ReturnState _ (VFVPartial _ _ _ _) _ _ -> error "runBlock ReturnState VFVPartial"
      ReturnState _ VFVEnd r _ -> endBlock es (BlockEndReturns (Core.Some r))
      _ -> error $ "runBlock: unhandled exec state " ++ show (ppExecState es)

resumptionTarget :: ControlResumption p sym ext rtp f -> Core.Some (ResolvedJump sym)
resumptionTarget (CheckMergeResumption target) = Core.Some target
resumptionTarget (ContinueResumption target) = Core.Some target
resumptionTarget (SwitchResumption {}) = error "resumptionTarget of SwitchResumption"
resumptionTarget (OverrideResumption {}) = error "resumptionTarget of OverrideResumption"

analyzeBlock ::
  ArchOk arch =>
  -- Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  MonadIO m =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  LLVM.Module ->
  ModuleTranslation arch ->
  Core.CFG LLVM blocks init ret ->
  LLVMContext arch ->
  SimContext (Crux sym) sym LLVM ->
  SymGlobalState sym ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Core.Block LLVM blocks ret block ->
  m (BlockInfo sym globCtx block)
analyzeBlock llvmModule moduleTranslation cfg llvmCtx simCtx globSt globCtx block =
  let sym = L.view ctxSymInterface simCtx
      blockArgs = Core.blockInputs block
      blockArgsNames =
        namesForContext
          (blockArgumentName (Core.blockID block))
          blockArgs
  in
  withBackend simCtx $ \ bak -> do
    -- assumptions/obligations must be cleared for each block
    liftIO $ Backend.resetAssumptionState bak
    liftIO $ Backend.clearProofObligations bak
    regMap <- liftIO $ freshRegMap sym blockArgsNames blockArgs
    let runBlockReader =
          RunBlockReader
            { runBlockBlock = block,
              runBlockGlobalContext = globCtx,
              runBlockLLVMContext = llvmCtx,
              runBlockSize = Ctx.size (Core.blockInputs block),
              runBlockBak = bak,
              runBlockSym = sym
            }
    let fnRet = Core.cfgReturnType cfg
    flip runReaderT runBlockReader $
      runBlock $
        InitialState simCtx globSt defaultAbortHandler fnRet $
          runOverrideSim fnRet $
            do
              registerFunctions defaultMemOptions defaultIntrinsicsOptions llvmModule moduleTranslation Nothing
              regValue <$> callBlock cfg (Core.blockID block) regMap

analyzeBlocks ::
  ArchOk arch =>
  -- Backend.IsSymBackend sym bak =>
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  MonadIO m =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (?memOpts :: MemOptions) =>
  LLVM.Module ->
  ModuleTranslation arch ->
  Core.CFG LLVM blocks init ret ->
  LLVMContext arch ->
  SimContext (Crux sym) sym LLVM ->
  SymGlobalState sym ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  m (Ctx.Assignment (BlockInfo sym globCtx) blocks)
analyzeBlocks llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos =
  do
    when dumpCFG $ liftIO $ print $ Core.ppCFG True cfg
    traverseFC
      (analyzeBlock llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos)
      (Core.cfgBlockMap cfg)
