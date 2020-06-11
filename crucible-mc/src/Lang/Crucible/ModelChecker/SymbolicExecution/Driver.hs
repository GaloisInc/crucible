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
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SymbolicExecution.Driver
  ( analyzeBlocks,
    natOfBlockID,
  )
where

import qualified Control.Lens as L
import Control.Monad (void, when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader, asks, runReaderT)
import Crux.LLVM.Overrides
import Crux.LLVM.Simulate
import Crux.Types
import Data.Foldable (toList)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.LLVM
import Lang.Crucible.LLVM.DataLayout (noAlignment)
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Run
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
  Backend.IsSymInterface sym =>
  LLVMContext arch ->
  ExecState p sym ext (RegEntry sym rtp) ->
  IO ()
doDebugExecState llvmCtx execState =
  do
    when (debugExecState || debugMemory || debugPredicates) $ putStrLn (replicate 80 '=')
    when debugExecState $ print (ppExecState execState)
    when debugMemory $ dumpMemory llvmCtx execState
    when debugPredicates $ do
      dumpAssumptions execState
      dumpObligations execState
    when stepManually (void getLine)

data RunBlockReader sym globCtx arch ext blocks ret ctx = RunBlockReader
  { runBlockBlock :: Core.Block ext blocks ret ctx,
    runBlockGlobalContext :: Ctx.Assignment (GlobalInfo sym) globCtx,
    runBlockLLVMContext :: LLVMContext arch,
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
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  HasPtrWidth w =>
  sym ->
  LLVMContext arch ->
  ExecState p sym ext rtp ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  IO (Ctx.Assignment (RegEntry sym) globCtx)
gatherGlobals sym llvmCtx execState globInfos =
  do
    mem <- getMemory llvmCtx execState
    traverseFC (gatherGlobal sym mem) globInfos

gatherGlobal ::
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  HasPtrWidth w =>
  sym ->
  MemImpl sym ->
  GlobalInfo sym tp ->
  IO (RegEntry sym tp)
gatherGlobal sym mem (GlobalInfo {..}) =
  do
    resolved <- doResolveGlobal sym mem globalSymbol
    storageType <- toStorableType globalMemType
    regValue <- doLoad sym mem resolved storageType globalTypeRepr noAlignment
    return $ RegEntry {regType = globalTypeRepr, regValue}

-- | @endBlock@ gathers the last information we need about the basic block that
-- was just explored, and finalizes the computed @BlockInfo@.
endBlock ::
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  HasPtrWidth w =>
  MonadIO m =>
  MonadReader (RunBlockReader sym globCtx arch ext blocks ret block) m =>
  ExecState p sym ext rtp ->
  BlockEnd sym ->
  m (BlockInfo sym globCtx block)
endBlock execState blockEnd =
  do
    sym <- asks runBlockSym
    blockID <- asks (natOfBlockID . Core.blockID . runBlockBlock)
    globalInfos <- asks runBlockGlobalContext
    llvmCtx <- asks runBlockLLVMContext
    globals <- liftIO $ gatherGlobals sym llvmCtx execState globalInfos
    assumptionsSeq <- liftIO $ Backend.collectAssumptions sym
    let assumptions = L.view Backend.labeledPred <$> toList assumptionsSeq
    obligations <- liftIO $ mapM (proofGoalExpr sym) =<< Backend.proofGoalsToList <$> Backend.getProofObligations sym
    return $
      BlockInfo
        { blockInfoEnd = blockEnd,
          blockInfoGlobals = globals,
          blockInfoID = blockID,
          blockInfoAssumptions = assumptions,
          blockInfoObligations = obligations
        }

runBlock ::
  ArchOk arch =>
  HasLLVMAnn sym =>
  Backend.IsBoolSolver sym =>
  Backend.IsSymInterface sym =>
  IsSyntaxExtension ext =>
  MonadIO m =>
  MonadReader (RunBlockReader sym globCtx arch ext blocks ret block) m =>
  ExecState p sym ext (RegEntry sym ret) ->
  m (BlockInfo sym globCtx block)
runBlock es =
  do
    llvmCtx <- asks runBlockLLVMContext
    liftIO $ doDebugExecState llvmCtx es
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
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  IsSyntaxExtension (LLVM arch) =>
  MonadIO m =>
  Module ->
  ModuleTranslation arch ->
  Core.CFG (LLVM arch) blocks init ret ->
  LLVMContext arch ->
  SimContext (Model sym) sym (LLVM arch) ->
  SymGlobalState sym ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Core.Block (LLVM arch) blocks ret block ->
  m (BlockInfo sym globCtx block)
analyzeBlock llvmModule moduleTranslation cfg llvmCtx simCtx globSt globCtx block =
  do
    let sym = L.view ctxSymInterface simCtx
        blockArgs = Core.blockInputs block
        blockArgsNames =
          namesForContext
            (blockArgumentName (Core.blockID block))
            blockArgs
    -- assumptions/obligations must be cleared for each block
    liftIO $ Backend.resetAssumptionState sym
    liftIO $ Backend.clearProofObligations sym
    regMap <- liftIO $ freshRegMap sym blockArgsNames blockArgs
    let runBlockReader =
          RunBlockReader
            { runBlockBlock = block,
              runBlockGlobalContext = globCtx,
              runBlockLLVMContext = llvmCtx,
              runBlockSym = sym
            }
    let fnRet = Core.cfgReturnType cfg
    flip runReaderT runBlockReader
      $ runBlock
      $ InitialState simCtx globSt defaultAbortHandler fnRet
      $ runOverrideSim fnRet
      $ do
        registerFunctions llvmModule moduleTranslation
        regValue <$> callBlock cfg (Core.blockID block) regMap

analyzeBlocks ::
  ArchOk arch =>
  Backend.IsSymInterface sym =>
  HasLLVMAnn sym =>
  IsSyntaxExtension (LLVM arch) =>
  MonadIO m =>
  Module ->
  ModuleTranslation arch ->
  Core.CFG (LLVM arch) blocks init ret ->
  LLVMContext arch ->
  SimContext (Model sym) sym (LLVM arch) ->
  SymGlobalState sym ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  m (Ctx.Assignment (BlockInfo sym globCtx) blocks)
analyzeBlocks llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos =
  do
    when dumpCFG $ liftIO $ print $ Core.ppCFG True cfg
    traverseFC
      (analyzeBlock llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos)
      (Core.cfgBlockMap cfg)
