{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.SymbolicExecution.Debugging
-- Description      : Debugging facilities for the symbolic execution of blocks
-- Copyright        : (c) Galois, Inc 2020-2022
-- License          : BSD3
-- Maintainer       : Valentin Robert <val@galois.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SymbolicExecution.Debugging
  ( dumpAssumptions,
    dumpMemory,
    dumpObligations,
    proofGoalExpr,
  )
where

import qualified Control.Lens as L
import Control.Monad (forM_)
import qualified Lang.Crucible.Backend as Backend
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)
import Lang.Crucible.LLVM.Translation (LLVMContext, llvmMemVar)
import Lang.Crucible.Simulator (SimError)
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState (lookupGlobal)
import System.IO (stdout)
import qualified What4.Interface as What4
import What4.LabeledPred (labeledPred)

-- TODO: move this elsewhere
proofGoalExpr ::
  What4.IsSymExprBuilder sym =>
  sym ->
  Backend.ProofGoal
    (Backend.CrucibleAssumptions (What4.SymExpr sym))
    -- (Backend.LabeledPred (What4.Pred sym) (Backend.LabeledPred (What4.Pred sym) msg))
    (Backend.LabeledPred (What4.Pred sym) SimError) ->
  IO (What4.Pred sym)
proofGoalExpr sym Backend.ProofGoal {..} =
  do
    assumptions <- Backend.assumptionsPred sym proofAssumptions
    let conclusion = L.view labeledPred proofGoal
    What4.impliesPred sym assumptions conclusion

dumpAssumptions ::
  Backend.IsSymInterface sym =>
  ExecState p sym ext rtp ->
  IO ()
dumpAssumptions execState =
  let simContext = execStateContext execState in
  withBackend simContext $ \ bak -> do
    let sym = L.view ctxSymInterface simContext
    assumptions <- Backend.flattenAssumptions sym =<< Backend.collectAssumptions bak
    putStrLn $ "Assumptions : " ++ show (length assumptions)
    forM_ assumptions $ \assumption ->
      print . What4.printSymExpr $ Backend.assumptionPred assumption -- L.view labeledPred assumption

dumpObligations ::
  Backend.IsSymInterface sym =>
  What4.IsSymExprBuilder sym =>
  ExecState p sym ext rtp ->
  IO ()
dumpObligations execState =
  let simContext = execStateContext execState in
  withBackend simContext $ \ bak -> do
    let sym = L.view ctxSymInterface simContext
    obligations <- maybe [] Backend.goalsToList <$> Backend.getProofObligations bak
    putStrLn $ "Obligations : " ++ show (length obligations)
    forM_ obligations $ \o -> print . What4.printSymExpr =<< proofGoalExpr sym o

dumpMemory ::
  What4.IsSymExprBuilder sym =>
  LLVMContext arch ->
  ExecState p sym ext rtp ->
  IO ()
dumpMemory llvmCtx execState = do
  case execStateSimState execState of
    Nothing -> return ()
    Just (SomeSimState simState) ->
      do
        let var = llvmMemVar llvmCtx
        let gs = L.view stateGlobals simState
        case lookupGlobal var gs of
          Nothing -> return ()
          Just m -> doDumpMem stdout m
