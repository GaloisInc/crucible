{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.SymbolicExecution.Debugging
-- Description      : Debugging facilities for the symbolic execution of blocks
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
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
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified What4.Interface as What4
import What4.LabeledPred (labeledPred)

-- TODO: move this elsewhere
proofGoalExpr ::
  What4.IsSymExprBuilder sym =>
  sym ->
  Backend.ProofGoal
    (Backend.LabeledPred (What4.Pred sym) Backend.AssumptionReason)
    (Backend.LabeledPred (What4.Pred sym) SimError) ->
  IO (What4.Pred sym)
proofGoalExpr sym Backend.ProofGoal {..} =
  do
    assumptions <- What4.andAllOf sym L.folded (L.view labeledPred <$> proofAssumptions)
    let conclusion = L.view labeledPred proofGoal
    What4.impliesPred sym assumptions conclusion

dumpAssumptions ::
  Backend.IsSymInterface sym =>
  ExecState p sym ext rtp ->
  IO ()
dumpAssumptions execState =
  do
    let sym = L.view ctxSymInterface (execStateContext execState)
    assumptions <- Backend.collectAssumptions sym
    putStrLn $ "Assumptions : " ++ show (length assumptions)
    forM_ assumptions $ \assumption ->
      print . PP.pretty . What4.printSymExpr $ L.view labeledPred assumption

dumpObligations ::
  Backend.IsBoolSolver sym =>
  What4.IsSymExprBuilder sym =>
  ExecState p sym ext rtp ->
  IO ()
dumpObligations execState =
  do
    let sym = L.view ctxSymInterface (execStateContext execState)
    obligations <- Backend.proofGoalsToList <$> Backend.getProofObligations sym
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
