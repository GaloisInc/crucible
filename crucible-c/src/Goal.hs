module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)

import What4.Interface
        (IsExprBuilder, Pred, notPred, impliesPred)
import What4.AssumptionStack(ProofGoal(..))
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver )
-- import What4.Solver.Z3(z3Adapter)


import Lang.Crucible.Backend
        ( ProofObligation, labeledPredMsg, labeledPred )
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, checkSatisfiableWithModel, getSolverProcess )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)

import Error
import Types
import Model


-- XXX: Change
obligGoal :: IsExprBuilder sym => sym -> ProofObligation sym -> IO (Pred sym)
obligGoal sym g = foldM imp (proofGoal g ^. labeledPred)
                            (proofAssumptions g)
  where
  imp p a = impliesPred sym (a ^. labeledPred) p

proveGoal ::
  OnlineSolver s solver =>
  SimCtxt (ExprBuilder s (OnlineBackendState solver)) arch ->
  ProofObligation (ExprBuilder s (OnlineBackendState solver)) ->
  IO (Maybe Error)
proveGoal ctxt g =
  do let sym = ctxt ^. ctxSymInterface
     g1 <- obligGoal sym g
     p <- notPred sym g1
     sp <- getSolverProcess sym

     checkSatisfiableWithModel sp p $ \res ->
        case res of
          Unsat -> return Nothing
          Sat evalFn ->
            do let model = ctxt ^. cruciblePersonality
               str <- ppModel evalFn model
               return (Just (e (Just str)))
          _  -> return (Just (e Nothing))

  where
  a    = proofGoal g
  e mb = FailedToProve (a ^. labeledPredMsg) mb



