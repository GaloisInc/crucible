{-# Language TypeFamilies #-}
{-# Language PatternSynonyms #-}
module Goal where

import Control.Lens((^.), (&), (.~))
import Control.Monad(forM)
import qualified Data.Sequence as Seq

import What4.Interface (notPred, falsePred)
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check, SolverProcess )
import What4.Protocol.SMTWriter(mkFormula,assumeFormula,smtExprGroundEvalFn)

import Lang.Crucible.Backend ( ProofObligation, labeledPred, ProofGoal(..) )
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, getSolverProcess )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)

import Types
import Model


data ProofResult = Proved
                 | NotProved (Maybe ModelViews)   -- ^ Counter example, if any



proveGoal ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO ProofResult

proveGoal ctxt g = proveGoal' ctxt g $ \sp ->
  do f <- smtExprGroundEvalFn (solverConn sp) (solverEvalFuns sp)
     let model = ctxt ^. cruciblePersonality
     str <- ppModel f model
     return (Just str)


canProve ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO ProofResult

canProve ctxt g = proveGoal' ctxt g $ \_sp -> return Nothing


proveGoal' ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
  ProofObligation sym ->
  (SolverProcess s solver -> IO (Maybe ModelViews)) ->
  IO ProofResult
proveGoal' ctxt g isSat =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     let conn = solverConn sp
     asmps <- forM (proofAssumptions g) $ \a ->
                 mkFormula conn (a ^. labeledPred)
     conc  <- mkFormula conn =<< notPred sym (proofGoal g ^. labeledPred)
     inNewFrame conn $
       do mapM_ (assumeFormula conn) asmps
          assumeFormula conn conc
          res <- check sp
          case res of
            Unsat  -> return Proved
            Sat () -> NotProved <$> isSat sp
            Unknown -> return (NotProved Nothing)


data SimpResult sym =
    Trivial
  | NotTrivial (ProofObligation sym)


simpProved ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO (SimpResult sym)
simpProved ctxt goal =
  do let false = falsePred (ctxt ^. ctxSymInterface)
         g1 = goal { proofGoal = (proofGoal goal) & labeledPred .~ false }
     res <- canProve ctxt g1
     case res of
       Proved -> return Trivial
       _      -> dropAsmps Seq.empty (proofAssumptions goal)

  where
  -- XXX: can use incremental for more efficient checking
  -- A simple way to figure out what might be relevant assumptions.
  dropAsmps keep asmps =
    case asmps of
      Seq.Empty -> return (NotTrivial goal { proofAssumptions = keep })
      a Seq.:<| as ->
        do res <- canProve ctxt goal { proofAssumptions = as Seq.>< keep }
           case res of
             Proved -> dropAsmps keep as
             NotProved {} -> dropAsmps (a Seq.:<| keep) as






