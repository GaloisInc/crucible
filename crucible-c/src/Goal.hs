{-# Language TypeFamilies #-}
module Goal where

import Control.Lens((^.))
import Control.Monad(forM)
import Data.Foldable(toList)
import Data.List(nub)
import Data.Maybe(mapMaybe)

import What4.Interface (notPred)
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check )
import What4.Protocol.SMTWriter(mkFormula,assumeFormula,smtExprGroundEvalFn)
import What4.ProgramLoc(ProgramLoc(..), Position(..))

import Lang.Crucible.Backend
        ( ProofObligation, labeledPredMsg, labeledPred
        , AssumptionReason(..), ProofGoal(..), assumptionLoc )
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, getSolverProcess )
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)

import Types
import Model
import Options


data ProofResult = Proved
                 | NotProved (Maybe String)   -- ^ Counter example, if any

proveGoal ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO ProofResult
proveGoal ctxt g =
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
            Sat () -> do f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                         let model = ctxt ^. cruciblePersonality
                         str <- ppModel f model
                         return (NotProved (Just str))
            Unknown -> return (NotProved Nothing)





