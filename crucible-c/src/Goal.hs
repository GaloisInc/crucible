module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)

import Lang.Crucible.Solver.SimpleBackend(SimpleBackend, SimpleBackendState)
import Lang.Crucible.Solver.Adapter(SolverAdapter(..))
import Lang.Crucible.Solver.BoolInterface(IsBoolExprBuilder, Pred)
import Lang.Crucible.Solver.SimpleBackend.Z3(z3Adapter)
import Lang.Crucible.Solver.SatResult(SatResult(..))


import Lang.Crucible.Simulator.ExecutionTree(ctxSymInterface, simConfig)

import Lang.Crucible.Solver.BoolInterface
        (notPred,impliesPred, Assertion, assertPred, assertMsg)

import Error
import Types


prover :: SolverAdapter SimpleBackendState
prover = z3Adapter


data Goal b = Goal
  { gAssumes :: [Formula b]
  , gShows   :: Assertion (Formula b)
  }

mkGoal :: ([Formula b], Assertion (Formula b)) -> Goal b
mkGoal (as,p) = Goal { gAssumes = as, gShows = p }

obligGoal :: (IsBoolExprBuilder b) => b -> Goal b -> IO (Pred b)
obligGoal sym g = foldM imp (gShows g ^. assertPred) (gAssumes g)
  where
  imp p a = impliesPred sym a p

proveGoal ::
  SimCtxt (SimpleBackend scope) arch ->
  Goal (SimpleBackend scope) ->
  IO ()
proveGoal ctxt g =
  do let sym = ctxt ^. ctxSymInterface
         cfg = simConfig ctxt
     p <- notPred sym =<< obligGoal sym g
     let say _n _x = return ()
     solver_adapter_check_sat prover sym cfg say p $ \res ->
        case res of
          Unsat -> return ()
          Sat (_evalFn,_mbRng) -> throwError (FailedToProve (assertMsg a))
          _     -> throwError (FailedToProve (assertMsg a))

  where a = gShows g

