module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)

-- import Lang.Crucible.Solver.Interface(printSymExpr)
import Lang.Crucible.Solver.BoolInterface
        ( IsBoolExprBuilder
        , Pred, notPred,impliesPred
        , Assertion, assertPred, assertMsg, assertLoc
        )
import Lang.Crucible.Solver.Adapter(SolverAdapter(..))
import Lang.Crucible.Solver.SatResult(SatResult(..))
import Lang.Crucible.Solver.SimpleBuilder (SimpleBuilder)
import Lang.Crucible.Solver.SimpleBackend.Z3(z3Adapter)
-- import Lang.Crucible.Solver.SimpleBackend.Yices(yicesAdapter)

import Lang.Crucible.Simulator.SimError(SimErrorReason(..))
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, simConfig, cruciblePersonality)


import Error
import Types
import Model


prover :: SolverAdapter s
prover = z3Adapter
--prover = yicesAdapter

data Goal sym = Goal
  { gAssumes :: [Pred sym]
  , gShows   :: Assertion (Pred sym)
  }

-- Check assertions before other things
goalPriority :: Goal sym -> Int
goalPriority g =
  case assertMsg (gShows g) of
    Just (AssertFailureSimError {}) -> 0
    _ -> 1

mkGoal :: ([Pred sym], Assertion (Pred sym)) -> Goal sym
mkGoal (as,p) = Goal { gAssumes = as, gShows = p }

obligGoal :: IsBoolExprBuilder sym => sym -> Goal sym -> IO (Pred sym)
obligGoal sym g = foldM imp (gShows g ^. assertPred) (gAssumes g)
  where
  imp p a = impliesPred sym a p

proveGoal ::
  SimCtxt (SimpleBuilder s t) arch ->
  Goal (SimpleBuilder s t) ->
  IO ()
proveGoal ctxt g =
  do let sym = ctxt ^. ctxSymInterface
         cfg = simConfig ctxt
     g1 <- obligGoal sym g
     p <- notPred sym g1

     let say _n _x = return () -- putStrLn ("[" ++ show _n ++ "] " ++ _x)
     solver_adapter_check_sat prover sym cfg say p $ \res ->
        case res of
          Unsat -> return ()
          Sat (evalFn,_mbRng) ->
            do let model = ctxt ^. cruciblePersonality
               str <- ppModel evalFn model
               giveUp (Just str)
          _  -> giveUp Nothing

  where
  a = gShows g
  giveUp mb = throwError (FailedToProve (assertLoc a) (assertMsg a) mb)



