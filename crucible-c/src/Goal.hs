module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)

import Lang.Crucible.Solver.BoolInterface
        ( IsBoolExprBuilder
        , Pred, notPred,impliesPred
        , Assertion, assertPred, assertMsg
        )
import Lang.Crucible.Solver.Adapter(SolverAdapter(..))
import Lang.Crucible.Solver.SatResult(SatResult(..))
import Lang.Crucible.Solver.OnlineBackend
        (OnlineBackend,yicesOnlineAdapter,OnlineBackendState)

import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, simConfig, cruciblePersonality)


import Error
import Types
import Model


prover :: SolverAdapter (OnlineBackendState s)
prover = yicesOnlineAdapter

data Goal sym = Goal
  { gAssumes :: [Pred sym]
  , gShows   :: Assertion (Pred sym)
  }

mkGoal :: ([Pred sym], Assertion (Pred sym)) -> Goal sym
mkGoal (as,p) = Goal { gAssumes = as, gShows = p }

obligGoal :: IsBoolExprBuilder sym => sym -> Goal sym -> IO (Pred sym)
obligGoal sym g = foldM imp (gShows g ^. assertPred) (gAssumes g)
  where
  imp p a = impliesPred sym a p

proveGoal ::
  SimCtxt (OnlineBackend s t) arch ->
  Goal (OnlineBackend s t) ->
  IO ()
proveGoal ctxt g =
  do let sym = ctxt ^. ctxSymInterface
         cfg = simConfig ctxt
     p <- notPred sym =<< obligGoal sym g

     let say _n _x = return () -- putStrLn ("[" ++ show n ++ "] " ++ x)
     solver_adapter_check_sat prover sym cfg say p $ \res ->
        case res of
          Unsat -> return ()
          Sat (evalFn,_mbRng) ->
            do let model = ctxt ^. cruciblePersonality
               str <- ppModel evalFn model
               throwError (FailedToProve (assertMsg a) (Just str))
          _     -> throwError (FailedToProve (assertMsg a) Nothing)

  where a = gShows g



