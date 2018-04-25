module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)

import Lang.Crucible.Solver.SimpleBuilder(SimpleBuilder)
import Lang.Crucible.Solver.Adapter(SolverAdapter(..))
import Lang.Crucible.Solver.BoolInterface(IsBoolExprBuilder, Pred)
import Lang.Crucible.Solver.SimpleBackend.Z3(z3Adapter)
import Lang.Crucible.Solver.SatResult(SatResult(..))


import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, simConfig, cruciblePersonality)

import Lang.Crucible.Solver.BoolInterface
        (notPred,impliesPred, Assertion, assertPred, assertMsg)

import Error
import Types
import Model


prover :: SolverAdapter s
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
  SimCtxt (SimpleBuilder t st) arch ->
  Goal (SimpleBuilder t st) ->
  IO ()
proveGoal ctxt g =
  do let sym = ctxt ^. ctxSymInterface
         cfg = simConfig ctxt
     p <- notPred sym =<< obligGoal sym g

     let say n x = putStrLn ("[" ++ show n ++ "] " ++ x)
     solver_adapter_check_sat prover sym cfg say p $ \res ->
        case res of
          Unsat -> return ()
          Sat (evalFn,_mbRng) ->
            do let model = ctxt ^. cruciblePersonality
               str <- ppModel evalFn model
               throwError (FailedToProve (assertMsg a) (Just str))
          _     -> throwError (FailedToProve (assertMsg a) Nothing)

  where a = gShows g



