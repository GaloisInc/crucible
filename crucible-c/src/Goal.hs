module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)
import Text.PrettyPrint.ANSI.Leijen(pretty)

import What4.Interface
        (IsExprBuilder, Pred, notPred, impliesPred)
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver )
import What4.ProgramLoc(ProgramLoc(..))

import Lang.Crucible.Backend
        ( ProofObligation, labeledPredMsg, labeledPred
        , AssumptionReason(..), ProofGoal(..) )
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, checkSatisfiableWithModel, getSolverProcess )
import Lang.Crucible.Simulator.SimError
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)

import Error
import Types
import Model
import Log


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
     describe g
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

describe :: ProofObligation (ExprBuilder s (OnlineBackendState solver)) -> IO()
describe o =
  do putStrLn "-- Trying to avoid:"
     ppConc (proofGoal o)
     putStrLn "-- Using assumptions:"
     mapM_ ppAsmp (proofAssumptions o)
  where
  ppAsmp a = case a ^. labeledPredMsg of
               AssumptionReason l s ->
                  putStrLn (sh l ++ ": " ++ s)
               ExploringAPath l ->
                  putStrLn (sh l ++ ": Exploring path")
               AssumingNoError x ->
                  putStrLn (sh l ++ ": Avoided failure")
                  where l = simErrorLoc x

  sh l = show (pretty (plSourceLoc l))

  ppConc x = print (x ^. labeledPredMsg)


proveGoals ::
  OnlineSolver s solver =>
  SimCtxt (ExprBuilder s (OnlineBackendState solver)) arch ->
  [ProofObligation (ExprBuilder s (OnlineBackendState solver))] ->
  IO (Maybe Error)
proveGoals ctx gs =
  case gs of
    [] -> return Nothing
    g : others ->
      do mb <- proveGoal ctx g
         case mb of
           Nothing -> do sayOK "Crux" "Success"
                         putStrLn "------------"
                         proveGoals ctx others
           Just e  -> return (Just e)



