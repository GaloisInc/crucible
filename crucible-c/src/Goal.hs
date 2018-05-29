module Goal where

import Control.Lens((^.))
import Control.Monad(foldM)
import Text.PrettyPrint.ANSI.Leijen(pretty)
import System.Directory(createDirectoryIfMissing)
import System.FilePath((</>))
import Data.Foldable(toList)

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
import Options
import Clang


-- XXX: Change
obligGoal :: IsExprBuilder sym => sym -> ProofObligation sym -> IO (Pred sym)
obligGoal sym g = foldM imp (proofGoal g ^. labeledPred)
                            (proofAssumptions g)
  where
  imp p a = impliesPred sym (a ^. labeledPred) p

proveGoal ::
  OnlineSolver s solver =>
  Options ->
  SimCtxt (ExprBuilder s (OnlineBackendState solver)) arch ->
  (String, ProofObligation (ExprBuilder s (OnlineBackendState solver))) ->
  IO ()
proveGoal opts ctxt (num,g) =
  do let sym = ctxt ^. ctxSymInterface
     let dir = outDir opts </> ("goal_" ++ num)
     createDirectoryIfMissing True dir

     let opts1 = opts { outDir = dir }
     describe opts1 g
     g1 <- obligGoal sym g
     p  <- notPred sym g1
     sp <- getSolverProcess sym

     checkSatisfiableWithModel sp p $ \res ->
        case res of
          Unsat -> do writeFile (dir </> "status") "proved"
                      return ()
          Sat evalFn ->
            do writeFile (dir </> "status") "not proved"
               let model = ctxt ^. cruciblePersonality
               str <- ppModel evalFn model
               buildModelExes opts1 str
          _  -> writeFile (dir </> "status") "not proved"

  where
  a = proofGoal g

describe :: Options ->
            ProofObligation (ExprBuilder s (OnlineBackendState solver)) -> IO()
describe opts o =
  do ppConc (proofGoal o)
     mapM_ ppAsmp (zip [ 1 .. ] (toList (proofAssumptions o)))
  where
  ppAsmp (n,a) =
    inFile ("assumption-" ++ show (n::Int))
      $ case a ^. labeledPredMsg of
          AssumptionReason l s -> sh l ++ ": " ++ s
          ExploringAPath l -> sh l ++ ": Exploring path"
          AssumingNoError x -> sh l ++ ": Avoided failure"
             where l = simErrorLoc x

  sh l = show (pretty (plSourceLoc l))

  ppConc x = inFile "goal" (show (x ^. labeledPredMsg))

  inFile x y = writeFile (outDir opts </> x) y

