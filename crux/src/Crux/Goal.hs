{-# Language ImplicitParams #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}

module Crux.Goal where

import Control.Lens ((^.), view)
import Control.Monad (forM_, unless, when)
import Data.Either (partitionEithers)
import Data.IORef
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as Text


import What4.Interface (notPred, printSymExpr,asConstantPred)
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check, getUnsatCore )
import What4.Protocol.SMTWriter( mkFormula, assumeFormulaWithFreshName
                               , assumeFormula, smtExprGroundEvalFn )
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, getSolverProcess )
import Lang.Crucible.Simulator.SimError
        ( SimError )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)

import Crux.Types
import Crux.Model
import Crux.Log
import Crux.Config.Common
import Crux.ProgressBar


-- | Simplify the proved goals.
provedGoalsTree ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver) fs
  , OnlineSolver s solver
  ) =>
  SimCtxt sym p ->
  Maybe (Goals (Assumption sym) (Assertion sym, ProofResult (Either (Assumption sym) (Assertion sym)))) ->
  IO (Maybe (ProvedGoals (Either AssumptionReason SimError)))
provedGoalsTree ctxt = traverse (go [])
  where
  go asmps gs =
    case gs of
      Assuming ps gs1 -> goAsmp asmps ps gs1

      Prove (p,r) -> return $ proveToGoal ctxt asmps p r

      ProveConj g1 g2 -> Branch <$> go asmps g1 <*> go asmps g2

  goAsmp asmps Seq.Empty gs = go asmps gs
  goAsmp asmps (ps Seq.:|> p) gs =
        case p ^. labeledPredMsg of
          ExploringAPath from to -> AtLoc from to <$> goAsmp (p : asmps) ps gs
          _                      -> goAsmp (p : asmps) ps gs


countGoals :: Goals a b -> Int
countGoals gs =
  case gs of
    Assuming _ gs1  -> countGoals gs1
    Prove _         -> 1
    ProveConj g1 g2 -> countGoals g1 + countGoals g2

countFailedGoals :: ProvedGoals a -> Int
countFailedGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countFailedGoals gs1
    Branch gs1 gs2 -> countFailedGoals gs1 + countFailedGoals gs2
    Goal _ _ _ (NotProved _) -> 1
    Goal _ _ _ (Proved _) -> 0

proveToGoal ::
  sym ~ ExprBuilder s (OnlineBackendState solver) fs =>
  SimCtxt sym p ->
  [Assumption sym] ->
  Assertion sym ->
  ProofResult (Either (Assumption sym) (Assertion sym)) ->
  ProvedGoals (Either AssumptionReason SimError)
proveToGoal _ allAsmps p pr =
  case pr of
    NotProved cex -> Goal (map showLabPred allAsmps) (showLabPred p) False (NotProved cex)
    Proved xs ->
      let xs' = map (either (Left . (view labeledPredMsg)) (Right . (view labeledPredMsg))) xs in
      case partitionEithers xs of
        (asmps, [])  -> Goal (map showLabPred asmps) (showLabPred p) True (Proved xs')
        (asmps, _:_) -> Goal (map showLabPred asmps) (showLabPred p) False (Proved xs')

 where
 showLabPred x = (x^.labeledPredMsg, show (printSymExpr (x^.labeledPred)))

-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
proveGoals ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver) fs
  , OnlineSolver s solver
  , ?outputConfig :: OutputConfig
  ) =>
  CruxOptions ->
  SimCtxt sym p ->
  Maybe (Goals (LPred sym asmp) (LPred sym ast)) ->
  IO (Maybe (Goals (LPred sym asmp) (LPred sym ast, ProofResult (Either (LPred sym asmp) (LPred sym ast)))))

proveGoals opts _ctxt Nothing =
  do case pathStrategy opts of
       AlwaysMergePaths -> sayOK "Crux" $ unwords [ "All goals discharged through internal simplification." ]
       _ -> return ()
     return Nothing

proveGoals opts ctxt (Just gs0) =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     goalNum <- newIORef (0,0,0) -- total, proved, disproved
     nameMap <- newIORef Map.empty
     unless hasUnsatCores $
      sayWarn "Crux" "Warning: skipping unsat cores because MC-SAT is enabled."
     res <- inNewFrame sp (go sp goalNum gs0 nameMap)
     (tot,proved,disproved) <- readIORef goalNum
     if proved /= tot
       then do
         sayFail "Crux" $ unwords
           [ "Disproved", show disproved
           , "out of", show tot, "goals."
           , show (tot - proved - disproved), "goals are unknown."
           ]
         if disproved > 0
           then sayFail "Crux" "Overall status: Invalid."
           else say "Crux" "Overall status: Unknown."
       else do
         sayOK "Crux" $ unwords [ "Proved all", show tot, "goals." ]
         sayOK "Crux" "Overall status: Valid."
     return (Just res)
  where
  (start,end) = prepStatus "Checking: " (countGoals gs0)

  bindName nm p nameMap = modifyIORef nameMap (Map.insert nm p)

  hasUnsatCores = not (yicesMCSat opts)

  failfast = proofGoalsFailFast opts

  go sp gn gs nameMap = do
    case gs of

      Assuming ps gs1 ->
        do forM_ ps $ \p ->
             unless (asConstantPred (p^.labeledPred) == Just True) $
              do nm <- doAssume =<< mkFormula conn (p ^. labeledPred)
                 bindName nm (Left p) nameMap
           res <- go sp gn gs1 nameMap
           return (Assuming ps res)

      Prove p ->
        do num <- atomicModifyIORef' gn (\(val,y,z) -> ((val + 1,y,z), val))
           start num
           let sym  = ctxt ^. ctxSymInterface
           nm <- doAssume =<< mkFormula conn =<< notPred sym (p ^. labeledPred)
           bindName nm (Right p) nameMap

           res <- check sp "proof"
           ret <- case res of
                      Unsat () ->
                        do modifyIORef' gn (\(x,u,s) -> (x,u+1,s))
                           namemap <- readIORef nameMap
                           core <- if hasUnsatCores
                                   then map (lookupnm namemap) <$> getUnsatCore sp
                                   else return (Map.elems namemap)
                           return (Prove (p, (Proved core)))

                      Sat ()  ->
                        do modifyIORef' gn (\(x,u,s) -> (x,u,s+1))
                           when failfast (sayOK "Crux" "Counterexample found, skipping remaining goals.")
                           f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           let model = ctxt ^. cruciblePersonality
                           vals <- evalModel f model
                           return (Prove (p, NotProved (Just (ModelView vals))))

                      Unknown -> return (Prove (p, NotProved Nothing))
           end
           return ret

      ProveConj g1 g2 ->
        do g1' <- inNewFrame sp (go sp gn g1 nameMap)
           -- NB, we don't need 'inNewFrame' here because
           --  we don't need to back up to this point again.

           if failfast then
             do (_,_,s) <- readIORef gn
                if s > 0 then
                  return g1'
                else
                  ProveConj g1' <$> go sp gn g2 nameMap
           else
             ProveConj g1' <$> go sp gn g2 nameMap

    where
    conn = solverConn sp

    lookupnm namemap x =
      fromMaybe (error $ "Named predicate " ++ show x ++ " not found!")
                (Map.lookup x namemap)

    doAssume formula = do
      namemap <- readIORef nameMap
      if hasUnsatCores
      then assumeFormulaWithFreshName conn formula
      else assumeFormula conn formula >> return (Text.pack ("x" ++ show (Map.size namemap)))

