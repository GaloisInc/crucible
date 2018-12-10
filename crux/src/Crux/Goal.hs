{-# Language ImplicitParams #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}

module Crux.Goal where

import Control.Lens ((^.), view)
import Control.Monad (forM_, unless)
import Data.Either (partitionEithers)
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Sequence as Seq


import What4.Interface (notPred, printSymExpr,asConstantPred)
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check, getUnsatCore )
import What4.Protocol.SMTWriter(mkFormula,assumeFormulaWithFreshName,smtExprGroundEvalFn)

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
  SimCtxt sym p ->
  Maybe (Goals (LPred sym asmp) (LPred sym ast)) ->
  IO (Maybe (Goals (LPred sym asmp) (LPred sym ast, ProofResult (Either (LPred sym asmp) (LPred sym ast)))))

proveGoals _ctxt Nothing =
  do -- sayOK "Crux" $ unwords [ "No goals to prove." ]
     return Nothing

proveGoals ctxt (Just gs0) =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     goalNum <- newIORef (0,0) -- total, proved
     nameMap <- newIORef Map.empty
     res <- inNewFrame sp (go sp goalNum gs0 nameMap)
     (tot,proved) <- readIORef goalNum
     if proved /= tot
       then sayFail "Crux" $ unwords
             [ "Failed to prove", show (tot - proved)
             , "out of", show tot, "goals." ]
       else sayOK "Crux" $ unwords [ "Proved all", show tot, "goals." ]
     return (Just res)
  where
  (start,end) = prepStatus "Checking: " (countGoals gs0)

  bindName nm p nameMap = modifyIORef nameMap (Map.insert nm p)

  go sp gn gs nameMap =
    case gs of

      Assuming ps gs1 ->
        do forM_ ps $ \p ->
             unless (asConstantPred (p^.labeledPred) == Just True) $
              do nm <- assumeFormulaWithFreshName conn =<< mkFormula conn (p ^. labeledPred)
                 bindName nm (Left p) nameMap
           res <- go sp gn gs1 nameMap
           return (Assuming ps res)

      Prove p ->
        do num <- atomicModifyIORef' gn (\(val,y) -> ((val + 1,y), val))
           start num
           let sym  = ctxt ^. ctxSymInterface
           nm <- assumeFormulaWithFreshName conn
                    =<< mkFormula conn =<< notPred sym (p ^. labeledPred)
           bindName nm (Right p) nameMap

           res <- check sp "proof"
           ret <- case res of
                      Unsat () ->
                        do modifyIORef' gn (\(x,f) -> (x,f+1))
                           core <- getUnsatCore sp
                           namemap <- readIORef nameMap
                           let core' = map (lookupnm namemap) core
                           return (Prove (p, (Proved core')))

                      Sat ()  ->
                        do f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           let model = ctxt ^. cruciblePersonality
                           str <- ppModel f model
                           return (Prove (p, NotProved (Just str)))

                      Unknown -> return (Prove (p, NotProved Nothing))
           end
           return ret

      ProveConj g1 g2 ->
        do g1' <- inNewFrame sp (go sp gn g1 nameMap)
           -- NB, we don't need 'inNewFrame' here because
           --  we don't need to back up to this point again.
           g2' <- go sp gn g2 nameMap
           return (ProveConj g1' g2')

    where
    conn = solverConn sp

    lookupnm namemap x =
      case Map.lookup x namemap of
        Just v  -> v
        Nothing -> error $ "Named predicate " ++ show x ++ " not found!"
