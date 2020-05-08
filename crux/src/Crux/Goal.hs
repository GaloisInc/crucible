{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# Language ImplicitParams #-}
{-# Language MultiWayIf #-}
{-# Language PatternSynonyms #-}
{-# Language TypeFamilies #-}

module Crux.Goal where

import Control.Lens ((^.), view)
import qualified Control.Lens as L
import Control.Monad (forM_, unless, when)
import Data.Either (partitionEithers)
import qualified Data.Foldable as F
import Data.IORef
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified System.Timeout as ST


import What4.Interface (notPred, printSymExpr,asConstantPred)
import qualified What4.Interface as WI
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check, getUnsatCore )
import What4.Protocol.SMTWriter( mkFormula, assumeFormulaWithFreshName
                               , assumeFormula, smtExprGroundEvalFn )
import qualified What4.Solver as WS
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, withSolverProcess )
import Lang.Crucible.Simulator.SimError
        ( SimError(..), SimErrorReason(..) )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)

import Crux.Types
import Crux.Model
import Crux.Log
import Crux.Config.Common
import Crux.ProgressBar


-- | Simplify the proved goals.
provedGoalsTree ::
  ( IsSymInterface sym
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

countTotalGoals :: ProvedGoals a -> Int
countTotalGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countTotalGoals gs1
    Branch gs1 gs2 -> countTotalGoals gs1 + countTotalGoals gs2
    Goal _ _ _ _ -> 1

countDisprovedGoals :: ProvedGoals a -> Int
countDisprovedGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countDisprovedGoals gs1
    Branch gs1 gs2 -> countDisprovedGoals gs1 + countDisprovedGoals gs2
    Goal _ _ _ (NotProved (Just _)) -> 1
    Goal _ _ _ (NotProved Nothing) -> 0
    Goal _ _ _ (Proved _) -> 0

countUnknownGoals :: ProvedGoals a -> Int
countUnknownGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countUnknownGoals gs1
    Branch gs1 gs2 -> countUnknownGoals gs1 + countUnknownGoals gs2
    Goal _ _ _ (NotProved Nothing) -> 1
    Goal _ _ _ (NotProved (Just _)) -> 0
    Goal _ _ _ (Proved _) -> 0

countProvedGoals :: ProvedGoals a -> Int
countProvedGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countProvedGoals gs1
    Branch gs1 gs2 -> countProvedGoals gs1 + countProvedGoals gs2
    Goal _ _ _ (NotProved _) -> 0
    Goal _ _ _ (Proved _) -> 1

countIncompleteGoals :: ProvedGoals a -> Int
countIncompleteGoals gs =
  case gs of
    AtLoc _ _ gs1 -> countIncompleteGoals gs1
    Branch gs1 gs2 -> countIncompleteGoals gs1 + countIncompleteGoals gs2
    Goal _ (SimError _ (ResourceExhausted _), _) _ (NotProved Nothing) -> 1
    Goal _ _ _ _ -> 0

proveToGoal ::
  (IsSymInterface sym) =>
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

data ProcessedGoals =
  ProcessedGoals { totalProcessedGoals :: !Integer
                 , provedGoals :: !Integer
                 , disprovedGoals :: !Integer
                 }

-- | Discharge a tree of proof obligations ('Goals') by using a non-online solver
--
-- This function traverses the 'Goals' tree while keeping track of a collection
-- of assumptions in scope for each goal.  For each proof goal encountered in
-- the tree, it creates a fresh solver connection using the provided solver
-- adapter.
--
-- This is in contrast to 'proveGoalsOnline', which uses an online solver
-- connection with scoped assumption frames.  This function allows using a wider
-- variety of solvers (i.e., ones that don't have support for online solving)
-- and would in principle enable parallel goal evaluation (though the tree
-- structure makes that a bit trickier, it isn't too hard).
--
-- Note that this function uses the same symbolic backend ('ExprBuilder') as the
-- symbolic execution phase, which should not be a problem.
proveGoalsOffline :: forall st sym p asmp ast t
                   . (?outputConfig :: OutputConfig, sym ~ ExprBuilder t st, IsSymInterface sym)
                  => WS.SolverAdapter st
                  -> CruxOptions
                  -> SimCtxt sym p
                  -> Maybe (Goals (LPred sym asmp) (LPred sym ast))
                  -> IO (Maybe (Goals (LPred sym asmp) (LPred sym ast, ProofResult (Either (LPred sym asmp) (LPred sym ast)))))
proveGoalsOffline _adapter _opts _ctx Nothing = return Nothing
proveGoalsOffline adapter opts ctx (Just gs0) = do
  goalNum <- newIORef (ProcessedGoals 0 0 0)
  (start,end,finish) <-
     if view quiet ?outputConfig then
       return (\_ -> return (), return (), return ())
     else
       prepStatus "Checking: " (countGoals gs0)
  (Just <$> go (start,end) goalNum [] gs0) <* finish

  where
    withTimeout action
      | Just seconds <- goalTimeout opts = ST.timeout (round seconds * 1000000) action
      | otherwise = Just <$> action

    failfast = proofGoalsFailFast opts

    go :: (Integer -> IO (), IO ())
       -> IORef ProcessedGoals
       -> [Seq.Seq (LPred sym asmp)]
       -> Goals (LPred sym asmp) (LPred sym ast)
       -> IO (Goals (LPred sym asmp) (LPred sym ast, ProofResult (Either (LPred sym asmp) (LPred sym ast))))
    go (start,end) goalNum assumptionsInScope gs =
      case gs of
        Assuming ps gs1 -> do
          res <- go (start,end) goalNum (ps : assumptionsInScope) gs1
          return (Assuming ps res)

        ProveConj g1 g2 -> do
          g1' <- go (start,end) goalNum assumptionsInScope g1
          numDisproved <- disprovedGoals <$> readIORef goalNum
          if failfast && numDisproved > 0
            then return g1'
            else ProveConj g1' <$> go (start,end) goalNum assumptionsInScope g2

        Prove p -> do
          num <- atomicModifyIORef' goalNum (\pg -> (pg { totalProcessedGoals = totalProcessedGoals pg + 1 }, totalProcessedGoals pg))
          start num
          -- Conjoin all of the in-scope assumptions, the goal, then negate and
          -- check sat with the adapter
          let sym = ctx ^. ctxSymInterface
          assumptions <- WI.andAllOf sym (L.folded . id) (fmap (^. labeledPred) (mconcat assumptionsInScope))
          goal <- notPred sym (p ^. labeledPred)
          -- NOTE: We don't currently provide a method for capturing the output
          -- sent to offline solvers.  We would probably want a file per goal.
          let logData = WS.defaultLogData
          mres <- withTimeout $ WS.solver_adapter_check_sat adapter sym logData [assumptions, goal] $ \satRes ->
            case satRes of
              Unsat _ -> do
                modifyIORef' goalNum (\pg -> pg { provedGoals = provedGoals pg + 1 })
                -- NOTE: We don't have an easy way to get an unsat core here
                -- because we don't have a solver connection.
                let core = fmap Left (F.toList (mconcat assumptionsInScope))
                end
                return (Prove (p, Proved core))
              Sat (evalFn, _) -> do
                modifyIORef' goalNum (\pg -> pg { disprovedGoals = disprovedGoals pg + 1 })
                end
                when failfast $ sayOK "Crux" "Counterexample found, skipping remaining goals"
                let model = ctx ^. cruciblePersonality
                vals <- evalModel evalFn model
                return (Prove (p, NotProved (Just (ModelView vals))))
              Unknown -> end >> return (Prove (p, NotProved Nothing))
          case mres of
            Just res -> return res
            Nothing -> return (Prove (p, NotProved Nothing))



-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
--
-- NOTE: This function takes an explicit symbolic backend as an argument, even
-- though the symbolic backend used for symbolic execution is available in the
-- 'SimCtxt'.  We do that so that we can use separate solvers for path
-- satisfiability checking and goal discharge.
proveGoalsOnline ::
  ( sym ~ ExprBuilder (CrucibleBackend s fm) (OnlineBackendState solver)
  , IsSymInterface sym
  , OnlineSolver solver
  , goalSym ~ ExprBuilder (CrucibleBackend s fm) (OnlineBackendState goalSolver)
  , IsSymInterface goalSym
  , OnlineSolver goalSolver
  , ?outputConfig :: OutputConfig
  ) =>
  goalSym ->
  CruxOptions ->
  SimCtxt sym p ->
  Maybe (Goals (LPred sym asmp) (LPred sym ast)) ->
  IO (Maybe (Goals (LPred sym asmp) (LPred sym ast, ProofResult (Either (LPred sym asmp) (LPred sym ast)))))

proveGoalsOnline _ _opts _ctxt Nothing =
     return Nothing

proveGoalsOnline sym opts ctxt (Just gs0) =
  do goalNum <- newIORef (ProcessedGoals 0 0 0)
     nameMap <- newIORef Map.empty
     unless hasUnsatCores $
       sayWarn "Crux" "Warning: skipping unsat cores because MC-SAT is enabled."
     (start,end,finish) <-
       if view quiet ?outputConfig then
         return (\_ -> return (), return (), return ())
       else
         prepStatus "Checking: " (countGoals gs0)
     res <- withSolverProcess sym $ \sp ->
              inNewFrame sp (go (start,end) sp goalNum gs0 nameMap)
     finish
     return (Just res)
  where

  bindName nm p nameMap = modifyIORef nameMap (Map.insert nm p)

  hasUnsatCores = not (yicesMCSat opts)

  failfast = proofGoalsFailFast opts

  go (start,end) sp gn gs nameMap = do
    case gs of

      Assuming ps gs1 ->
        do forM_ ps $ \p ->
             unless (asConstantPred (p^.labeledPred) == Just True) $
              do nm <- doAssume =<< mkFormula conn (p ^. labeledPred)
                 bindName nm (Left p) nameMap
           res <- go (start,end) sp gn gs1 nameMap
           return (Assuming ps res)

      Prove p ->
        do num <- atomicModifyIORef' gn (\pg -> (pg { totalProcessedGoals = totalProcessedGoals pg + 1 }, totalProcessedGoals pg))
           start num
           nm <- doAssume =<< mkFormula conn =<< notPred sym (p ^. labeledPred)
           bindName nm (Right p) nameMap

           res <- check sp "proof"
           ret <- case res of
                      Unsat () ->
                        do modifyIORef' gn (\pg -> pg { provedGoals = provedGoals pg + 1 })
                           namemap <- readIORef nameMap
                           core <- if hasUnsatCores
                                   then map (lookupnm namemap) <$> getUnsatCore sp
                                   else return (Map.elems namemap)
                           end
                           return (Prove (p, (Proved core)))

                      Sat ()  ->
                        do modifyIORef' gn (\pg -> pg { disprovedGoals = disprovedGoals pg + 1 })
                           f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           let model = ctxt ^. cruciblePersonality
                           vals <- evalModel f model
                           end
                           when failfast (sayOK "Crux" "Counterexample found, skipping remaining goals.")
                           return (Prove (p, NotProved (Just (ModelView vals))))

                      Unknown -> end >> return (Prove (p, NotProved Nothing))
           return ret

      ProveConj g1 g2 ->
        do g1' <- inNewFrame sp (go (start,end) sp gn g1 nameMap)
           -- NB, we don't need 'inNewFrame' here because
           --  we don't need to back up to this point again.

           if failfast then
             do numDisproved <- disprovedGoals <$> readIORef gn
                if numDisproved > 0 then
                  return g1'
                else
                  ProveConj g1' <$> go (start,end) sp gn g2 nameMap
           else
             ProveConj g1' <$> go (start,end) sp gn g2 nameMap

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

