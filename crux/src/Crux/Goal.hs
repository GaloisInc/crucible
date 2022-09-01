{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# Language ImplicitParams #-}
{-# Language MultiWayIf #-}
{-# Language PatternSynonyms #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeFamilies #-}
{-# Language ViewPatterns #-}

module Crux.Goal where

import Control.Concurrent.Async (async, asyncThreadId, waitAnyCatch)
import Control.Exception (throwTo, SomeException, displayException)
import Control.Lens ((^.), view)

import Control.Monad (forM, forM_, unless, when)
import Data.Either (partitionEithers)
import Data.IORef
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Parameterized.Map as MapF
import qualified Data.Text as Text
import           Data.Void
import           Prettyprinter
import           System.Exit (ExitCode(ExitSuccess))
import qualified System.Timeout as ST

import What4.Interface (notPred, getConfiguration, IsExprBuilder)
import What4.Config (setOpt, getOptionSetting, Opt, ConfigOption)
import What4.ProgramLoc (ProgramLoc)
import What4.SatResult(SatResult(..))
import What4.Expr (ExprBuilder, GroundEvalFn(..), BoolExpr, GroundValueWrapper(..))
import What4.Protocol.Online( OnlineSolver, inNewFrame, inNewFrame2Open
                            , inNewFrame2Close, solverEvalFuns, solverConn
                            , check, getUnsatCore, getAbducts )
import What4.Protocol.SMTWriter( mkFormula, assumeFormulaWithFreshName
                               , assumeFormula, smtExprGroundEvalFn )
import qualified What4.Solver as WS
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
        ( OnlineBackend, withSolverProcess, enableOnlineBackend, solverInteractionFile )
import Lang.Crucible.Simulator.SimError
        ( SimError(..), SimErrorReason(..) )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface)
import Lang.Crucible.Panic (panic)

import Crux.Types
import Crux.Model
import Crux.Log as Log
import Crux.Config.Common
import Crux.ProgressBar


symCfg :: (IsExprBuilder sym, Opt t a) => sym -> ConfigOption t -> a -> IO ()
symCfg sym x y =
  do opt <- getOptionSetting x (getConfiguration sym)
     _   <- setOpt opt y
     pure ()


-- | Simplify the proved goals.
provedGoalsTree :: forall sym.
  ( IsSymInterface sym
  ) =>
  sym ->
  Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym)) ->
  IO (Maybe ProvedGoals)
provedGoalsTree sym = traverse (go mempty)
  where
  go :: Assumptions sym ->
        Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym) ->
        IO ProvedGoals
  go asmps gs =
    case gs of
      Assuming as gs1 -> go (asmps <> as) gs1
      Prove (p,locs,r) -> proveToGoal sym asmps p locs r
      ProveConj g1 g2 -> Branch <$> go asmps g1 <*> go asmps g2

proveToGoal ::
  (IsSymInterface sym) =>
  sym ->
  Assumptions sym ->
  Assertion sym ->
  [ProgramLoc] ->
  ProofResult sym ->
  IO ProvedGoals
proveToGoal sym allAsmps p locs pr =
  case pr of
    NotProved ex cex s ->
      do as <- flattenAssumptions sym allAsmps
         return (NotProvedGoal (map showAsmp as) (showGoal p) ex locs cex s)
    Proved xs ->
      case partitionEithers xs of
        (asmps, [])  -> return (ProvedGoal (map showAsmp asmps) (showGoal p) locs True)
        (asmps, _:_) -> return (ProvedGoal (map showAsmp asmps) (showGoal p) locs False)

 where
 showAsmp x = forgetAssumption x
 showGoal x = x^.labeledPredMsg


countGoals :: Goals a b -> Int
countGoals gs =
  case gs of
    Assuming _ gs1  -> countGoals gs1
    Prove _         -> 1
    ProveConj g1 g2 -> countGoals g1 + countGoals g2

isResourceExhausted :: LabeledPred p SimError -> Bool
isResourceExhausted (view labeledPredMsg -> SimError _ (ResourceExhausted _)) = True
isResourceExhausted _ = False

updateProcessedGoals ::
  LabeledPred p SimError ->
  ProofResult a ->
  ProcessedGoals ->
  ProcessedGoals
updateProcessedGoals _ (Proved _) pgs =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs
     , provedGoals = 1 + provedGoals pgs
     }

updateProcessedGoals res (NotProved _ _ _) pgs | isResourceExhausted res =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs
     , incompleteGoals = 1 + incompleteGoals pgs
     }

updateProcessedGoals _ (NotProved _ (Just _) _) pgs =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs
     , disprovedGoals = 1 + disprovedGoals pgs
     }

updateProcessedGoals _ (NotProved _ Nothing _) pgs =
  pgs{ totalProcessedGoals = 1 + totalProcessedGoals pgs }

-- | A function that can be used to generate a pretty explanation of a
-- simulation error.

type Explainer sym t ann = Maybe (GroundEvalFn t)
                           -> LPred sym SimError
                           -> IO (Doc ann)

type ProverCallback sym =
  forall ext personality t st fs.
    (sym ~ ExprBuilder t st fs) =>
    CruxOptions ->
    SimCtxt personality sym ext ->
    Explainer sym t Void ->
    Maybe (Goals (Assumptions sym) (Assertion sym)) ->
    IO (ProcessedGoals, Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym)))

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
proveGoalsOffline :: forall st sym p t fs personality msgs.
  ( sym ~ ExprBuilder t st fs
  , Logs msgs
  , SupportsCruxLogMessage msgs
  ) =>
  [WS.SolverAdapter st] ->
  CruxOptions ->
  SimCtxt personality sym p ->
  (Maybe (GroundEvalFn t) -> Assertion sym -> IO (Doc Void)) ->
  Maybe (Goals (Assumptions sym) (Assertion sym)) ->
  IO (ProcessedGoals, Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym)))
proveGoalsOffline _adapter _opts _ctx _explainFailure Nothing = return (ProcessedGoals 0 0 0 0, Nothing)
proveGoalsOffline adapters opts ctx explainFailure (Just gs0) = do
  goalNum <- newIORef (ProcessedGoals 0 0 0 0)
  (start,end,finish) <- proverMilestoneCallbacks gs0
  gs <- go (start,end) goalNum mempty gs0
  nms <- readIORef goalNum
  finish
  return (nms, Just gs)

  where
    sym = ctx^.ctxSymInterface

    failfast = proofGoalsFailFast opts

    go :: SupportsCruxLogMessage msgs
       => (ProverMilestoneStartGoal, ProverMilestoneEndGoal)
       -> IORef ProcessedGoals
       -> Assumptions sym
       -> Goals (Assumptions sym) (Assertion sym)
       -> IO (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym))
    go (start,end) goalNum assumptionsInScope gs =
      case gs of
        Assuming ps gs1 -> do
          res <- go (start,end) goalNum (assumptionsInScope <> ps) gs1
          return (Assuming ps res)

        ProveConj g1 g2 -> do
          g1' <- go (start,end) goalNum assumptionsInScope g1
          numDisproved <- disprovedGoals <$> readIORef goalNum
          if failfast && numDisproved > 0
            then return g1'
            else ProveConj g1' <$> go (start,end) goalNum assumptionsInScope g2

        Prove p -> do
          goalNumber <- totalProcessedGoals <$> readIORef goalNum
          start goalNumber

          -- Conjoin all of the in-scope assumptions, the goal, then negate and
          -- check sat with the adapter
          assumptions <- assumptionsPred sym assumptionsInScope
          goal <- notPred sym (p ^. labeledPred)

          res <- dispatchSolversOnGoalAsync (goalTimeout opts) adapters
                           (runOneSolver p assumptionsInScope assumptions goal)
          end goalNumber
          case res of
            Right Nothing -> do
              let details = NotProved "(timeout)" Nothing []
              let locs = assumptionsTopLevelLocs assumptionsInScope
              modifyIORef' goalNum (updateProcessedGoals p details)
              return (Prove (p, locs, details))

            Right (Just (locs,details)) -> do
              modifyIORef' goalNum (updateProcessedGoals p details)
              case details of
                NotProved _ (Just _) _ ->
                  when (failfast && not (isResourceExhausted p)) $
                    sayCrux Log.FoundCounterExample
                _ -> return ()
              return (Prove (p, locs, details))
            Left es -> do
              modifyIORef' goalNum (updateProcessedGoals p (NotProved mempty Nothing []))
              let allExceptions = unlines (displayException <$> es)
              fail allExceptions

    runOneSolver :: Assertion sym
                 -> Assumptions sym
                 -> BoolExpr t
                 -> BoolExpr t
                 -> WS.SolverAdapter st
                 -> IO ([ProgramLoc], ProofResult sym)
    runOneSolver p assumptionsInScope assumptions goal adapter = do
      -- NOTE: We don't currently provide a method for capturing the output
      -- sent to offline solvers.  We would probably want a file per goal per adapter.
      let logData = WS.defaultLogData
      WS.solver_adapter_check_sat adapter (ctx ^. ctxSymInterface) logData [assumptions, goal] $ \satRes ->
        case satRes of
          Unsat _ -> do
            -- NOTE: We don't have an easy way to get an unsat core here
            -- because we don't have a solver connection.
            as <- flattenAssumptions sym assumptionsInScope
            let core = fmap Left as ++ [ Right p ]
            let locs = assumptionsTopLevelLocs assumptionsInScope
            return (locs, Proved core)
          Sat (evalFn, _) -> do
            evs  <- concretizeEvents (groundEval evalFn) assumptionsInScope
            let vals = evalModelFromEvents evs
            explain <- explainFailure (Just evalFn) p
            let locs = map eventLoc evs
            return (locs, NotProved explain (Just (vals,evs)) [])
          Unknown -> do
            explain <- explainFailure Nothing p
            let locs = assumptionsTopLevelLocs assumptionsInScope
            return (locs, NotProved explain Nothing [])

evalModelFromEvents :: [CrucibleEvent GroundValueWrapper] -> ModelView
evalModelFromEvents evs = ModelView (foldl f (modelVals emptyModelView) evs)
 where
   f m (CreateVariableEvent loc nm tpr (GVW v)) = MapF.insertWith jn tpr (Vals [Entry nm loc v]) m
   f m _ = m

   jn (Vals new) (Vals old) = Vals (old++new)

dispatchSolversOnGoalAsync :: forall a b s time.
                              (RealFrac time)
                           => Maybe time
                           -> [WS.SolverAdapter s]
                           -> (WS.SolverAdapter s -> IO (b,ProofResult a))
                           -> IO (Either [SomeException] (Maybe (b,ProofResult a)))
dispatchSolversOnGoalAsync mtimeoutSeconds adapters withAdapter = do
  asyncs <- forM adapters (async . withAdapter)
  await asyncs []
  where
    await [] es = return $ Left es
    await as es = do
      mresult <- withTimeout $ waitAnyCatch as
      case mresult of
        Just (a, result) -> do
          let as' = filter (/= a) as
          case result of
            Left  exc ->
              await as' (exc : es)
            Right (x, r@(Proved _)) -> do
              mapM_ kill as'
              return $ Right (Just (x,r))
            Right (x,r@(NotProved _ (Just _) _)) -> do
              mapM_ kill as'
              return $ Right (Just (x,r))
            Right _ ->
              await as' es
        Nothing -> do
          mapM_ kill as
          return $ Right $ Nothing

    withTimeout action
      | Just seconds <- mtimeoutSeconds = ST.timeout (round seconds * 1000000) action
      | otherwise = Just <$> action

    -- `cancel` from async blocks until the canceled thread has terminated.
    kill a = throwTo (asyncThreadId a) ExitSuccess


-- | Returns three actions, called respectively when the proving process for a
-- goal is started, when it is ended, and when the final goal is solved.  These
-- handlers should handle all necessary output / notifications to external
-- observers, based on the run options.
proverMilestoneCallbacks ::
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  Goals asmp ast -> IO ProverMilestoneCallbacks
proverMilestoneCallbacks goals = do
  (start, end, finish) <-
    if view quiet ?outputConfig then
      return silentProverMilestoneCallbacks
    else
      prepStatus "Checking: " (countGoals goals)
  return
    ( start <> sayCrux . Log.StartedGoal
    , end <> sayCrux . Log.EndedGoal
    , finish
    )


-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
--
-- NOTE: This function takes an explicit symbolic backend as an argument, even
-- though the symbolic backend used for symbolic execution is available in the
-- 'SimCtxt'.  We do that so that we can use separate solvers for path
-- satisfiability checking and goal discharge.
proveGoalsOnline ::
  ( sym ~ ExprBuilder s st fs
  , OnlineSolver goalSolver
  , Logs msgs
  , SupportsCruxLogMessage msgs
  ) =>
  OnlineBackend goalSolver s st fs ->
  CruxOptions ->
  SimCtxt personality sym p ->
  (Maybe (GroundEvalFn s) -> Assertion sym -> IO (Doc Void)) ->
  Maybe (Goals (Assumptions sym) (Assertion sym)) ->
  IO (ProcessedGoals, Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym)))
proveGoalsOnline _ _opts _ctxt _explainFailure Nothing =
     return (ProcessedGoals 0 0 0 0, Nothing)

proveGoalsOnline bak opts _ctxt explainFailure (Just gs0) =
  do 
     -- send solver interactions to the correct file
     mapM_ (symCfg sym solverInteractionFile) (fmap Text.pack (onlineSolverOutput opts))
     -- initial goal count
     goalNum <- newIORef (ProcessedGoals 0 0 0 0)
     -- nameMap is a mutable ref to a map from Text to Either (Assumption sym) (Assertion sym)
     nameMap <- newIORef Map.empty
     when (unsatCores opts && yicesMCSat opts) $
       sayCrux Log.SkippingUnsatCoresBecauseMCSatEnabled
     -- callbacks for starting a goal, ending a goal, and finishing all goals
     (start,end,finish) <- proverMilestoneCallbacks gs0
     -- make sure online features are enabled
     enableOpt <- getOptionSetting enableOnlineBackend (getConfiguration sym)
     _ <- setOpt enableOpt True
     -- @go@ traverses a proof tree, processing/solving each goal as it traverses it.
     -- It also updates goal count and nameMap
     res <- withSolverProcess bak (panic "proveGoalsOnline" ["Online solving not enabled!"]) $ \sp ->
              inNewFrame sp (go (start,end) sp mempty goalNum gs0 nameMap)
     nms <- readIORef goalNum
     finish
     return (nms, Just res)

  where
  sym = backendGetSym bak

  bindName nm p nameMap = modifyIORef nameMap (Map.insert nm p)

  hasUnsatCores = unsatCores opts && not (yicesMCSat opts)

  howManyAbducts = fromMaybe 0 (getNAbducts opts)

  failfast = proofGoalsFailFast opts

  go (start,end) sp assumptionsInScope gn gs nameMap = do
    -- traverse goal tree
    case gs of
      -- case: assumption in context for all the contained goals
      Assuming asms gs1 ->
        do ps <- flattenAssumptions sym asms
           forM_ ps $ \asm ->
             unless (trivialAssumption asm) $
               -- extract predicate from assumption
               do let p = assumptionPred asm
                  -- create formula, assert to SMT solver, create new name and add to nameMap
                  nm <- doAssume =<< mkFormula conn p
                  bindName nm (Left asm) nameMap
           -- recursive call
           res <- go (start,end) sp (assumptionsInScope <> asms) gn gs1 nameMap
           return (Assuming (mconcat (map singleAssumption ps)) res)
      -- case: proof obligation in the context of all previously-made assumptions
      Prove p ->
        -- number of processed goals gives goal number to prove
        do goalNumber <- totalProcessedGoals <$> readIORef gn
           start goalNumber
           -- negate goal, create formula
           t <- mkFormula conn =<< notPred sym (p ^. labeledPred)
           -- assert formula to SMT solver, create new name and add to nameMap.
           -- This is done in a new assertion frame if abduction is turned on since
           -- this assertion would need to be removed before asking for abducts
           if howManyAbducts /= 0 then
             inNewFrame2Open sp
           else
             return ()
           nm <- doAssume t
           bindName nm (Right p) nameMap
           -- check-sat with SMT solver, pattern match on result
           res <- check sp "proof"
           ret <- case res of
                      Unsat () ->
                        -- build unsat core, which is the entire assertion set by default
                        do namemap <- readIORef nameMap
                           core <- if hasUnsatCores then
                                      map (lookupnm namemap) <$> getUnsatCore sp
                                   -- default unsat core: entire assertion set
                                   else return (Map.elems namemap)
                           end goalNumber
                           let pr = Proved core
                           -- update goal count
                           modifyIORef' gn (updateProcessedGoals p pr)
                           
                           let locs = assumptionsTopLevelLocs assumptionsInScope
                           if howManyAbducts /= 0 then
                             inNewFrame2Close sp
                           else
                             return ()
                           return (Prove (p, locs, pr))
                      Sat ()  ->
                        do -- evaluate counter-example
                           f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           evs <- concretizeEvents (groundEval f) assumptionsInScope
                           let vals = evalModelFromEvents evs
                           explain <- explainFailure (Just f) p
                           end goalNumber
                           -- close the frame in which the final assertion and its 
                           -- checksat call were made, and then get the abducts
                           if howManyAbducts /= 0 then
                             do inNewFrame2Close sp
                           else return ()
                           abds <- if howManyAbducts /= 0 then 
                                     getAbducts sp (fromIntegral howManyAbducts) "abd" (p ^. labeledPred)
                                   else
                                     return []
                           let gt = NotProved explain (Just (vals,evs)) abds
                           -- update goal count
                           modifyIORef' gn (updateProcessedGoals p gt)
                           when (failfast && not (isResourceExhausted p)) $
                             sayCrux Log.FoundCounterExample
                           let locs = map eventLoc evs
                           return (Prove (p, locs, gt))
                      Unknown ->
                        do explain <- explainFailure Nothing p
                           end goalNumber
                           let gt = NotProved explain Nothing []
                           modifyIORef' gn (updateProcessedGoals p gt)
                           let locs = assumptionsTopLevelLocs assumptionsInScope
                           inNewFrame2Close sp
                           return (Prove (p, locs, gt))
           return ret
      -- case: conjunction of goals
      ProveConj g1 g2 ->
        do g1' <- inNewFrame sp (go (start,end) sp assumptionsInScope gn g1 nameMap)
           -- NB, we don't need 'inNewFrame' here because
           --  we don't need to back up to this point again.
           if failfast then
             do numDisproved <- disprovedGoals <$> readIORef gn
                if numDisproved > 0 then
                  return g1'
                else
                  ProveConj g1' <$> go (start,end) sp assumptionsInScope gn g2 nameMap
           else
             ProveConj g1' <$> go (start,end) sp assumptionsInScope gn g2 nameMap

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
