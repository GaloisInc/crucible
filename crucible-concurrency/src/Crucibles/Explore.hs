{- |
Module           : Crucibles.Explore
Description      : Provides an ExecutionFeature that is concurrency-aware
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

Provides an ExecutionFeature that is concurrency-aware.

The feature works by finding new states to explore, triggered by the execution
of _hooks_, functions in the program source designed to trigger certain behavior
in the scheduler.

For example, before a program accesses a global variable 'X', it should call a
function like 'crucibles_yield(X)', signaling to the scheduler that a global
access is about to occur. The scheduler uses this information to decide if the
current thread should be preempted or not.

The scheduler decisions in this module are actually parameterized by a
'SchedulingAlgorithm', which factors out the logic for determining which thread
should be selected after the execution of a given hook.
-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# LANGUAGE FlexibleContexts #-}
module Crucibles.Explore ( scheduleFeature, ppScheduler ) where

import           Control.Lens
import           Control.Monad (unless, when)
import           Control.Monad.IO.Class
import           Control.Monad.State (MonadState(..), StateT(..), evalStateT, gets)
import           Control.Monad.Reader (ReaderT(..))
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IntMap
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Text (Text)
import qualified Data.Vector as V

import Data.Foldable (foldlM)
import           GHC.Stack

import           Lang.Crucible.Backend
import           Lang.Crucible.FunctionHandle
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.Simulator
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Operations hiding (defaultAbortHandler)
import           Lang.Crucible.Simulator.EvalStmt
import           Lang.Crucible.Simulator.ExecutionTree
import           What4.Interface
import           What4.Config

import           Crucibles.Common
import           Crucibles.Execution
import           Crucibles.ExploreTypes
import           Crucibles.Scheduler
import           Crucibles.Primitives
import           Crucibles.SchedulingAlgorithm hiding (_exec, exec)
import Lang.Crucible.Simulator.GlobalState (insertGlobal, lookupGlobal)
import Data.Parameterized.Nonce (freshNonce)

type SchedulerConstraints sym ext alg =
  (?bound::Int, IsSymInterface sym, IsSyntaxExtension ext, SchedulingAlgorithm alg)

-- | Toplevel feature
scheduleFeature ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  ExplorePrimitives (ThreadExec alg sym ext ret) sym ext ->
  -- | Some primitives allow waiting on the value of _source-defined_ global variables,
  -- so the client can provide an assoc list of source variables here if they'd like. This can
  -- frequently be empty -- some of the crucible-syntax examples implement mutexes as global
  -- boolean variables, but this is likely not the right approach for most languages.
  [Some GlobalVar]  ->
  ExecutionFeature (ThreadExec alg sym ext ret) sym ext rtp
scheduleFeature prims =
  ExecutionFeature . schedule prims

-- | Determine the next state, which may involve running a new thread, suspending
-- the current one, performing some bookkeeping, or splitting a branch state into
-- a taken branch and a branch that we must backtrack to.
schedule ::
  forall alg sym ext ret rtp.
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  ExplorePrimitives (ThreadExec alg sym ext ret) sym ext ->
  [Some GlobalVar] ->
  ExecState (ThreadExec alg sym ext ret) sym ext rtp ->
  IO (ExecutionFeatureResult (ThreadExec alg sym ext ret) sym ext rtp)
schedule prims globs = \case
  CallState rh (CrucibleCall x cf) s ->
    scheduleCall prims globs rh x cf s

  SymbolicBranchState p tframe fframe _tgt s ->
    exploreNewState s $
      do me   <- use $ stateExpl.scheduler.activeThread
         curr <- use $ stateExec.currentEventID
         runUpdateSchedAlg $ notifyBranch (ThreadID me) curr
         stk <- use (stateTree.actContext)
         let save = BranchingThread p stk tframe fframe
         yieldThread globs save

  -- We're assuming here that we're being
  -- called from some toplevel override: if there's nothing else to do
  -- then we can terminate.
  ReturnState fnm (VFVCall (VFFEnd VFVEnd) frm k) val s
    | 0 == s ^. stateExpl.scheduler.activeThread ->
    do let newState = CompletedThread val
       maybeTerminate globs (ReturnState fnm (VFVCall (VFFEnd VFVEnd) frm k) val) newState s

  -- We tried to run a thread that isn't actually runnable. This is OK, because
  -- we might have conservatively added this thread to a backtracking list even
  -- though it wasn't actually runnable. In any case, restart the computation
  -- using the mainCont continuation.
  ResultState (AbortedResult ctx (AbortedExec _rsn _gps)) -> return (ExecutionFeatureNewState s0)
    where
      k  = ctx ^. cruciblePersonality.scheduler.to (\x -> mainCont x)
      t  = ctx ^. cruciblePersonality.scheduler.retRepr
      s0 = InitialState ctx emptyGlobals defaultAbortHandler t $ runOverrideSim t k

  -- TODO: I don't think this is reachable anymore, but this needs to be
  -- verified
  ResultState (FinishedResult ctx _) ->
    do let n   = ctx ^. cruciblePersonality.num
       let sym = ctx ^. ctxSymInterface
       verbOpt <- liftIO $ getOptionSetting verbosity $ getConfiguration sym
       verb    <- liftIO $ getOpt verbOpt
       when (verb > 2) $
         liftIO $ putStrLn $ "Explored " ++ show n ++ " executions."
       return $ ExecutionFeatureNoChange

  _ -> return ExecutionFeatureNoChange

  where
    exploreNewState s act =
      maybe ExecutionFeatureNoChange ExecutionFeatureNewState <$>
        do (a, _) <- runStateT act s
           return a

-- | Determine if we should do anything given a Call state.
scheduleCall ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  ExplorePrimitives (ThreadExec alg sym ext ret) sym ext ->
  [Some GlobalVar] ->
  ReturnHandler rty (ThreadExec alg sym ext ret) sym ext rtp f a {-^ rh of original CallState -} ->
  C.BlockID callBlocks ctx {-^ block of original CrucibleTarget -} ->
  (CallFrame sym ext callBlocks rty ctx) {-^ callframe of original CrucibleTarget -} ->
  SimState (ThreadExec alg sym ext ret) sym ext rtp f a {-^ SimState in which the CrucibleCall is executing -} ->
  IO (ExecutionFeatureResult (ThreadExec alg sym ext ret) sym ext rtp)
scheduleCall prims globs rh@(ReturnToCrucible tpr rest) x cf@CallFrame { _frameCFG = cfg } s =
  case matchPrimitive prims globs nm blkRepr cf (SomeSimState s) of
    Just (ThreadJoin tid) ->
      evalTEWithState s $
        (scheduleJoin globs (ThreadID (fromIntegral tid)) rh)

    Just (ThreadYield yieldSpec mods ro) ->
      evalTEWithState s $
        scheduleYield globs rh call yieldSpec mods ro

    Just (ThreadCondWait cv mv) ->
       let ts0 = saveThreadState (OnCond cv mv False) rh s
       in evalTEWithState s $
            (maybe ExecutionFeatureNoChange ExecutionFeatureNewState
               <$> yieldThread globs ts0)

    Just (ThreadCondSignal cv) ->
        evalTEWithState s $
          do stateExpl.scheduler.threads %= V.map (notifyThread cv)
             ts0 <- gets (saveThreadState (Resumable (Just (False, Set.singleton cv))) rh)
             s'  <- yieldThread globs ts0
             return $ maybe ExecutionFeatureNoChange ExecutionFeatureNewState s'

    Just (ThreadCreate ty retTy spawnRetTy fh arg mkRet)
     | Just Refl <- testEquality spawnRetTy tpr ->
         evalTEWithState s $
           scheduleThreadCreate ty retTy tpr fh arg mkRet rest
     | otherwise -> error "Unexpected return type for thread create primitive"


    Just (ThreadFinish (C.Some val)) ->
       maybeTerminate globs (CallState rh call) (CompletedThread val) s

    Nothing -> return ExecutionFeatureNoChange
  where
    nm       = handleName h
    h        = C.cfgHandle cfg
    blkRepr  = C.blockInputs (C.getBlock x (frameBlockMap cf))
    call     = CrucibleCall x cf
scheduleCall _ _ _ _ _ _ = return ExecutionFeatureNoChange

-- | Defer to another thread, or keep running if enabled & the joining thread
-- has already completed.
scheduleJoin ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  ThreadID ->
  ReturnHandler rty (ThreadExec alg sym ext ret) sym ext rtp (CrucibleLang blocks r) a ->
  ThreadExecM alg sym ext ret rtp (CrucibleLang blocks r) a
    (ExecutionFeatureResult (ThreadExec alg sym ext ret) sym ext rtp)
scheduleJoin globs tid rh =
  do ts0@(RunningThread _ rh' stk) <- gets (blockThreadOnJoin tid rh)
     mnext <- yieldThread globs ts0
     case mnext of
       Just ne ->
         return $ ExecutionFeatureNewState ne
       Nothing ->
         ExecutionFeatureNewState <$> restoreRunningThread rh' stk

-- | Possibly defer to another thread depending on the type of yield (which
-- indicates an access to some shared resource). We may not actually yield
-- control if we're merely giving up a lock.
scheduleYield ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  ReturnHandler rty (ThreadExec alg sym ext ret) sym ext rtp f a ->
  ResolvedCall (ThreadExec alg sym ext ret) sym ext rty {-^ The original call prompting the yield -} ->
  YieldSpec {-^ A description of what triggered the yield -} ->
  [Text] {-^ The accessed resources triggering the yield -}  ->
  Bool {-^ Is this a readonly access? Always safe to pass False here -} ->
  ThreadExecM alg sym ext ret rtp f a
    (ExecutionFeatureResult (ThreadExec alg sym ext ret) sym ext rtp)
scheduleYield globs rh call spec mods ro =
  case spec of
    SimpleYield ->
      runYield $ Resumable (Just (ro, modSet))

    GlobalPred predVar ->
      runYield $ OnPred modSet (ProgramVar predVar)

    Acquire l ->
      do initializeInternalGlobal l C.BoolRepr (return . truePred)
         runYield $ OnPred modSet (SchedulerVar l)

    Release l ->
      do setInternalGlobal l C.BoolRepr (return . truePred)
         es <- gets (CallState rh call)
         return $ ExecutionFeatureModifiedState es
  where
    modSet = Set.fromList mods

    runYield resumeCond =
      do ts0 <- gets (saveThreadState resumeCond rh)
         mes <- yieldThread globs ts0
         return $! maybe ExecutionFeatureNoChange ExecutionFeatureNewState mes

-- | Add a new executing thread.
scheduleThreadCreate ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  C.TypeRepr ty {-^ The type of the argument to newly executing thread -} ->
  C.TypeRepr retTy {-^ The return type of the thread -} ->
  C.TypeRepr spawnRetTy {-^ The return type of the function starting the thread (e.g. spawn) -} ->
  FnHandle (Ctx.EmptyCtx Ctx.::> ty) retTy {-^ The new thread -} ->
  RegValue sym ty {-^ The argument to pass to the new thread -} ->
  (sym -> Int -> IO (RegValue sym spawnRetTy)) {-^ How to construct the return value from the new thread's ID -} ->
  C.StmtSeq ext blocks rty (ctx C.::> spawnRetTy) {-^ Continuation of the spawn function -} ->
  ThreadExecM alg sym ext ret root (CrucibleLang blocks rty) ('Just ctx)
    (ExecutionFeatureResult (ThreadExec alg sym ext ret) sym ext root)
scheduleThreadCreate ty retTy tpr fh arg mkRet rest =
  do let newThread = NewThread ty retTy arg fh
     addThread (stateExpl.scheduler) newThread
     len  <- use (stateExpl.scheduler.threads.to length)
     let tid = len - 1
     curr <- use (stateExec.currentEventID)
     stateExec %= addSpawnEvent (ThreadID tid) curr
     s' <- get
     case s' ^. stateTree.actFrame.gpValue of
       MF f ->
         do sym <- use (stateContext.ctxSymInterface)
            ret <- liftIO $ mkRet sym tid
            let f' = extendFrame tpr ret rest f
                st' = s' & stateTree.actFrame.gpValue .~ MF f'
            return (ExecutionFeatureNewState $ RunningState (RunReturnFrom "spawn") st')

-- | Consult the Scheduling Algorithm for the next thread to run.
yieldThread ::
  ( SchedulerConstraints sym ext alg
  , HasCallStack -- better debugging here
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  ThreadState alg sym ext ret {-^ The thread state to use for the currently executing thread -}  ->
  ThreadExecM alg sym ext ret rtp f a (Maybe (ExecState (ThreadExec alg sym ext ret) sym ext rtp))
yieldThread globs ts0 =
  do setActiveThreadState (stateExpl.scheduler) ts0 -- Critical! We want to be able to pick this thread
     ts <- runnableThreads globs
     if null ts
       -- If there are no runnable threads, then just return the (hopefully)
       -- already stored main result
       then do -- res <- use (stateExpl.scheduler.to mainCont)
               curr <- use (stateExec.currentEventID)
               stateExec.maximalEvents %= IntSet.insert curr
               return Nothing

       -- Otherwise mark backtracking points and pick a new thread
       else do me     <- use (stateExpl.scheduler.activeThread)
               mnext  <- runUpdateSchedAlg $ pickNextThread (ThreadID me) ts
               case mnext of
                 Nothing ->
                   -- Why is this infeasible? The scheduling algorithm might
                   -- have naively tried to backtrack a thread that wasn't
                   -- actually enabled. That's fine, we'll just abort execution
                   -- and the algorithm can decide what to do next.
                   Just <$> abortInfeasible

                 Just next ->
                   do let preempted = threadID (fst next) `elem` (fst <$> ts)
                                   && me /= threadID (fst next)
                      switchToPendingThread globs preempted next


-- | Run an action in the event that there are no threads to yield to. This is
-- used to wrap the pattern of attempting to yield to a new thread, finding none
-- are runnable, and finally updating the state with some bookkeeping.
maybeTerminate ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  (SimState (ThreadExec alg sym ext ret) sym ext rtp f a->
    ExecState (ThreadExec alg sym ext ret) sym ext rtp ) ->
  ThreadState alg sym ext ret ->
  SimState (ThreadExec alg sym ext ret) sym ext rtp f a ->
  IO (ExecutionFeatureResult (ThreadExec alg sym ext ret) sym ext rtp)
maybeTerminate globs withModified ts s =
  flip evalStateT s $!
    do res <- yieldThread globs ts
       case res of
         Nothing ->
           do s' <- get
              return $ ExecutionFeatureModifiedState $! withModified s'
         Just nextExSt ->
           return $! ExecutionFeatureNewState nextExSt

-- | Start executing a thread. This function does all the necessary bookkeeping,
-- chiefly adding the new event to the event graph.
switchToPendingThread ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  Bool ->
  (ThreadID, Direction) ->
  ThreadExecM alg sym ext ret rtp f a (Maybe (ExecState (ThreadExec alg sym ext ret) sym ext rtp))
switchToPendingThread globals preempted (tid, dir) =
  do curr <- use $ stateExec.currentEventID
     tstate <- (V.! threadID tid) <$> use (stateExpl.scheduler.threads)
     es <- lookupNextEvent curr tid dir (tsEventInfo tstate dir)
     runUpdateSchedAlg $ notifyNewEvents tid dir es
     let e = last es
     stateExec.currentEventID .= e ^. eventID
     when preempted $ stateExpl.scheduler.numSwitches %= (+1)
     n <- use (stateExpl.scheduler.numSwitches)
     blocked <- not <$> checkRunnable globals tstate
     if (?bound > 0 && n > ?bound) || blocked
       -- TODO: Re-evaluate if returning a Maybe value here is ever useful.
        then Just <$> abortInfeasible
        else do assertRunnable globals tid tstate e
                Just <$> resumeThreadState globals tid tstate dir

-- | Given a thread ID and state for that thread, resume execution of that
-- thread from that state. Fails with an error if the thread is not actually
-- runnable.
resumeThreadState ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  ThreadID ->
  ThreadState alg sym ext ret ->
  Direction ->
  ThreadExecM alg sym ext ret rtp f a (ExecState (ThreadExec alg sym ext ret) sym ext rtp)
resumeThreadState globalVars tID ts dir =
  do stateExpl.scheduler.activeThread .= threadID tID
     case ts of
       CompletedThread {} ->
         error "resumeThreadState: trying to resume a completed thread!"
       EmptyThread ->
         error "resumeThreadState: trying to resume an empty thread!"

       NewThread argRepr _retRepr arg fh
         | dir == NoDirection -> startNewThread globalVars argRepr arg fh
         | otherwise -> error "Running Thread, with direction"

       RunningThread resumeCond retHandler stack
         | dir == NoDirection ->
           do isRunnable <- checkRunnable globalVars ts
              if isRunnable then
                do case resumeCond of
                     OnPred _ (SchedulerVar gvName) ->
                       setInternalGlobal gvName C.BoolRepr (return . falsePred)
                     _ -> return ()
                   restoreRunningThread retHandler stack
              else error "Restoring a thread that is not runnable"

         | otherwise -> error "Running Thread, with direction"

       BranchingThread p stk tframe fframe ->
         restoreBranchingThread tID dir p stk tframe fframe

-- | Starts a new thread, passing the given RegValue as its argument.
startNewThread ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  [Some GlobalVar] ->
  C.TypeRepr ty ->
  RegValue sym ty ->
  FnHandle (Ctx.EmptyCtx Ctx.::> ty) retTy ->
  ThreadExecM alg sym ext ret (RegEntry sym ret) f a (ExecState (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret))
startNewThread globalVars argRepr arg fh =
  do st   <- get
     loc  <- liftIO $ getCurrentProgramLoc (st ^. stateSymInterface)
     ty@C.UnitRepr   <- use (stateExpl.scheduler.retRepr)
     ctx   <- use stateContext
     globs <- use (stateTree.actFrame.gpGlobals)
     let s0   = InitialState ctx globs defaultAbortHandler ty act
         regs = assignReg argRepr arg emptyRegMap
         act  = callFunction (HandleFnVal fh) regs err loc
         err  = ReturnToOverride c
         c v retSt =
           do (res, retSt') <- runStateT (yieldThread globalVars (CompletedThread v)) retSt
              case res of
                Nothing  ->
                  do let k = retSt' ^. stateExpl.scheduler.to (\x -> mainCont x)
                     runReaderT (runOverrideSim C.UnitRepr k) retSt'
                Just st' ->
                  return st'
     return s0

-- | Resume a thread that was suspended
restoreRunningThread ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  ReturnHandler r (ThreadExec alg sym ext ret) sym ext rtp g args ->
  ActiveTree (ThreadExec alg sym ext ret) sym ext rtp g args ->
  ThreadExecM alg sym ext ret rtp f a (ExecState (ThreadExec alg sym ext ret) sym ext rtp)
restoreRunningThread (ReturnToCrucible C.UnitRepr rest) (ActiveTree ctx pres) =
  case pres ^. partialValue.gpValue of
    MF f ->
      do st <- get
         let s' = st & (stateTree.actFrame.gpGlobals .~ st ^. stateTree.actFrame.gpGlobals)
                     . (stateTree .~ ActiveTree ctx (pres & partialValue . gpValue .~ MF f'))
             f' = extendFrame C.UnitRepr () rest f
         liftIO $ runReaderT (continue (RunReturnFrom "yield")) s'
restoreRunningThread (ReturnToCrucible retType rest) (ActiveTree ctx pres) =
  do me <- use $ stateExpl.scheduler.activeThread
     thds <- use $ stateExpl.scheduler.threads
     ts <- getThreadState (stateExpl.scheduler) me
     st <- get
     case pres ^. partialValue.gpValue of
       MF f ->
         case ts of -- TODO: make this a parameter
           RunningThread (OnJoin blockingThread) _ _
             | CompletedThread retVal <- thds V.! threadID blockingThread
             , Just Refl <- testEquality retType (C.BVRepr (knownNat @32))
             , Just Refl <- testEquality retType (regType retVal) ->
               do let s' = st & (stateTree.actFrame.gpGlobals .~ st ^. stateTree.actFrame.gpGlobals)
                              . (stateTree .~ ActiveTree ctx (pres & partialValue . gpValue .~ MF f'))
                      f' = extendFrame (regType retVal) (regValue retVal) rest f
                  liftIO $ runReaderT (continue (RunReturnFrom "crucible_join")) s'
             | otherwise ->
               do error "Thread calling join is about to be resumed but the blocking thread has not returned correctly!"
           _ ->
             error $ "Missing case: " ++ show me ++ ": " ++ ppThreadState ts
restoreRunningThread (ReturnToOverride _k) (ActiveTree _ctx _pres) =
  error "TBD: ReturnToOverride"
restoreRunningThread TailReturnToCrucible (ActiveTree _ctx _pres) =
  error "TBD: TailReturnToCrucible"

-- | Restore a thread that paused to pick a branch to execute by executing the
-- branch indicated by the given @Direction@.
restoreBranchingThread ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  ThreadID ->
  Direction ->
  Pred sym ->
  ValueFromFrame (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) g ->
  PausedFrame (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) g ->
  PausedFrame (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) g ->
  ThreadExecM alg sym ext ret (RegEntry sym ret) f a (ExecState (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret))
restoreBranchingThread tID dir branchPred stk tframe fframe =
  use stateContext >>= \ctx -> withBackend ctx $ \bak ->
  do let sym = backendGetSym bak
     loc <- liftIO $ getCurrentProgramLoc sym
     prev <- use (stateExec.prevEventID)
     runUpdateSchedAlg $ notifyBranch tID prev
     let (frame, assm) = if dir == TBranch
                            then (tframe, return branchPred)
                            else (fframe, notPred sym branchPred)
     assmPred <- liftIO assm
     liftIO $ addAssumption bak (BranchCondition loc (pausedLoc frame) assmPred)
     s <- get
     case frame of
       PausedFrame frm cont l ->
         do globs <- use (stateTree.actFrame.gpGlobals)
            let frm' = frm & partialValue.gpGlobals .~ globs
            liftIO $ runReaderT (resumeFrame (PausedFrame frm' cont l) stk) s

abortInfeasible ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  ThreadExecM alg sym ext ret rtp f a (ExecState (ThreadExec alg sym ext ret) sym ext rtp)
abortInfeasible =
  do s <- get
     sym <- use (stateContext.ctxSymInterface)
     loc <- liftIO $ getCurrentProgramLoc sym
     liftIO $ runReaderT (abortExec (InfeasibleBranch loc)) s

returnFinishedResult ::
  ( SchedulerConstraints sym ext alg
  , rtp ~ RegEntry sym ret
  ) =>
  Maybe (RegEntry sym ret) ->
  ThreadExecM alg sym ext ret rtp f a (ExecState (ThreadExec alg sym ext ret) sym ext rtp)
returnFinishedResult mres =
  use stateContext >>= \ctx -> withBackend ctx $ \bak ->
  do gp  <- use $ stateTree.actFrame
     case mres of
       Just res ->
         return $ ResultState (FinishedResult ctx (TotalRes (gp & gpValue .~ res)))
       Nothing ->
         do sym <- use (stateContext.ctxSymInterface)
            loc <- liftIO $ getCurrentProgramLoc sym
            let simerr = SimError loc "<deadlock>"
            let err = LabeledPred (falsePred sym) simerr
            liftIO $ addProofObligation bak err
            s <- get
            liftIO $
              do putStrLn "<deadlock>"
                 runReaderT (abortExec (AssertionFailure simerr)) s

-- | ThreadState helpers

-- | The ThreadState corresponding to a thread executing @join@
blockThreadOnJoin ::
  ThreadID ->
  ReturnHandler r (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) f a ->
  SimState (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) f a ->
  ThreadState alg sym ext ret
blockThreadOnJoin tid = saveThreadState (OnJoin tid)

-- | Grab enough state to be able resume running the current thread
saveThreadState ::
  ResumeCond ->
  ReturnHandler r (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) f a ->
  SimState (ThreadExec alg sym ext ret) sym ext (RegEntry sym ret) f a ->
  ThreadState alg sym ext ret
saveThreadState rcond rh st = RunningThread rcond rh (st ^. stateTree)

-- | Modifying the Execution graph

-- | This is the main function to use to either lookup or insert new events.
-- Given a list of EventInfos to possibly insert, starting from the given event
-- follow the given thread and direction. Creates new EventInfos if necessary.
-- N.B. the assumption is that EITHER the requested EventInfos will be found, OR
-- none of them will be, AND that they will be of the same sort (Writes, Reads, etc).
lookupNextEvent :: EventID -> ThreadID -> Direction -> [EventInfo] -> ThreadExecM alg sym ext ret r f a [ThreadEvent]
lookupNextEvent fromEvent p dir (i:infos) =
  do nextEId  <- use (stateExec.nextEvent. at (fromEvent, p, dir))
     case nextEId of
       Just eid ->
         do nextE <- use (stateExec.event eid)
            let nextInfo = mergeEventInfo i (nextE ^. eventInfo)
                nextE'   = nextE & eventInfo .~ nextInfo
            stateExec.eventMap %= IntMap.insert eid nextE'
            es' <- lookupNextEvent eid p dir infos
            return (nextE' : es')
       Nothing  -> addNewEvents fromEvent p dir (i:infos)
  where
    -- | TODO: Evaluate why this is right!
    -- I think we don't REALLY need to store the read/write sets _after_ a run,
    -- because all we need them for is identifying backtracking points. Backtracking points
    -- DO persist across executions, but we only really need the latest resource names.
    mergeEventInfo (Write ws) (Write _) = Write ws
    mergeEventInfo (Read rs) (Read _) = Read rs
    mergeEventInfo ti ti' | ti == ti' = ti
                          | otherwise = error "Unexpected case in mergeEventInfo"
lookupNextEvent _ _ _ [] = return []

-- | Insert a new event as a child of the given @EventID@. There must not
-- already be a "next" event from the given @EventID@ along the triple of the
-- given @ThreadID@, @EventInfo@'s thread, and @Direction@.
addNewEvent ::
  EventID ->
  ThreadID ->
  EventInfo ->
  Direction ->
  ThreadExecM alg sym ext ret r f a (ScheduleEvent EventInfo)
addNewEvent curr who ei dir =
  do eId   <- freshEventID
     let new = ScheduleEvent { _eventID = eId
                             , _eventThread = who
                             , _eventInfo = ei
                             }
     stateExec.eventMap %= IntMap.insert eId new
     stateExec.nextEvent.at (curr, who, dir) %= \case
       Nothing -> Just eId
       Just _  -> error ("Adding new event " ++ ppScheduleEvent new
                          ++ " to already-taken path!\n") -- ++ ppSchedExecutionsDPOR exe dpor)
     stateExec.prevEvent.at eId %= \case
       Nothing -> Just curr
       Just _ -> error "Previous event exists for new event!"
     return new

addNewEvents ::
  EventID ->
  ThreadID ->
  Direction ->
  [EventInfo] ->
  ThreadExecM alg sym ext ret r f a [ScheduleEvent EventInfo]
addNewEvents curr who dir eis =
  reverse . snd <$> foldlM addOne (curr, []) eis
  where
    addOne (lastEvent, es) ei =
      do e' <- addNewEvent lastEvent who ei dir
         return (e' ^. eventID, e':es)

freshEventID :: ThreadExecM alg sym ext ret r f a Int
freshEventID =
  do stateExec.lastEventID %= (+1)
     use $ stateExec.lastEventID

-- | Set a condition variable to True
notifyThread :: Text -> ThreadState alg sym ext ret -> ThreadState alg sym ext ret
notifyThread gv ts =
  case ts of
    RunningThread (OnCond gv' m _) rh stk
      | gv == gv' -> RunningThread (OnCond gv' m True) rh stk
    _ -> ts

-- | Return True if the given @ThreadState@ denotes an executable thread
checkRunnable ::
  IsSymInterface sym =>
  [Some GlobalVar] ->
  ThreadState alg sym ext ret ->
  ThreadExecM alg sym ext ret r f a Bool
checkRunnable globs ts =
  do ths <- use (stateExpl.scheduler.threads)
     ourglobs <- use (stateExpl.gVars)
     globState <- use stateGlobals
     return (runnable globState ourglobs globs ths ts)

-- | Exit with an error if the given @ThreadState@ is is not runnable
assertRunnable ::
  IsSymInterface sym =>
  [Some GlobalVar] ->
  ThreadID ->
  ThreadState alg sym ext ret ->
  ScheduleEvent EventInfo ->
  ThreadExecM alg sym ext ret r f a ()
assertRunnable globs thID thNext e =
  do canRun <- checkRunnable globs thNext
     unless canRun $
       do me  <- use (stateExpl.scheduler.activeThread)
          liftIO $ putStrLn ("Thread: " ++ show me)
          liftIO $ putStrLn ("Trying pending event: " ++ ppScheduleEvent e)
          error $ "Thread " ++ show thID ++ "empty!"

-- | Return all the threads that can be run
runnableThreads ::
  IsSymInterface sym =>
  [Some GlobalVar] ->
  ThreadExecM alg sym ext ret r f a [(Int, ThreadState alg sym ext ret)]
runnableThreads globs =
  do globState <- use stateGlobals
     ourglobs  <- use (stateExpl.gVars)
     selectThreads (stateExpl.scheduler) (\ths _ st -> runnable globState ourglobs globs ths st)

-- | Pure function that returns True if the given state denotes a runnable thread
runnable ::
  IsSymInterface sym =>
  SymGlobalState sym {-^ Current global state -} ->
  Map.Map Text (C.Some GlobalVar) {-^ Scheduler variables that we might want to inspect -} ->
  [Some GlobalVar] {-^ Program globals that we might want to inspect -} ->
  V.Vector (ThreadState alg sym ext ret) {-^ State of all threads -} ->
  ThreadState alg sym ext ret {-^ Thread in question -} ->
  Bool
runnable st ourglobals globals allThreads ts =
  case ts of
    NewThread{} -> True
    EmptyThread -> False
    CompletedThread {} -> False
    RunningThread (OnPred _ (ProgramVar predVar)) _ _
      | Just gv <- findGlobalVar globals predVar C.BoolRepr ->
      evalGlobalPred gv st
      | otherwise ->
        error $ "Unknown program var: " ++ show predVar
    RunningThread (OnPred _ (SchedulerVar predVar)) _ _
      | Just (C.Some gv) <- Map.lookup predVar ourglobals
      , C.BoolRepr <- globalType gv ->
      evalGlobalPred gv st
      | otherwise ->
        error $ "Unknown scheduler var: " ++ show predVar
    RunningThread (OnCond _ _ notified) _ _ -> notified
    RunningThread (OnJoin tid) _ _
      | threadID tid < V.length allThreads ->
        done (allThreads V.! threadID tid)
      | otherwise ->
        error $ "Bad thread id " ++ show tid
    RunningThread (Resumable _) _ _ -> True
    BranchingThread {} -> True
  where
    done :: ThreadState alg sym ext ret -> Bool
    done EmptyThread = True
    done CompletedThread{} = True
    done _ = False

getInternalGlobal ::
  Text ->
  C.TypeRepr tp ->
  ThreadExecM alg sym ext ret r f a (Maybe (RegValue sym tp))
getInternalGlobal l tpr =
  do gvar <- use $ stateExpl.gVars.at l
     case gvar of
       Just (C.Some gv)
         | Just C.Refl <- testEquality (globalType gv) tpr ->
           lookupGlobal gv <$> use stateGlobals
       _ -> return Nothing

setInternalGlobal ::
  Text ->
  C.TypeRepr tp ->
  (sym -> IO (RegValue sym tp)) ->
  ThreadExecM alg sym ext ret r f a ()
setInternalGlobal l tpr val =
  do gvar <- use $ stateExpl.gVars.at l
     case gvar of
       Just (C.Some gv)
         | Just C.Refl <- testEquality (globalType gv) tpr ->
           do sym <- use $ stateContext.ctxSymInterface
              v   <- liftIO $ val sym
              stateGlobals %= insertGlobal gv v
       _ -> return ()


-- | Adds a new internal global mapping from l |-> new global, if necessary.
-- ADDITIONALLY sets the value *in crucible* of this global variable.
initializeInternalGlobal :: Text -> C.TypeRepr ty -> (sym -> IO (RegValue sym ty)) -> ThreadExecM alg sym ext ret r f a ()
initializeInternalGlobal l tpr mkVal =
  do ha     <- use $ stateContext.to simHandleAllocator.to haCounter
     gvar   <- use $ stateExpl.gVars.at l
     globSt <- use stateGlobals
     case gvar of
       Nothing ->
         do n <- liftIO $ freshNonce ha
            let gv = GlobalVar n l tpr
            sym <- use $ stateContext.ctxSymInterface
            stateExpl.gVars.at l .= Just (C.Some gv)
            val <- liftIO $ mkVal sym
            stateGlobals .= insertGlobal gv val globSt

       Just (C.Some gv)
         | Just Refl <- testEquality tpr (globalType gv)
         , Nothing   <- lookupGlobal gv globSt ->
         do sym <- use $ stateContext.ctxSymInterface
            val <- liftIO $ mkVal sym
            stateGlobals .= insertGlobal gv val globSt

       _ -> return ()

-- | Debugging
ppScheduler :: Scheduler p sym1 ext (ThreadState alg sym2 ext ret1) ret2 -> [Char]
ppScheduler sched =
  "[" ++ unwords (ppThreadState <$> V.toList (_threads sched)) ++ "]"
