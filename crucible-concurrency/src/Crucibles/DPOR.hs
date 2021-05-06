{- |
Module           : Crucibles.DPOR
Description      : Vanilla DPOR implementation of SchedulingAlgorithm
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

This exports an instance of of SchedulingAlgorithm that implements DPOR
(Flanagan and Godefroid, 2005).

Essentially, on each step that accesses a resource R, the algorithm finds the
last event E that modified R. If that event doesn't 'happen before' a thread P
that is also about to access R, then we try to backtrack and run P just before
E. That's it! We use clockvectors to quickly compute the happens-before relation
(see the paper for details).
-}
{-# LANGUAGE ImplicitParams #-}
{-# Language TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
module Crucibles.DPOR (DPOR, ppSchedExecutionsDPOR) where

import           Control.Lens
import           Data.List (intercalate)
import           Data.Map.Strict (Map)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.IntMap.Strict as IntMap
import           Data.Maybe (fromMaybe)
import           GHC.Stack
import           Control.Monad.State
import           Data.Foldable (traverse_)

import           Crucibles.Common
import           Crucibles.Execution
import           Crucibles.ClockVector
import           Crucibles.SchedulingAlgorithm

-- | A @PendingThread@ denotes an event that has not been explored, by running
-- the next action of @pendingThread@ (taking the branch denoted by
-- @pendingDirection@ if it is a branch)
data PendingThread = Pending { pendingThread :: ThreadID
                             , pendingDirection :: Direction
                             }
                   deriving (Eq, Ord, Show)
type PendingThreadSet = Set.Set PendingThread

data DPOR = DPOR
  { _pending        :: !(EventIDMap PendingThreadSet) -- ^ Which processes to take next
  , _explored       :: !(EventIDMap PendingThreadSet) -- ^ Which processes already explored
  , _aborting       :: !(EventIDMap PendingThreadSet) -- ^ Which processes lead to an invalid execution
  , _lastAccess     :: !(Map (Resource Text) EventID)
    -- ^ bookkeeping for exploration (should be refactored): the eventID of
    -- the most recent access to a resource.
  , _clockVectors   :: !(Map (Resource Text) (ClockVector (Resource Text) EventID))
    -- ^ Clockvectors for the execution: Using a resource here lets us track
    -- resources as well as threads as processes (refactor as this is very
    -- specific to their usage in Flanagan/Godefroid 05)
  }
makeLenses ''DPOR

instance SchedulingAlgorithm DPOR where

  initialAlgState = initialDPOR

  processExecution = markCovered

  fullyExplored = fullyExploredDPOR

  prepareNewExecution = prepareNewExecutionDPOR

  notifyNewEvents = notifyNewEventsDPOR

  notifyBranch = notifyBranchDPOR

  pickNextThread = pickNextThreadDPOR

  ppExecutions = ppExecutionsDPOR


initialDPOR :: DPOR
initialDPOR = DPOR
  { _pending = mempty
  , _explored = mempty
  , _aborting = mempty
  , _lastAccess = mempty
  , _clockVectors = mempty
  }

-- | Convenience lens for looking up the current pending events. Fails if the current
-- event is not actually mapped.
pendingAt :: HasCallStack => EventID -> Lens' DPOR PendingThreadSet
pendingAt eid = lens getter setter
  where
    getter e   = fromMaybe mempty (IntMap.lookup eid (_pending e))
    setter e v = e { _pending = IntMap.insert eid v (_pending e) }

-- | Convenience lens for looking up the current explored events. Fails if the current
-- event is not actually mapped.
exploredAt :: HasCallStack =>  EventID -> Lens' DPOR PendingThreadSet
exploredAt eid = lens getter setter
  where
    getter e   = fromMaybe mempty (IntMap.lookup eid (_explored e))
    setter e v = e { _pending = IntMap.insert eid v (_explored e) }

-- | Convenience lens for looking up the current aborting events. Fails if the current
-- event is not actually mapped.
abortingAt :: HasCallStack =>  EventID -> Lens' DPOR PendingThreadSet
abortingAt eid = lens getter setter
  where
    getter e   = fromMaybe mempty (IntMap.lookup eid (_aborting e))
    setter e v = e { _pending = IntMap.insert eid v (_aborting e) }

-- | True when we've explored all pending events
fullyExploredDPOR :: Executions e -> DPOR -> Bool
fullyExploredDPOR exe dpor =
     Set.isSubsetOf pendHere (Set.union abortHere doneHere)
  && (not (Set.null pendHere) || maximalExecution exe)
  where
    curID      = exe ^. currentEventID
    pendHere   = dpor ^. pendingAt curID
    doneHere   = dpor ^. exploredAt curID
    abortHere  = dpor ^. abortingAt curID

-- | Starting from the last event, update pending events in ancestors
markCovered :: Executions (ScheduleEvent EventInfo) -> DPOR -> DPOR
markCovered exe dpor =
  if maximalExecution exe
    then markCovered' exe dpor
    else markAborted' exe dpor

-- | Treat the current event as aborted, and propagate that information to parents
markAborted' :: Executions (ScheduleEvent EventInfo) -> DPOR -> DPOR
markAborted' exe dpor
  | exe ^. currentEventID == 0 =
    dpor
  | otherwise =
    markCovered' (exe & currentEventID .~ prevID)
                 (dpor & (pending.at prevID %~ pure . del)
                       . (aborting.at prevID %~ pure . ins))
  where
    prevID     = exe ^. prevEventID
    thisThread = exe ^. currentEvent.eventThread
    ins        = maybe (Set.singleton avoid) (Set.insert avoid)
    avoid      = Pending thisThread (infoDirection (exe ^. currentEvent.eventInfo))
    del        = maybe mempty (Set.delete avoid)

    infoDirection (Branch d) = if d then TBranch else FBranch
    infoDirection _          = NoDirection


-- | Propagate current event's status to parents
markCovered' :: Executions (ScheduleEvent EventInfo) -> DPOR -> DPOR
markCovered' exe dpor
  | exe ^. currentEventID == 0 =
    dpor
  | Set.isSubsetOf pendHere (Set.union abortHere doneHere)
  , not (Set.null pendHere) || maximalExecution exe =
    -- Remove self from parent
    markCovered' (exe & currentEventID .~ prevID)
                 (dpor & explored.at prevID %~ ins thisPending)

  | otherwise =
    -- Make sure we're in the parent pending set
    markCovered' (exe & currentEventID .~ prevID)
                 (dpor & pending.at prevID %~ ins thisPending)
  where
    thisThread = exe ^. currentEvent.eventThread
    thisPending = case exe ^. currentEvent.eventInfo of
                      Branch d -> Set.fromList [ Pending thisThread (if d then TBranch else FBranch)
                                               , Pending thisThread NoDirection ]
                      _        -> Set.singleton (Pending thisThread NoDirection)

    prevID     = exe ^. prevEventID
    curID      = exe ^. currentEventID
    pendHere   = dpor ^. pending.at curID.to (fromMaybe mempty)
    doneHere   = dpor ^. explored.at curID.to (fromMaybe mempty)
    abortHere  = dpor ^. aborting.at curID.to (fromMaybe mempty)

    ins x s = pure $ maybe x (Set.union x) s

-- | Returns true if eid happens before p in this execution (from DPOR paper), i.e. if
-- eid <= C(p)(eid.threadid)
eventBeforeProc :: EventID -> ThreadID -> Executions (ScheduleEvent EventInfo) -> DPOR -> Bool
eventBeforeProc eid p exe dpor
  | eid == 0
  = False
  | th <- exe ^.event eid.eventThread
  = eid <= val th
  | otherwise = False
  where
    val t        = dpor ^. clockVectors.at (Thread p).to emp.cvAt (Thread t)
    emp Nothing  = CV mempty
    emp (Just x) = x

-- | Pretty print (for debugging)
ppEvent :: ScheduleEvent EventInfo -> [Char]
ppEvent e =
  "e" ++ show (_eventID e) ++ "<"
  ++ "t" ++ show (threadID (_eventThread e))
  ++ " " ++ ppEventInfo (_eventInfo e)

  ++ ">"

-- | Pretty print (for debugging)
ppPending :: Maybe PendingThreadSet -> String
ppPending Nothing  = "{}"
ppPending (Just s) =
  "{" ++ intercalate ", " (ppPendingThread <$> Set.toList s) ++ "}"

-- | Pretty print (for debugging)
ppPendingThread :: PendingThread -> String
ppPendingThread p = "t" ++ show (threadID (pendingThread p)) ++ ppDirection (pendingDirection p)

-- | Pretty print (for debugging)
ppSchedExecutionsDPOR :: Executions (ScheduleEvent EventInfo) -> DPOR -> [Char]
ppSchedExecutionsDPOR Exe{..} DPOR{..} =
  "Executions ending at  " ++ show _currentEventID ++ ":\n" ++
   concat [ "  event " ++ ppScheduleEvent e ++ "\n" | (_, e) <- IntMap.toList _eventMap] ++
   "\n" ++
   unlines [ "  pending " ++ show k ++ " => " ++ show e | (k, e) <- IntMap.toList _pending ] ++
   "\n" ++
   unlines [ "  done " ++ show k ++ " => " ++ show e | (k, e) <- IntMap.toList _explored ]

-- | Pretty print (for debugging)
ppExecutionsDPOR :: Executions (ScheduleEvent EventInfo) -> DPOR -> String
ppExecutionsDPOR exe dpor =
  ppExecutionsDPOR' exe dpor ++ "\n" ++
  if maximalExecution exe then "(maximal)" else "(aborted)"
ppExecutionsDPOR' :: Executions (ScheduleEvent EventInfo) -> DPOR -> String
ppExecutionsDPOR' exe dpor
  | this == 0
  = ppBirthdays (exe ^. birthdays)
    ++ "\n<root:0> " ++ ppPending (dpor ^. pending . at this)
         ++ " " ++ ppPending (dpor ^. explored . at this)
         ++ " " ++ ppPending (dpor ^. aborting . at this)
  | otherwise -- Just prev <- _prevID ev
  = ppExecutionsDPOR' exe { _currentEventID = exe ^. prevEventID } dpor ++ "\n"
    ++ ppEvent ev
    ++ " " ++ ppPending (dpor ^. (pending.at this))
    ++ " " ++ ppPending (dpor ^. (explored.at this))
    ++ " " ++ ppPending (dpor ^. (aborting.at this))
  where
    this = exe ^. currentEventID
    ev   = exe ^. currentEvent

-- | Reset the clock vectors
prepareNewExecutionDPOR :: SchedAlgM DPOR ()
prepareNewExecutionDPOR =
  do lastAccess   .= mempty
     clockVectors .= mempty

-- | Pick the next thread & mark any backtracking
pickNextThreadDPOR ::
  ThreadID ->
  [(Int, ThreadStateP p sym ext ret)] ->
  SchedAlgM DPOR (Maybe (ThreadID, Direction))
pickNextThreadDPOR me runnable =
  do markBacktracking me runnable
     toExplore <- pendingThreads
     mnext     <- pickArbitraryThread me toExplore runnable
     return     $ do Pending tid dir <- mnext
                     return (tid, dir)

-- | Pick an arbitrary thread, not necessarily based on which threads are
-- pending
pickArbitraryThread ::
  ThreadID ->
  PendingThreadSet ->
  [(Int, ThreadStateP p sym ext ret)] ->
  SchedAlgM DPOR (Maybe PendingThread)
pickArbitraryThread me pendingSet allRunnable =
  do curr <- view (exec.currentEventID)
     aborting0 <- use (abortingAt curr)

     let myPending    = Set.filter (\p -> threadID (pendingThread p) == threadID me) pendingSet Set.\\ aborting0
         spawnPending = Set.filter (\p -> threadID (pendingThread p) `elem` spawning) pendingSet Set.\\ aborting0

     case (Set.toList (pendingSet Set.\\ aborting0), Set.toList myPending, Set.toList spawnPending) of
       (_, _, p:_) -> return $ Just p
       (_, p:_, _) -> return $ Just p
       (p:_, _, _) -> return $ Just p

       ([], _, _)  -> return Nothing
  where
    spawning = [ i | (i, NewThread{}) <- allRunnable ]

-- | As described in the DPOR paper, find places where we ran thread P and need
-- to try running thread P' because they both access the same resource.
markBacktracking ::
  ThreadID ->
  [(Int, ThreadStateP p sym ext ret)] ->
  SchedAlgM DPOR ()
markBacktracking me ts =
  do curr <- view (exec.currentEventID)
     -- Set up the pending set for this event if necessary
     aborting0 <- use (aborting.at curr)
     let nonAborting  = Set.filter ((`Set.notMember` abortingTids) . pendingThread) ps
         abortingTids = Set.map pendingThread (fromMaybe mempty aborting0)
         ps           = mconcat (uncurry makePending <$> ts)
     mp <- pickArbitraryThread me nonAborting ts
     case mp of
       Just p -> initializeBacktracking curr (Set.singleton p)
       _      -> return ()
     forM_ ts $ \(tid, s) -> backtrack (ThreadID tid) s

-- | Record both directions of a branch as pending.
notifyBranchDPOR :: ThreadID -> EventID -> SchedAlgM DPOR ()
notifyBranchDPOR thread whereBranching =
  do markThreadPending (Pending thread TBranch) whereBranching
     markThreadPending (Pending thread FBranch) whereBranching

-- | Add a pending event for each ScheduleEvent, and update the vector clocks.
notifyNewEventsDPOR :: ThreadID -> Direction -> [ScheduleEvent EventInfo] -> SchedAlgM DPOR ()
notifyNewEventsDPOR who dir es =
  do curr <- view $ exec.currentEventID
     foldM_ addOne curr es
  where
    addOne lastEvent e =
      do markThreadPending (Pending who dir) lastEvent
         updateClocks e
         return (e ^. eventID)

-- | Add an event to a set of pending events
markThreadPending :: PendingThread -> EventID -> SchedAlgM DPOR ()
markThreadPending thread wherePending =
  pending  %= IntMap.alter ins wherePending
  where
    ins Nothing  = Just (Set.singleton thread)
    ins (Just s) = Just (Set.insert thread s)

-- | Find all the pending threads at the current event
pendingThreads :: SchedAlgM DPOR (Set.Set PendingThread)
pendingThreads =
  do curr     <- view (exec.currentEventID)
     pend     <- use (pendingAt curr)
     donets   <- use (exploredAt curr)
     aborted  <- use (abortingAt curr)
     return (pend Set.\\ (aborted <> donets))

-- | When we find a new event we need to set up its backtracking set
-- with an initial value.
initializeBacktracking :: EventID -> PendingThreadSet -> SchedAlgM DPOR ()
initializeBacktracking eid ps =
  do pending0  <- fromMaybe mempty <$> use (pending.at eid)
     when (Set.null pending0) $
       do curr <- view $ exec.currentEventID
          pendingAt curr  .= ps
          explored.at eid .= Just Set.empty

-- | Instead of DPOR, we could have just backtracked every thread at every step.
_backtrackAll ::
  ThreadID ->
  ThreadStateP p sym ext ret ->
  SchedAlgM DPOR ()
_backtrackAll t _ =
  do curr <- view $ exec.currentEventID
     pending.at curr %= fmap (Set.insert (Pending t NoDirection))

-- | For ALL of the resources that are about to be touched by a given threadstate,
-- mark backtracking points
backtrack ::
  ThreadID ->
  ThreadStateP p sym ext ret ->
  SchedAlgM DPOR ()
backtrack thId thState =
  traverse_ backtrackOne (nextResources thState)

  where
    backtrackOne r =
     do i        <- use (lastAccess.at r.to (fromMaybe 0)) -- Which event was the last access?
        currExec <- view exec
        hbefore  <- gets (eventBeforeProc i thId currExec)      -- Did the last event "happen before"
        let pend = Pending thId NoDirection
        when (0 < i && not hbefore) $
          do eventBeforeIID <- view (exec.prevEvent.at i.to (fromMaybe (error "no parent event in backtrack!")))
             myBirth        <- view  (exec.to (spawnEvent thId))
             -- This is all moot if the thread hadn't even been spawned at the
             -- backtracking point
             case myBirth of
               Just birthID | birthID <= eventBeforeIID ->
                 pending.at eventBeforeIID %=
                   (pure . (Set.singleton pend <>) . fromMaybe mempty)
               _ -> return ()

    -- search e =
    --   case e ^. eventInfo of
    --     Read{} -> True
    --     Write{} -> True
    --     ThreadSpawn -> e ^. eventThread == thId
    --     _ -> False

-- | Update vector clocks given a new event: the new event is the new timestamp
-- for the resources that it mentions.
updateClocks ::
  ScheduleEvent EventInfo ->
  SchedAlgM DPOR ()
updateClocks e =
  do cvP  <- use (clockVectors.at p.to (fromMaybe cvEmpty))
     cvOs <- sequence
       [use (clockVectors.at r.to (fromMaybe cvEmpty))
       | r <- Set.toList rs ]
     let cv = maxClockVectors (cvP : cvOs) & cvAt p .~ (e ^. eventID)
     clockVectors.at p .= Just cv
     forM_ rs $ \r ->
       do clockVectors.at r .= Just cv
          lastAccess.at r   .= Just (e ^. eventID)
  where
    rs = eventResource (e ^. eventInfo)
    p  = Thread (e ^. eventThread)

-- walkPrevID ::
--   (ScheduleEvent EventInfo -> Bool) ->
--   EventID ->
--   SchedAlgM DPOR EventID
-- walkPrevID stop eid
--   | eid == 0 = return eid
--   | otherwise =
--     do e <- view (exec.event eid)
--        if stop e then
--          return eid
--         else
--          do prev <- view (exec.prevEvent.at eid.to (fromMaybe (error "no parent event in walkPrevID")))
--             walkPrevID stop prev

-- | Given a thread state, turn it into a set of pending threads. This is either
-- just the threadID + no direction, or both directions of a branch.
makePending :: Int -> ThreadStateP p sym ext ret -> PendingThreadSet
makePending t ts =
  case ts of
    BranchingThread{} ->
      Set.fromList [Pending (ThreadID t) TBranch, Pending (ThreadID t) FBranch]
    _ ->
      Set.singleton (Pending (ThreadID t) NoDirection)
