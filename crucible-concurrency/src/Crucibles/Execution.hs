{- |
Module           : Crucibles.Execution
Description      : Representation of process executions
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>

This module exposes types for tracking sets of process executions. It is
designed to make tracing executions from end to start (somewhat) convenient, at
least compared to start-to-end.

An execution here is a sequence of events. Each event has a unique predecessor.

A set of executions are bundled into an @Executions@ data type, which is the
tree of all executions. A value of type @Executions@ also has a notion of the
"current" event, from which the notion of the "current" execution may be derived
(by following the predecessors of the current exeuction).

The @Executions@ structure includes process clock vectors, and the set of
"maximal" events, which are terminal events in _feasible_ executions, as opposed
to executions that were aborted partway.

Crucially, the data type allows labeling each event with sets of events that are
"pending," "done," or "aborted." The module exposes an operation that propagates
this information _backwards_ from a given event ID. This operation treats a
maximal event as "done," and marks it as such in the parent (predecessor) event.
An event is also "done" if its pending set minus its aborted & done sets is
empty.

A set of execution is hence "done" when the root node (event ID 0) is "done".

(This should probably be refactored, as it is
somewhat specific to a particular class of exploration algorithms.)

N.B. This module makes heavy use of lenses, partially because I took this as an
opportunity to learn the @lens@ library.

-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# Language TemplateHaskell #-}
module Crucibles.Execution where

import           Control.Lens
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import           Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import           Data.Text (Text)
import           Data.Maybe (fromMaybe)
import           GHC.Stack

type EventID    = Int
type EventIDMap = IntMap
type EventIDSet = IntSet

-- | Wrapper for Thread IDs to distinguish them from Event IDs
newtype ThreadID = ThreadID { threadID :: Int }
  deriving (Eq, Ord, Show)
type ThreadIDSet = Set ThreadID

-- | A @Direction@ is the (possible) result of taking a branch
data Direction = NoDirection | TBranch | FBranch
               deriving (Eq, Ord, Show)

-- | A @Resource@ is anything that might be shared & accessed by multiple
-- threads, i.e. global variables.
data Resource res = Thread !ThreadID | Resource !res
                  deriving (Eq, Ord, Show)

-- | An @Executions@ denotes a tree of individual, labeled executions, stored as a graph.
-- The nodes are eventIDs.
-- @_pending@ labels each event by the pending threads at that event (i.e. that should be explored next)
-- @_explored@ labels each event by the threads that have been completely explored at that event  (i.e. are done)
-- @_aborting@ labels each event by the threads that eventually cause the execution to abort (e.g. lead to an infeasible path)
data Executions e =
  Exe { _eventMap       :: !(EventIDMap e) -- ^ Labels each eventID by the corresponding event structure
      , _nextEvent      :: !(Map (EventID, ThreadID, Direction) EventID)
        -- ^ The successor of an event when taking a given thread in a given direction
      , _prevEvent      :: !(EventIDMap EventID) -- ^ The predecessor of an event
      , _currentEventID :: !EventID
        -- ^ Builds in a notion of a current trace: a trace is hence extended by
        -- adding a successor of the current event.
      , _lastEventID    :: !EventID
        -- ^ the domain of the event map is [0, lastEventID]
      , _maximalEvents  :: !EventIDSet -- ^ Set of terminal events of feasible paths
      , _birthdays      :: !(Map ThreadID EventID)
        -- ^ The events where each thread is spawned (possibly separate from
        -- when the thread actually starts running)
      } deriving (Show)
makeLenses ''Executions

-- | While the @Executions@ structure is parameterized by the type of event, most of the time
-- we seem to want something like a @ScheduleEvent@. This is parameterized by the actual details of
-- the event.
data ScheduleEvent eventinfo =
  ScheduleEvent { _eventID     :: !EventID -- ^ The event's ID
                , _eventThread :: !ThreadID -- ^ The thread responsible for this event
                , _eventInfo   :: !eventinfo -- ^ Any important information
                }
  deriving (Show, Eq, Ord)
makeLenses ''ScheduleEvent

-- | Return the set of empty executions
initialExecutions :: Executions e
initialExecutions =
  Exe { _eventMap = mempty
      , _nextEvent = mempty
      , _prevEvent = mempty
      , _currentEventID = 0
      , _lastEventID = 0
      , _maximalEvents = mempty
      , _birthdays = mempty
      }

-- | True if the current execution is maximal
maximalExecution :: Executions e -> Bool
maximalExecution e = IntSet.member (e ^. currentEventID) (e ^. maximalEvents)

-- | Lens for extracting an event given its eventID. Will fail with an error if
-- the eventID is not mapped.
event :: HasCallStack => EventID -> Getter (Executions e) e
event eid = to (fromMaybe err . IntMap.lookup eid . _eventMap)
  where
    err = error ("Executions with unknown current event: " ++ show eid)

-- | Convenience lens for looking up the current event. Fails if the current
-- event is not actually mapped.
currentEvent :: Getter (Executions e) e
currentEvent = to getter
  where
    getter e = fromMaybe (err e) (IntMap.lookup (_currentEventID e) (_eventMap e))
    err e    = error ("Executions with unknown current event: " ++ show (_currentEventID e))

-- | Convenience lens for looking up the current event's previous event. Fails
-- if the current event is not actually mapped.
prevEventID :: Getter (Executions (ScheduleEvent i)) EventID
prevEventID = to getter
  where
    getter e = fromMaybe (err e) $ e ^. prevEvent.at (e ^. currentEvent.eventID)
    err e    = error ("No prior event ID " ++ show (_currentEventID e))

-- | Lookup the "Birthday" of a thread, i.e. the event that must preceed the
-- first event of the new thread.
spawnEvent :: ThreadID -> Executions e -> Maybe EventID
spawnEvent tid exe = exe ^. birthdays.at tid

-- | Record a thread's "birthday"
addSpawnEvent :: ThreadID -> EventID -> Executions e -> Executions e
addSpawnEvent tid eventid exe = exe & birthdays.at tid ?~ eventid

-- | Look up the last event in the current execution performed by the given @ThreadID@.
threadPreviousEvent :: ThreadID -> EventID -> Executions (ScheduleEvent i) -> Maybe EventID
threadPreviousEvent tid eventid exe
  | tid == prevE ^. eventThread
  = Just prev
  | 0 == prev
  = Nothing
  | otherwise
  = threadPreviousEvent tid prev exe
  where
    prev  = exe ^. prevEvent . at eventid . to (fromMaybe 0)
    prevE = exe ^. event prev

-- | @EventInfo@ denotes the different events we are interested in.
data EventInfo = Write !(Set Text) -- ^ Modify a named resource
               | Read !(Set Text) -- ^ Access (but do not modify) a named resource
               | ThreadSpawn -- ^ Thread starts running
               | ThreadExit -- ^ Thread terminates
               | Join -- ^ Thread terminates, unblocking a waiting thread
               | Branch !Bool -- ^ Take a local branch
  deriving (Show, Eq, Ord)

-- | Get all of the resources accessed by the denoted event
eventResource :: EventInfo -> Set (Resource Text)
eventResource ei =
  case ei of
    Write t     -> Set.map Resource t
    Read t      -> Set.map Resource t
    ThreadSpawn -> mempty
    ThreadExit  -> mempty
    Join        -> mempty
    Branch{}    -> mempty

-- | Get the current execution as a sequence of events
currentTrace :: Executions (ScheduleEvent i) -> [ScheduleEvent i]
currentTrace = go []
  where
    go tr exe
      | exe ^. currentEventID == 0 =
          tr
      | otherwise =
          go (exe ^. currentEvent : tr) (exe & currentEventID .~ exe ^. prevEventID)


-- | Pretty print (for debugging)
ppDirection :: Direction -> String
ppDirection NoDirection = ""
ppDirection TBranch = "@T"
ppDirection FBranch = "@F"

-- | Pretty print (for debugging)
ppEventInfo :: EventInfo -> [Char]
ppEventInfo = show

-- | Pretty print (for debugging)
ppScheduleEvent :: ScheduleEvent EventInfo -> [Char]
ppScheduleEvent ScheduleEvent{..} =
  "<" ++ show _eventID ++ ": thread " ++ show _eventThread ++ " " ++ ppEventInfo _eventInfo  ++ ">"

-- | Pretty print (for debugging)
ppBirthdays :: Map ThreadID EventID -> String
ppBirthdays bdays =
  "Birthdays:\n" ++ unlines [ " " ++ show t ++ "@" ++ show e | (ThreadID t, e) <- Map.toList bdays ]
