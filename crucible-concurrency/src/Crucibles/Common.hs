{- |
Module           : Crucibles.Common
Description      : Common definitions related to resources and thread state
Copyright        : (c) Galois, Inc 2021
Maintainer       : Alexander Bakst <abakst@galois.com>
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Crucibles.Common where

import qualified Data.Set as Set
import           Data.Text (Text)

import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.CFG.Core as C

import Lang.Crucible.Simulator
import Lang.Crucible.FunctionHandle (FnHandle)
import Lang.Crucible.Simulator.ExecutionTree
import What4.Interface (Pred)

import Crucibles.Execution

data ResumeCond = Resumable !(Maybe (Bool, Set.Set Text))
                -- ^ Can be resumed (possibly with the resource that caused us to yield
                | OnJoin !ThreadID
                -- ^ unblocked when ThreadID has terminated
                | OnPred !(Set.Set Text) !ResumePred
                -- ^ Resumable once the global variable (a predicate, i.e. bool)
                -- denoted by the second Text parameter is equivalent to True
                -- The first parameter is a set of resources that cuased us to yield
                | OnCond !Text !Text !Bool
                -- ^ the condition variable + mutex + whether or not we've been notified
                -- (This is highly specialized to condition variables -- perhaps this should be
                -- folded into the more general Condition form)
                deriving (Show, Eq)

data ResumePred =
    ProgramVar !Text   -- ^ A predicate the user has defined
  | SchedulerVar !Text -- ^ A name denoting a predicate that we have defined (usually a lock)
                       --   that gets set *by the scheduler*
  deriving (Show, Eq)

data ThreadStateP p sym ext ret where
  -- | Empty thread: usually this denotes the root thread before it begins.
  EmptyThread ::
    ThreadStateP p sym ext ret

  -- | A thread that has terminated.
  CompletedThread ::
    RegEntry sym ty {-^ The value returned by the completed thread -} ->
    ThreadStateP p sym ext ret

  -- | A spawned thread that has not yet started execution
  NewThread ::
    C.TypeRepr ty {-^ The type of the argument to the thread function -} ->
    C.TypeRepr retTy {-^ The type returned by this thread -} ->
    RegValue sym ty {-^ The value that was passed to the thread function when it was spawned -} ->
    FnHandle (Ctx.EmptyCtx Ctx.::> ty) retTy -> --  This could probably be generalized -
    ThreadStateP p sym ext ret

  -- | A thread mid-execution
  RunningThread ::
    ResumeCond {-^ When this can be resumed -} ->
    ReturnHandler r p sym ext (RegEntry sym ret) f args {-^ What to do on termination -} ->
    ActiveTree p sym ext (RegEntry sym ret) f args {-^ The "stack" -} ->
    ThreadStateP p sym ext ret

  -- | A thread hit a a branch: since we don't really know how to merge different scheduler states,
  -- we'll end up just picking one direction and throwing the other away.
  BranchingThread ::
    Pred sym ->
    ValueFromFrame p sym ext (RegEntry sym ret) f ->
    PausedFrame p sym ext (RegEntry sym ret) f ->
    PausedFrame p sym ext (RegEntry sym ret) f ->
    ThreadStateP p sym ext ret

-- | The resources that this thread is about to touch.
nextResources :: ThreadStateP p sym ext ret -> [Resource Text]
nextResources ts =
  case ts of
    EmptyThread         -> []
    CompletedThread{}   -> []
    BranchingThread {}  -> []
    NewThread {}        -> []
    RunningThread r _ _ -> Set.toList $ condResource r

-- | The resources mentioned by the 'ResumeCond'
condResource :: ResumeCond -> Set.Set (Resource Text)
condResource = \case
  Resumable mres -> maybe mempty (Set.map Resource . snd) mres
  OnCond cv m _  -> Set.fromList [Resource cv, Resource m]
  OnJoin tid     -> Set.singleton (Thread tid)
  OnPred rs m    -> resumePredResource m <> Set.map Resource rs

-- | The resources mentioned by the 'ResumePred'
resumePredResource :: ResumePred -> Set.Set (Resource Text)
resumePredResource = \case
  ProgramVar r -> Set.singleton $ Resource r
  SchedulerVar r -> Set.singleton $ Resource r

-- | Build eventinfos corresponding to resuming the thread denoted by the given
-- state. Errors if the Direction is not NoDirection with any state other than
-- BranchingThread.
tsEventInfo ::
  ThreadStateP p sym ext ret ->
  Direction ->
  [EventInfo]
tsEventInfo ts dir =
  case ts of
    BranchingThread {} -> [Branch (dir == TBranch)]
    NewThread {}
      | dir == NoDirection -> [ThreadSpawn]
      | otherwise -> error "Direction given with NewThread"
    RunningThread rcond _ _
      | dir == NoDirection -> condEventInfo rcond
      | otherwise -> error "Direction given with RunningThread"
    EmptyThread
      | dir == NoDirection -> [ThreadExit]
      | otherwise -> error "Direction given with EmptyThread"
    CompletedThread{}
      | dir == NoDirection -> [ThreadExit]
      | otherwise -> error "Direction given with CompletedThread"
  where
    condEventInfo c =
      case c of
        OnJoin {} | dir == NoDirection -> [Join]
                  | otherwise          -> error "Direction given with Join"
        OnPred rs (ProgramVar m)       -> [Write (rs <> Set.singleton m)]
        OnPred rs (SchedulerVar m)     -> [Write (rs <> Set.singleton m)]
        OnCond gv m _                  -> [Write (Set.fromList [gv, m])]
        Resumable (Just (ro, r))       -> [if ro then Read r else Write r]
        Resumable Nothing              -> []

-- | Pretty print the thread state (useful for debugging).
ppThreadState :: ThreadStateP p sym ext ret -> [Char]
ppThreadState ts =
  case ts of
    EmptyThread -> "<empty>"
    CompletedThread{} -> "<done>"
    NewThread{} -> "<new>"
    BranchingThread{} -> "<branch>"
    RunningThread (OnJoin t) _ _ -> "<join: " ++ show (threadID t) ++ ">"
    RunningThread (OnPred _rs p) _ _ -> "<blocking on : " ++ show p ++ ">"
    RunningThread (OnCond c _m True) _ _ -> "<waiting (signaled): " ++ show c ++ ">"
    RunningThread (OnCond c _m False) _ _ -> "<waiting (blocked): " ++ show c ++ ">"
    RunningThread{} -> "<running>"
