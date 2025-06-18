{-|
Module      : Lang.Crucible.Backend.ProofGoals
Copyright   : (c) Galois, Inc 2014-2018
License     : BSD3

This module defines a data structure ('GoalCollector') for storing the current
state of assumptions and a collection of proof obligations.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Lang.Crucible.Backend.ProofGoals
  ( -- * Goals
    ProofGoal(..), Goals(..), goalsToList, proveAll, goalsConj
    -- ** traversals
  , traverseGoals, traverseOnlyGoals
  , traverseGoalsWithAssumptions
  , traverseGoalsSeq

    -- * Goal collector
  , FrameIdentifier(..), GoalCollector
  , emptyGoalCollector
  , ppGoalCollector

    -- ** traversals
  , traverseGoalCollector
  , traverseGoalCollectorWithAssumptions

    -- ** Context management
  , gcAddAssumes, gcProve
  , gcPush, gcPop, gcAddGoals, gcAddTopLevelAssume,

    -- ** Global operations on context
    gcRemoveObligations, gcRestore, gcReset, gcFinish

    -- ** Viewing the assumption state
  , AssumptionFrames(..), gcFrames
  )
  where

import           Control.Monad.Reader
import qualified Data.Foldable as F
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Word (Word64)
import qualified Prettyprinter as PP

import           Lang.Crucible.Backend.Goals

-- | A @FrameIdentifier@ is a value that identifies an
--   an assumption frame.  These are expected to be unique
--   when a new frame is pushed onto the stack.  This is
--   primarily a debugging aid, to ensure that stack management
--   remains well-bracketed.
newtype FrameIdentifier = FrameIdentifier Word64
 deriving(Eq,Ord,Show)


-- | A data-structure that can incrementally collect goals in context.
--   It keeps track both of the collection of assumptions that lead to
--   the current state, as well as any proof obligations incurred along
--   the way.
--
--   The main use of 'GoalCollector' is as the state of an
--   'Lang.Crucible.Backend.AssumptionStack.AssumptionStack', which itself is
--   part of the state of the simple and online backends.
--
--   'GoalCollector' can be somewhat counter-intuitive. The "top"
--   ('TopCollector') is the *leaf* when 'GoalCollector' is considered as
--   a tree (which is a common way to conceptualize recursive algebraic
--   data types such as this one). A 'GoalCollector' is shaped like a
--   cons-list with three different cons-like constructors ('CollectorFrame',
--   'CollectingAssumptions', and 'CollectingGoals') and one nil-like
--   constructor 'TopCollector'. That is to say, a 'GoalCollector' is a sequence
--   that always ends in a single 'TopCollector'.
--
--   Furthermore, the frame identified by the first ('FrameIdentifier') argument
--   of 'CollectorFrame' does not conceptually contain the goals *inside* the
--   second ('GoalCollector') argument, but rather contains all the assumptions
--   and goals in whatever 'GoalCollector' *contains* the 'CollectorFrame'
--   constructor (everything *outside* of the 'CollectorFrame'). Concretely, in
--   the expression
--   @
--   'CollectingGoals' gls ('CollectingAssumptions' asmps ('CollectorFrame' frm ('TopCollector' gls0)))
--   @
--   the goals @gls@ and assumptions @asmps@ are in the frame @frm@, rather than
--   the top-level goals @gls0@.
--
--   This inside-out structure is reflected in the pretty-printer
--   'ppGoalCollector' below. The Crucible-CLI test-case @assumption-state@
--   shows this pretty-printer in action in a Crucible program with branching,
--   which can be helpful in understanding 'GoalCollector'.
data GoalCollector asmp goal
  = TopCollector !(Seq (Goals asmp goal))
  | CollectorFrame !FrameIdentifier !(GoalCollector asmp goal)
  | CollectingAssumptions !asmp !(GoalCollector asmp goal)
  | CollectingGoals !(Seq (Goals asmp goal)) !(GoalCollector asmp goal)

ppGoalCollector ::
  forall asmp goal ann.
  (asmp -> PP.Doc ann) ->
  (goal -> PP.Doc ann) ->
  GoalCollector asmp goal ->
  PP.Doc ann
ppGoalCollector ppAsmp ppGoal = go mempty
  where
    go :: PP.Doc ann -> GoalCollector asmp goal -> PP.Doc ann
    go remainder =
      \case
        TopCollector gls ->
          PP.vcat
          [ PP.pretty "Top-level goals:"
          , PP.list (map (ppGoals ppAsmp ppGoal) (F.toList gls))
          , remainder
          ]
        CollectorFrame (FrameIdentifier fid) gc ->
          let pLines = [PP.pretty "Frame " <> PP.viaShow fid <> PP.pretty ":", remainder] in
          go (PP.hang 2 (PP.vcat pLines)) gc
        CollectingAssumptions asmp gc ->
          let pLines = [PP.pretty "Assumptions:" , ppAsmp asmp, remainder] in
          go (PP.hang 2 (PP.vcat pLines)) gc
        CollectingGoals gls gc ->
          let pLines = [ PP.pretty "Prove all:"
                       , PP.list (map (ppGoals ppAsmp ppGoal) (F.toList gls))
                       , remainder
                       ] in
          go (PP.hang 2 (PP.vcat pLines)) gc

-- | Intended for debugging, this is not generally a user-facing datatype.
instance (PP.Pretty asmp, PP.Pretty goal) => PP.Pretty (GoalCollector asmp goal) where
  pretty = ppGoalCollector PP.pretty PP.pretty

-- | A collector with no goals and no context.
emptyGoalCollector :: GoalCollector asmp goal
emptyGoalCollector = TopCollector mempty

-- | Traverse the goals in a 'GoalCollector.  See 'traverseGoals'
--   for an explaination of the action arguments.
traverseGoalCollector :: (Applicative f, Monoid asmp') =>
  (forall a. asmp -> f a -> f (asmp', a)) ->
  (goal -> f (Maybe goal')) ->
  GoalCollector asmp goal -> f (GoalCollector asmp' goal')
traverseGoalCollector fas fgl = go
 where
 go (TopCollector gls) = TopCollector <$> traverseGoalsSeq fas fgl gls
 go (CollectorFrame fid gls) = CollectorFrame fid <$> go gls
 go (CollectingAssumptions asmps gls) = CollectingAssumptions <$> (fst <$> fas asmps (pure ())) <*> go gls
 go (CollectingGoals gs gls) = CollectingGoals <$> traverseGoalsSeq fas fgl gs <*> go gls

-- | Traverse the goals in a 'GoalCollector', keeping track,
--   for each goal, of the assumptions leading to that goal.
traverseGoalCollectorWithAssumptions :: (Applicative f, Monoid asmp) =>
  (asmp -> goal -> f (Maybe goal')) ->
  GoalCollector asmp goal -> f (GoalCollector asmp goal')
traverseGoalCollectorWithAssumptions f gc =
    runReaderT (traverseGoalCollector fas fgl gc) mempty
  where
  fas a m = (a,) <$> withReaderT (<> a) m
  fgl gl  = ReaderT $ \as -> f as gl


-- | The 'AssumptionFrames' data structure captures the current state of
--   assumptions made inside a 'GoalCollector'.
data AssumptionFrames asmp =
  AssumptionFrames
  { -- | Assumptions made at the top level of a solver.
    baseFrame    :: !asmp
    -- | A sequence of pushed frames, together with the assumptions that
    --   were made in each frame.  The sequence is organized with newest
    --   frames on the end (right side) of the sequence.
  , pushedFrames :: !(Seq (FrameIdentifier, asmp))
  }

-- | Return a list of all the assumption frames in this goal collector.
--   The first element of the pair is a collection of assumptions made
--   unconditionaly at top level.  The remaining list is a sequence of
--   assumption frames, each consisting of a collection of assumptions
--   made in that frame.  Frames closer to the front of the list
--   are older.  A `gcPop` will remove the newest (rightmost) frame from the list.
gcFrames :: forall asmp goal. Monoid asmp => GoalCollector asmp goal -> AssumptionFrames asmp
gcFrames = go mempty mempty
  where
  go ::
    asmp ->
    Seq (FrameIdentifier, asmp) ->
    GoalCollector asmp goal ->
    AssumptionFrames asmp

  go as fs (TopCollector _)
    = AssumptionFrames as fs

  go as fs (CollectorFrame frmid gc) =
    go mempty ((frmid, as) Seq.<| fs) gc

  go as fs (CollectingAssumptions as' gc) =
    go (as' <> as) fs gc

  go as fs (CollectingGoals _ gc) =
    go as fs gc

-- | Mark the current frame.  Using 'gcPop' will unwind to here.
gcPush :: FrameIdentifier -> GoalCollector asmp goal -> GoalCollector asmp goal
gcPush frmid gc = CollectorFrame frmid gc

gcAddGoals :: Goals asmp goal -> GoalCollector asmp goal -> GoalCollector asmp goal
gcAddGoals g (TopCollector gs) = TopCollector (gs Seq.|> g)
gcAddGoals g (CollectingGoals gs gc) = CollectingGoals (gs Seq.|> g) gc
gcAddGoals g gc = CollectingGoals (Seq.singleton g) gc

-- | Add an assumption that is in scope for all goals, even ones in earlier
-- frames.
gcAddTopLevelAssume ::
  Monoid asmp =>
  asmp ->
  GoalCollector asmp goal ->
  GoalCollector asmp goal
gcAddTopLevelAssume asmp =
  \case
    TopCollector gls ->
      -- Syntactically, it appears that `asmp` is duplicated here, perhaps
      -- unnecessarily. In fact, this is necessary. The `CollectingAssumptions`
      -- constructor brings the assumption into scope for all the goals
      -- *outside* of the top-level (see the comment on `GoalCollector` for
      -- the "inside-out" structure of `GoalCollector`), whereas the `assuming`
      -- brings it into scope for top-level goals.
      CollectingAssumptions asmp (TopCollector (assuming asmp <$> gls))
    CollectorFrame frm gc ->
      CollectorFrame frm (gcAddTopLevelAssume asmp gc)
    CollectingAssumptions asmp' gc ->
      CollectingAssumptions asmp' (gcAddTopLevelAssume asmp gc)
    CollectingGoals gls gc ->
      CollectingGoals gls (gcAddTopLevelAssume asmp gc)

-- | Add a new proof obligation to the current context.
gcProve :: goal -> GoalCollector asmp goal -> GoalCollector asmp goal
gcProve g = gcAddGoals (Prove g)

-- | Add a sequence of extra assumptions to the current context.
gcAddAssumes :: Monoid asmp => asmp -> GoalCollector asmp goal -> GoalCollector asmp goal
gcAddAssumes as' (CollectingAssumptions as gls) = CollectingAssumptions (as <> as') gls
gcAddAssumes as' gls = CollectingAssumptions as' gls

{- | Pop to the last push, or all the way to the top, if there were no more pushes.
If the result is 'Left', then we popped until an explicitly marked push;
in that case we return:

    1. the frame identifier of the popped frame,
    2. the assumptions that were forgotten,
    3. any proof goals that were generated since the frame push, and
    4. the state of the collector before the push.

If the result is 'Right', then we popped all the way to the top, and the
result is the goal tree, or 'Nothing' if there were no goals. -}

gcPop ::
  Monoid asmp =>
  GoalCollector asmp goal ->
  Either (FrameIdentifier, asmp, Maybe (Goals asmp goal), GoalCollector asmp goal)
         (Maybe (Goals asmp goal))
gcPop = go Nothing mempty
  where

  {- The function `go` completes frames one at a time.  The "hole" is what
     we should use to complete the current path.  If it is 'Nothing', then
     there was nothing interesting on the current path, and we discard
     assumptions that lead to here -}
  go hole _as (TopCollector gs) =
    Right (goalsConj (proveAll gs) hole)

  go hole as (CollectorFrame fid gc) =
    Left (fid, as, hole, gc)

  go hole as (CollectingAssumptions as' gc) =
    go (assuming as' <$> hole) (as' <> as) gc

  go hole as (CollectingGoals gs gc) =
    go (goalsConj (proveAll gs) hole) as gc

-- | Get all currently collected goals.
gcFinish :: Monoid asmp => GoalCollector asmp goal -> Maybe (Goals asmp goal)
gcFinish gc = case gcPop gc of
                Left (_,_,Just g,gc1)  -> gcFinish (gcAddGoals g gc1)
                Left (_,_,Nothing,gc1) -> gcFinish gc1
                Right a -> a

-- | Reset the goal collector to the empty assumption state; but first
--   collect all the pending proof goals and stash them.
gcReset :: Monoid asmp => GoalCollector asmp goal -> GoalCollector asmp goal
gcReset gc = TopCollector gls
  where
  gls = case gcFinish gc of
          Nothing     -> mempty
          Just p      -> Seq.singleton p

pushGoalsToTop :: Goals asmp goal -> GoalCollector asmp goal -> GoalCollector asmp goal
pushGoalsToTop gls = go
 where
 go (TopCollector gls') = TopCollector (gls' Seq.|> gls)
 go (CollectorFrame fid gc) = CollectorFrame fid (go gc)
 go (CollectingAssumptions as gc) = CollectingAssumptions as (go gc)
 go (CollectingGoals gs gc) = CollectingGoals gs (go gc)

-- | This operation restores the assumption state of the first given
--   `GoalCollector`, overwriting the assumptions state of the second
--   collector.  However, all proof obligations in the second collector
--   are retained and placed into the the first goal collector in the
--   base assumption level.
--
--   The end result is a goal collector that maintains all the active
--   proof obligations of both collectors, and has the same
--   assumption context as the first collector.
gcRestore ::
  Monoid asmp =>
  GoalCollector asmp goal {- ^ The assumption state to restore -} ->
  GoalCollector asmp goal {- ^ The assumptions state to overwrite -} ->
  GoalCollector asmp goal
gcRestore restore old =
  case gcFinish old of
    Nothing -> restore
    Just p  -> pushGoalsToTop p restore

-- | Remove all collected proof obligations, but keep the current set
-- of assumptions.
gcRemoveObligations :: Monoid asmp => GoalCollector asmp goal -> GoalCollector asmp goal
gcRemoveObligations = go
 where
 go (TopCollector _) = TopCollector mempty
 go (CollectorFrame fid gc) = CollectorFrame fid (go gc)
 go (CollectingAssumptions as gc) =
      case go gc of
        CollectingAssumptions as' gc' -> CollectingAssumptions (as <> as') gc'
        gc' -> CollectingAssumptions as gc'
 go (CollectingGoals _ gc) = go gc
