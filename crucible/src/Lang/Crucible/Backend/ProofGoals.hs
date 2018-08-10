{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

{-|
Module      : Lang.Crucible.Backend.ProofGoals
Copyright   : (c) Galois, Inc 2014-2018
License     : BSD3

This module defines a data strucutre for storing a collection of
proof obligations, and the current state of assumptions.
-}
module Lang.Crucible.Backend.ProofGoals
  ( -- * Goals
    ProofGoal(..), Goals(..), goalsToList, proveAll, goalsConj, assuming
    -- ** traversals
  , traverseGoals, traverseOnlyGoals
  , traverseGoalsWithAssumptions
  , traverseGoalsSeq

    -- * Goal collector
  , FrameIdentifier(..), GoalCollector
  , emptyGoalCollector

    -- ** traversals
  , traverseGoalCollector
  , traverseGoalCollectorWithAssumptions

    -- ** Context management
  , gcAssume, gcAddAssumes, gcProve
  , gcPush, gcPop,

    -- ** Global operations on context
    gcRemoveObligations, gcRestore, gcReset, gcFinish

    -- ** Viewing the assumption state
  , AssumptionFrames(..), gcFrames
  )
  where

import           Control.Monad.Reader
import           Data.Functor.Const
import           Data.Semigroup
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Word


-- | A proof goal consists of a collection of assumptions
--   that were in scope when an assertion was made, together
--   with the given assertion.
data ProofGoal asmp goal =
  ProofGoal
  { proofAssumptions :: Seq asmp
  , proofGoal        :: goal
  }

-- | A collection of goals, which can represent shared assumptions.
data Goals asmp goal =
    -- | Make an assumption that is in context for all the
    --   contained goals.
    Assuming (Seq asmp) !(Goals asmp goal)

    -- | A proof obligation, to be proved in the context of
    --   all previously-made assumptions.
  | Prove goal

    -- | A conjunction of two goals.
  | ProveConj !(Goals asmp goal) !(Goals asmp goal)
    deriving Show

-- | Construct a goal that first assumes a collection of
--   assumptions and then states a goal.
assuming :: Seq asmp -> Goals asmp goal -> Goals asmp goal
assuming Seq.Empty g = g
assuming as (Assuming bs g) = assuming (as <> bs) g
assuming as g = Assuming as g

-- | Construct a 'Goals' object from a collection of subgoals, all of
--   which are to be proved.  This yields 'Nothing' if the collection
--   of goals is empty, and otherwise builds a conjunction of all the
--   goals.  Note that there is no new sharing in the resulting structure.
proveAll :: Foldable t => t (Goals asmp goal) -> Maybe (Goals asmp goal)
proveAll = foldr f Nothing
 where
 f x Nothing  = Just $! x
 f x (Just y) = Just $! ProveConj x y

-- | Helper to conjoin two possibly trivial 'Goals' objects.
goalsConj :: Maybe (Goals asmp goal) -> Maybe (Goals asmp goal) -> Maybe (Goals asmp goal)
goalsConj x y =
  case x of
    Nothing -> y
    Just xg -> case y of
                 Nothing -> x
                 Just yg -> Just (ProveConj xg yg)

-- | Render the tree of goals as a list instead, duplicating
--   shared assumptions over each goal as necessary.
goalsToList :: Goals asmp goal -> [ProofGoal asmp goal]
goalsToList =
  getConst . traverseGoalsWithAssumptions
    (\as g -> Const [ProofGoal as g])

-- | Traverse the structure of a 'Goals' data structure.  The function for
--   visiting goals my decide to remove the goal from the structure.  If
--   no goals remain after the traversal, the resulting value will be a 'Nothing'.
--
--   In a call to 'traverseGoals assumeAction transformer goals', the
--   arguments are used as follows:
--
--   * 'traverseGoals' is an action is called every time we encounter
--     an 'Assuming' constructor.  The first argument is the original
--     sequence of assumptions.  The second argument is a continuation
--     action.  The result is a sequence of transformed assumptions
--     and the result of the continuation action.
--
--   * 'assumeAction' is a transformer action on goals.  Return
--     'Nothing' if you wish to remove the goal from the overall tree.
traverseGoals :: Applicative f =>
                 (forall a. Seq asmp -> f a -> f (Seq asmp', a))
              -> (goal -> f (Maybe goal'))
              -> Goals asmp goal
              -> f (Maybe (Goals asmp' goal'))
traverseGoals fas fgl = go
  where
  go (Prove gl)        = fmap Prove <$> fgl gl
  go (Assuming as gl)  = assuming' <$> fas as (go gl)
  go (ProveConj g1 g2) = goalsConj <$> go g1 <*> go g2

  assuming' (_, Nothing) = Nothing
  assuming' (as, Just g) = Just $! assuming as g


traverseOnlyGoals :: Applicative f =>
  (goal -> f (Maybe goal')) ->
  Goals asmp goal -> f (Maybe (Goals asmp goal'))
traverseOnlyGoals f = traverseGoals (\as m -> (as,) <$> m) f

-- | Traverse a sequence of 'Goals' data structures.  See 'traverseGoals'
--   for an explaination of the action arguments.  The resulting sequence
--   may be shorter than the original if some 'Goals' become trivial.
traverseGoalsSeq :: Applicative f =>
  (forall a. Seq asmp -> f a -> f (Seq asmp', a)) ->
  (goal -> f (Maybe goal')) ->
  Seq (Goals asmp goal) -> f (Seq (Goals asmp' goal'))
traverseGoalsSeq fas fgl = go
  where
  go Seq.Empty      = pure Seq.Empty
  go (g Seq.:<| gs) = combine <$> traverseGoals fas fgl g <*> go gs

  combine Nothing gs  = gs
  combine (Just g) gs = g Seq.<| gs

-- | Visit every goal in a 'Goals' structure, remembering the sequence of
--   assumptions along the way to that goal.
traverseGoalsWithAssumptions :: Applicative f =>
  (Seq asmp -> goal -> f (Maybe goal')) ->
  Goals asmp goal -> f (Maybe (Goals asmp goal'))

traverseGoalsWithAssumptions f gls =
   runReaderT (traverseGoals fas fgl gls) mempty
  where
  fas a m = (a,) <$> withReaderT (<> a) m
  fgl gl  = ReaderT $ \as -> f as gl


-- | A @FrameIdentifier@ is a value that identifies an
--   an assumption frame.  These are expected to be unique
--   when a new frame is pushed onto the stack.  This is
--   primarily a debugging aid, to ensure that stack management
--   remains well-bracketed.
newtype FrameIdentifier = FrameIdentifier Word64
 deriving(Eq,Ord)


-- | A data-strucutre that can incrementally collect goals in context.
--   It keeps track both of the collection of assumptions that lead to
--   the current state, as well as any proof obligations incurred along
--   the way.
data GoalCollector asmp goal = GoalCollector
  { gcCurDone   :: !(Seq (Goals asmp goal))
    -- ^ Siblings in the current context that are already build.

  , gcCurAsmps  :: !(Seq asmp)
    -- ^ Assumptions for the child under construction.
    -- These are *not* in scope for 'gcCurDone'.

  , gcIsPushFrame  :: !(Maybe FrameIdentifier)
    -- ^ Is this a frame that came from a "push" instruction.
    -- The @pop@ command will stop unwinding when it sees a frame
    -- with this flag set to 'True'

  , gcContext :: !(Maybe (GoalCollector asmp goal))
    -- ^ These are the goals and assumptions further up the tree from here.
    -- The assumptions of the current path are `gcCurAsmps` together
    -- with all the assumptions in `gcContext`.
  }

-- | A collector with no goals and no context.
emptyGoalCollector :: GoalCollector asmp goal
emptyGoalCollector = GoalCollector
  { gcCurDone     = mempty
  , gcCurAsmps    = mempty
  , gcIsPushFrame = Nothing
  , gcContext     = Nothing
  }

-- | Traverse the goals in a 'GoalCollector.  See 'traverseGoals'
--   for an explaination of the action arguments.
traverseGoalCollector :: Applicative f =>
  (forall a. Seq asmp -> f a -> f (Seq asmp', a)) ->
  (goal -> f (Maybe goal')) ->
  GoalCollector asmp goal -> f (GoalCollector asmp' goal')
traverseGoalCollector fas fgl = go
 where
 go (GoalCollector gls asmps pf ctx) =
       GoalCollector
         <$> traverseGoalsSeq fas fgl gls
         <*> (fst <$> fas asmps (pure ()))
         <*> pure pf
         <*> traverse go ctx

-- | Traverse the goals in a 'GoalCollector', keeping track,
--   for each goal, of the assumptions leading to that goal.
traverseGoalCollectorWithAssumptions :: Applicative f =>
  (Seq asmp -> goal -> f (Maybe goal')) ->
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
  { -- | A sequence of assumptions made at the top level of a solver.
    baseFrame    :: Seq asmp
    -- | A sequence of pushed frames, together with the assumptions that
    --   were made in each frame.  The sequence is organized with newest
    --   frames on the end (right side) of the sequence.
  , pushedFrames :: Seq (FrameIdentifier, Seq asmp)
  }

-- | Return a list of all the assumption frames in this goal collector.
--   The first element of the pair is a collection of assumptions made
--   unconditionaly at top level.  The remaining list is a sequence of
--   assumption frames, each consisting of a collection of assumptions
--   made in that frame.  Frames closer to the front of the list
--   are older.  A `gcPop` will remove the newest (rightmost) frame from the list.
gcFrames :: GoalCollector asmp goal -> (Seq asmp, Seq (FrameIdentifier, Seq asmp))
gcFrames = go mempty mempty . Just
  where
  go ::
    Seq asmp ->
    Seq (FrameIdentifier, Seq asmp) ->
    Maybe (GoalCollector asmp goal) ->
    (Seq asmp, Seq (FrameIdentifier, Seq asmp))

  go as fs Nothing
    = (as, fs)

  go as fs (Just gc)
    | Just frmid <- gcIsPushFrame gc
    = go mempty ((frmid, gcCurAsmps gc <> as) Seq.<| fs) (gcContext gc)

    | otherwise
    = go (gcCurAsmps gc <> as) fs (gcContext gc)


-- | Mark the current frame.  Using 'gcPop' will unwind to here.
gcPush :: FrameIdentifier -> GoalCollector asmp goal -> GoalCollector asmp goal
gcPush frmid gc =
   GoalCollector { gcCurDone     = mempty
                 , gcCurAsmps    = mempty
                 , gcIsPushFrame = Just frmid
                 , gcContext     = Just gc
                 }

-- | Add a new proof obligation to the current context.
gcProve :: goal -> GoalCollector asmp goal -> GoalCollector asmp goal
gcProve g gc =
  if Seq.null (gcCurAsmps gc) then
    {- If we don't have any new assumptions, then we don't need to push
       a new assumptions frame: instead we can just add the proof obligations
       as a sibling. -}

    gc { gcCurDone = gcCurDone gc Seq.|> Prove g }
  else
    {- If we do have assumptions, then we need to start a new frame,
       as the current assumptions are the only ones that should be in
       in scope for the new proof obligations. -}
    GoalCollector { gcCurDone     = Seq.singleton (Prove g)
                  , gcCurAsmps    = mempty
                  , gcIsPushFrame = Nothing
                  , gcContext     = Just gc
                  }

-- | Add an extra assumption to the current context.
gcAssume :: asmp -> GoalCollector asmp goal -> GoalCollector asmp goal
gcAssume a gc = gc { gcCurAsmps = gcCurAsmps gc Seq.|> a }

-- | Add a sequence of extra assumptions to the current context.
gcAddAssumes :: Seq asmp -> GoalCollector asmp goal -> GoalCollector asmp goal
gcAddAssumes as gc = gc { gcCurAsmps = gcCurAsmps gc <> as }

-- | Pop to the last push, or all the way to the top,
-- if there were no more pushed.
gcPop ::
  GoalCollector asmp goal ->
  Either (FrameIdentifier, Seq asmp, GoalCollector asmp goal)
         (Maybe (Goals asmp goal))
gcPop = go Nothing mempty
  where

  {- The function `go` completes frames one at a time.  The "hole" is what
     we should use to complete the current path.  If it is 'Nothing', then
     there was nothing interesting on the current path, and we discard
     assumptions that lead to here -}
  go hole as gc =
    case gcContext gc of

      -- Reached the top
      Nothing -> Right newHole

      -- More frames
      Just prev
        | Just frmid <- gcIsPushFrame gc ->
          -- This was a push frame, so we should stop right here.
          Left ( frmid
               , newAs
               , case newHole of
                    Nothing -> prev
                    Just p  -> prev { gcCurDone = gcCurDone prev Seq.|> p }
               )

         -- Keep unwinding, using the newly constructed child.
        | otherwise -> go newHole newAs prev

    where
    newAs = gcCurAsmps gc <> as

    -- Turn the new children into a new item to fill in the parent context.
    newHole = proveAll newChildren

    {- The new children consist of the already complete children, 'gcCurDone',
       and potentially a new child, if the current path was filled with
       something interesting. -}
    newChildren =
          case hole of
            Nothing -> gcCurDone gc
            Just p  -> gcCurDone gc Seq.|> assuming (gcCurAsmps gc) p
            -- NB, no need to assume all of 'newAs' here, the goals in
            -- 'p' will already have assumed the hypotheses in 'as'

-- | Get all currently collected goals.
gcFinish :: GoalCollector asmp goal -> Maybe (Goals asmp goal)
gcFinish gc = case gcPop gc of
                Left (_,_,gc1) -> gcFinish gc1
                Right a        -> a


-- | Reset the goal collector to the empty assumption state; but first
--   collect all the pending proof goals and stash them.
gcReset :: GoalCollector asmp goal -> GoalCollector asmp goal
gcReset gc =
    GoalCollector
    { gcCurDone     = gls
    , gcCurAsmps    = mempty
    , gcIsPushFrame = Nothing
    , gcContext     = Nothing
    }
  where
  gls = case gcFinish gc of
          Nothing     -> mempty
          Just p      -> Seq.singleton p

pushGoalsToTop :: Goals asmp goal -> GoalCollector asmp goal -> GoalCollector asmp goal
pushGoalsToTop gls = go
 where
 go gc =
  case gcContext gc of
    Nothing  -> gc{ gcCurDone = gls Seq.<| gcCurDone gc }
    Just gc' -> gc{ gcContext = Just $! go gc' }

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
  GoalCollector asmp goal {- ^ The assumption state to restore -} ->
  GoalCollector asmp goal {- ^ The assumptions state to overwrite -} ->
  GoalCollector asmp goal
gcRestore restore old =
  case gcFinish old of
    Nothing -> restore
    Just p  -> pushGoalsToTop p restore

-- | Remove all collected proof obligations, but keep the current set
-- of assumptions.
gcRemoveObligations :: GoalCollector asmp goal -> GoalCollector asmp goal
gcRemoveObligations gc = gc { gcCurDone = mempty
                            , gcContext = gcRemoveObligations <$> gcContext gc
                            }
