{-|
Module      : Lang.Crucible.Backend.Goals
Copyright   : (c) Galois, Inc 2025
License     : BSD3

This module defines a data strucutre for storing a collection of
proof obligations, and the current state of assumptions.
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Lang.Crucible.Backend.Goals
  ( ProofGoal(..)
  , Goals(..)
  , goalsToList
  , assuming
  , proveAll
  , goalsConj
    -- * Traversals
  , traverseGoals
  , traverseOnlyGoals
  , traverseGoalsWithAssumptions
  , traverseGoalsSeq
  )
  where

import           Control.Monad.Reader (ReaderT(..), withReaderT)
import           Data.Functor.Const (Const(..))
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

-- | A proof goal consists of a collection of assumptions
--   that were in scope when an assertion was made, together
--   with the given assertion.
data ProofGoal asmp goal =
  ProofGoal
  { proofAssumptions :: asmp
  , proofGoal        :: goal
  }

-- | A collection of goals, which can represent shared assumptions.
data Goals asmp goal =
    -- | Make an assumption that is in context for all the
    --   contained goals.
    Assuming asmp !(Goals asmp goal)

    -- | A proof obligation, to be proved in the context of
    --   all previously-made assumptions.
  | Prove goal

    -- | A conjunction of two goals.
  | ProveConj !(Goals asmp goal) !(Goals asmp goal)
    deriving Show

-- | Construct a goal that first assumes a collection of
--   assumptions and then states a goal.
assuming :: Monoid asmp => asmp -> Goals asmp goal -> Goals asmp goal
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
goalsConj Nothing y = y
goalsConj x Nothing = x
goalsConj (Just x) (Just y) = Just (ProveConj x y)

-- | Render the tree of goals as a list instead, duplicating
--   shared assumptions over each goal as necessary.
goalsToList :: Monoid asmp => Goals asmp goal -> [ProofGoal asmp goal]
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
traverseGoals :: (Applicative f, Monoid asmp') =>
                 (forall a. asmp -> f a -> f (asmp', a))
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


traverseOnlyGoals :: (Applicative f, Monoid asmp) =>
  (goal -> f (Maybe goal')) ->
  Goals asmp goal -> f (Maybe (Goals asmp goal'))
traverseOnlyGoals f = traverseGoals (\as m -> (as,) <$> m) f

-- | Traverse a sequence of 'Goals' data structures.  See 'traverseGoals'
--   for an explanation of the action arguments.  The resulting sequence
--   may be shorter than the original if some 'Goals' become trivial.
traverseGoalsSeq :: (Applicative f, Monoid asmp') =>
  (forall a. asmp -> f a -> f (asmp', a)) ->
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
traverseGoalsWithAssumptions :: (Applicative f, Monoid asmp) =>
  (asmp -> goal -> f (Maybe goal')) ->
  Goals asmp goal -> f (Maybe (Goals asmp goal'))

traverseGoalsWithAssumptions f gls =
   runReaderT (traverseGoals fas fgl gls) mempty
  where
  fas a m = (a,) <$> withReaderT (<> a) m
  fgl gl  = ReaderT $ \as -> f as gl

