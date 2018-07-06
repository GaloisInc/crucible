
-- | This module defines a data strucutre for storing a collection of
-- proof obligations.
module Lang.Crucible.Backend.ProofGoals
  ( Goals(..), goalsToList
  , GoalCollector
  , emptyGoalCollector, gcAssume, gcProve, gcPush, gcPop, gcFinish
  )
  where

-- | A collection of goals, which can represent shared assumptions.
data Goals asmp goal =
    Assuming asmp (Goals asmp goal)
  | Prove goal
  | ProveAll [Goals asmp goal]
    deriving Show

goalsToList :: Goals asmp goal -> [([asmp],goal)]
goalsToList = go []
  where
  go as gs =
    case gs of
      Assuming a gs1 -> go (a : as) gs1
      Prove p        -> [(as,p)]
      ProveAll gss   -> concatMap (go as) gss


-- | A data-strucutre that can incrementally collect goals in context.
data GoalCollector asmp goal = GoalCollector
  { gcCurDone   :: [Goals asmp goal]
    -- ^ Siblings in the current context that are already build.

  , gcCurAsmps  :: [asmp]
    -- ^ Assumptions for the child under construction.

  , gcIsPushFrame  :: Bool
    -- ^ Is this a frame that came from a "push" instruction.
    -- The @pop@ command will stop unwinding when it sees a frame
    -- with this flag set to 'True'

  , gcContext :: Maybe (GoalCollector asmp goal)
    -- ^ This the context for the current goal under construction.
  }

-- | A collector with no goals and no context.
emptyGoalCollector :: GoalCollector asmp goal
emptyGoalCollector = GoalCollector
  { gcCurDone     = []
  , gcCurAsmps    = []
  , gcIsPushFrame = False
  , gcContext     = Nothing
  }

-- | Mark the current frame.  Using 'gcPop' will unwind to here.
gcPush :: GoalCollector asmp goal -> GoalCollector asmp goal
gcPush gc = GoalCollector { gcCurDone     = []
                          , gcCurAsmps    = []
                          , gcIsPushFrame = True
                          , gcContext       = Just gc
                          }

-- | Add a new proof obligation to the current context.
gcProve :: goal -> GoalCollector asmp goal -> GoalCollector asmp goal
gcProve g gc =
  case gcCurAsmps gc of
    [] -> gc { gcCurDone = Prove g : gcCurDone gc }
    _  -> GoalCollector { gcCurDone     = [Prove g]
                        , gcCurAsmps    = []
                        , gcIsPushFrame = False
                        , gcContext       = Just gc
                        }

-- | Add an extra assumptions to the current context.
gcAssume :: asmp -> GoalCollector asmp goal -> GoalCollector asmp goal
gcAssume a gc = gc { gcCurAsmps = a : gcCurAsmps gc }

-- | Pop to the last push, or all the way to the top,
-- if there were no more pushed.
gcPop :: GoalCollector asmp goal ->
          Either (GoalCollector asmp goal) (Goals asmp goal)
gcPop = go Nothing
  where
  go hole gc =
    case gcContext gc of

      -- Reached the top
      Nothing -> Right $ case newHole of
                           Nothing -> ProveAll []
                           Just p  -> p

      -- More frames
      Just prev
        | gcIsPushFrame gc ->
          Left $ case newHole of
                   Nothing -> prev
                   Just p  -> prev { gcCurDone = p : gcCurDone prev }

        | otherwise -> go newHole prev



    where
    newHole  = case newChildren of
                     []  -> Nothing
                     [p] -> Just p
                     ps  -> Just (ProveAll ps)

    newChildren =
          case hole of
            Nothing -> gcCurDone gc
            Just p  -> foldl (flip Assuming) p (gcCurAsmps gc) : gcCurDone gc

-- | Get all currently collected goals.
gcFinish :: GoalCollector asmp goal -> Goals asmp goal
gcFinish gc = case gcPop gc of
                Left gc1 -> gcFinish gc1
                Right a  -> a


