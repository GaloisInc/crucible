{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Crux.Config.Solver (
  parseSolverConfig,
  SolverConfig(..),
  SolverOnline(..),
  SolverOffline(..),
  HasDefaultFloatRepr(..),
  sameSolver
  ) where

import           Control.Applicative ( (<|>), empty, Alternative )
import           Data.List.Split (wordsBy)
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import           Text.Printf ( printf )
import qualified What4.Expr.Builder as WEB
import qualified What4.InterpretedFloatingPoint as WIF

import qualified Crux.Config.Common as CCC

data SolverOnline = Yices | Z3 | CVC4 | CVC5 | STP | Bitwuzla
  deriving (Eq, Ord, Show)
data SolverOffline = SolverOnline SolverOnline | Boolector | DReal
  deriving (Eq, Ord, Show)

class HasDefaultFloatRepr solver where
  withDefaultFloatRepr ::
    st s ->
    solver ->
    (forall fm. (WIF.IsInterpretedFloatExprBuilder (WEB.ExprBuilder s st (WEB.Flags fm))) => WEB.FloatModeRepr fm -> a) ->
    a

instance HasDefaultFloatRepr SolverOnline where
  withDefaultFloatRepr _ s k =
    case s of
      CVC4 -> k WEB.FloatRealRepr
      CVC5 -> k WEB.FloatRealRepr
      STP -> k WEB.FloatRealRepr
      Yices -> k WEB.FloatRealRepr
      Z3 -> k WEB.FloatIEEERepr
      Bitwuzla -> k WEB.FloatIEEERepr

instance HasDefaultFloatRepr SolverOffline where
  withDefaultFloatRepr st s k =
    case s of
      SolverOnline s' -> withDefaultFloatRepr st s' k
      Boolector -> k WEB.FloatUninterpretedRepr
      DReal -> k WEB.FloatRealRepr

-- | Test to see if an online and offline solver are actually the same
sameSolver :: SolverOnline -> SolverOffline -> Bool
sameSolver o f =
  case f of
    SolverOnline s' -> o == s'
    _ -> False

data SolverConfig = SingleOnlineSolver SolverOnline
                  -- ^ Use a single online solver for both path satisfiability
                  -- checking and goal discharge

                  | OnlineSolverWithOfflineGoals SolverOnline SolverOffline
                  -- ^ Use an online solver for path satisfiability checking and
                  -- use an offline solver for goal discharge

                  | OnlineSolverWithSeparateOnlineGoals SolverOnline SolverOnline
                  -- ^ Use one online solver connection for path satisfiability
                  -- checking and a separate online solver connection for goal
                  -- discharge.  INVARIANT: the solvers must be distinct.

                  | OnlyOfflineSolvers [SolverOffline]
                  -- ^ Try any of a number of offline solvers with no support
                  -- for path satisfiability checking

-- | A type that contains a validated instance of a value or a list of messages
-- describing why it was not valid
--
-- This is basically `Either [String] a` but with instances that accumulate
-- error messages across alternatives unless there is a success.
data Validated a = Invalid [String] | Validated a
  deriving (Show, Functor, F.Foldable, T.Traversable)

validatedToEither :: Validated a -> Either [String] a
validatedToEither v =
  case v of
    Invalid rsns -> Left rsns
    Validated a -> Right a

instance Applicative Validated where
  pure = Validated
  Validated f <*> Validated a = Validated (f a)
  Validated _f <*> Invalid rsns = Invalid rsns
  Invalid rsns1 <*> Invalid rsns2 = Invalid (rsns1 <> rsns2)
  Invalid rsns <*> Validated _ = Invalid rsns

instance Alternative Validated where
  empty = Invalid []
  Validated a <|> _ = Validated a
  Invalid rsns1 <|> Invalid rsns2 = Invalid (rsns1 <> rsns2)
  Invalid _ <|> Validated a = Validated a

invalid :: String -> Validated a
invalid rsn = Invalid [rsn]

-- | Boolector and DReal only support offline solving (for our purposes), so
-- attempt to parse them from the given string
asOnlyOfflineSolver :: String -> Validated SolverOffline
asOnlyOfflineSolver s =
  case s of
    "dreal" -> pure DReal
    "boolector" -> pure Boolector
    _ -> invalid (printf "%s is not an offline-only solver (expected dreal or boolector)" s)

-- | Solvers that can be used in offline mode
asAnyOfflineSolver :: String -> Validated SolverOffline
asAnyOfflineSolver s = case s of
      "dreal" -> pure DReal
      "boolector" -> pure Boolector
      "z3" -> pure (SolverOnline Z3)
      "yices" -> pure (SolverOnline Yices)
      "cvc4" -> pure (SolverOnline CVC4)
      "cvc5" -> pure (SolverOnline CVC5)
      "stp" -> pure (SolverOnline STP)
      "bitwuzla" -> pure (SolverOnline Bitwuzla)
      _ -> invalid (printf "%s is not a valid solver (expected dreal, boolector, z3, yices, cvc4, cvc5, stp, or bitwuzla)" s)

asManyOfflineSolvers :: String -> Validated [SolverOffline]
asManyOfflineSolvers s
  | s == "all"         = asManyOfflineSolvers "dreal,boolector,z3,yices,cvc4,cvc5,stp,bitwuzla"
  | length solvers > 1 = traverse asAnyOfflineSolver solvers
  | otherwise          = invalid (printf "%s is not a valid solver list (expected 'all' or a comma separated list of solvers)" s)
  where
    solvers = wordsBy (== ',') s

-- | Attempt to parse the string as one of our solvers that supports online mode
asOnlineSolver :: String -> Validated SolverOnline
asOnlineSolver s =
  case s of
    "yices" -> pure Yices
    "cvc4" -> pure CVC4
    "cvc5" -> pure CVC5
    "z3" -> pure Z3
    "stp" -> pure STP
    "bitwuzla" -> pure Bitwuzla
    _ -> invalid (printf "%s is not a valid online solver (expected yices, cvc4, cvc5, z3, stp, or bitwuzla)" s)

-- | Examine a 'CCC.CruxOptions' and determine what solver configuration to use for
-- symbolic execution.  This can fail if an invalid solver configuration is
-- requested by the user.
--
-- The high level logic is that:
--
--  * If a user specifies only a single solver with the --solver option, that is
--    used as an online solver if possible for path sat checking (if requested)
--    and goal discharge.
--  * If the user specifies an explicit --path-sat-solver, that solver is used
--    for path satisfiability checking (if requested) while the solver specified
--    with --solver is used for goal discharge.
--  * The goal solver can be entirely offline (if it doesn't support online
--    mode) or if the user requests that it be used in offline mode with the
--    --force-offline-goal-solving option.
parseSolverConfig :: CCC.CruxOptions -> Either [String] SolverConfig
parseSolverConfig cruxOpts = validatedToEither $
  case (CCC.pathSatSolver cruxOpts, CCC.checkPathSat cruxOpts, CCC.forceOfflineGoalSolving cruxOpts) of
    (Nothing, True, False) ->
      -- No separate path sat checker was requested, but we do have to check
      -- path satisfiability.  That means that we have to use the one solver
      -- specified and it must be one that supports online solving
      trySingleOnline
    (Nothing, True, True) ->
      -- The user requested path satisfiability checking (using an online
      -- solver), but also wants to force goals to be discharged using the same
      -- solver in offline mode.
      OnlineSolverWithOfflineGoals <$> asOnlineSolver (CCC.solver cruxOpts) <*> asAnyOfflineSolver (CCC.solver cruxOpts)
    (Just _, False, False) ->
      -- The user specified a separate path sat checking solver, but did not
      -- request path satisfiability checking; we'll treat that as not asking
      -- for path satisfiability checking and just use a single online solver
      tryOnlyOffline <|> trySingleOnline
    (Just _, False, True) ->
      -- The user requested a separate path sat checking solver, but did not
      -- request path satisfiability checking.  They also requested that a
      -- separate solver be used for each goal (offline mode).  We'll use the
      -- specified solver as the only solver purely in offline mode.
      tryAnyOffline <|> tryManyOffline
    (Nothing, False, False) ->
      -- This is currently the same as the previous case, but the user
      -- explicitly selected no path sat checking
      tryOnlyOffline <|> trySingleOnline
    (Nothing, False, True) ->
      -- This is the same as the `(Just _, False, True)` case since we were just
      -- ignoring the unused path sat solver option.
      tryAnyOffline <|> tryManyOffline
    (Just onSolver, True, False) ->
      -- The user requested path sat checking and specified a solver
      --
      -- NOTE: We can still use the goal solver in online mode if it is supported

      -- In this case, the user requested a goal solver that is only usable as
      -- an offline solver
      (OnlineSolverWithOfflineGoals <$> asOnlineSolver onSolver <*> asOnlyOfflineSolver (CCC.solver cruxOpts)) <|>
        -- In this case, the requested solver can be used in online mode so we
        -- use it as such
        (onlineWithOnlineGoals <$> asOnlineSolver onSolver <*> asOnlineSolver (CCC.solver cruxOpts))

    (Just onSolver, True, True) ->
      -- In this case, the user requested separate solvers for path sat checking
      -- and goal discharge, but further requested that we force goals to be
      -- discharged with an offline solver.
      OnlineSolverWithOfflineGoals <$> asOnlineSolver onSolver <*> asAnyOfflineSolver (CCC.solver cruxOpts)
  where
    tryAnyOffline = OnlyOfflineSolvers . pure <$> asAnyOfflineSolver (CCC.solver cruxOpts)
    tryOnlyOffline = OnlyOfflineSolvers . pure <$> asOnlyOfflineSolver (CCC.solver cruxOpts)
    trySingleOnline = SingleOnlineSolver <$> asOnlineSolver (CCC.solver cruxOpts)
    tryManyOffline = OnlyOfflineSolvers <$> asManyOfflineSolvers (CCC.solver cruxOpts)

    onlineWithOnlineGoals s1 s2
      | s1 == s2  = SingleOnlineSolver s1
      | otherwise = OnlineSolverWithSeparateOnlineGoals s1 s2
