{-|
Module      : Lang.Crucible.Backend
Copyright   : (c) Galois, Inc 2014-2016
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides an interface that symbolic backends must provide
for interacting with the symbolic simulator.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
module Lang.Crucible.Backend
  ( BranchResult(..)
  , IsBoolSolver(..)
  , IsSymInterface

    -- * Assumption management
  , AssumptionReason(..)
  , ppAssumptionReason
  , assumptionLoc
  , Assertion
  , Assumption
  , ProofObligation
  , ProofObligations
  , AssumptionState
  , assert

    -- ** Reexports
  , AS.LabeledPred(..)
  , AS.labeledPred
  , AS.labeledPredMsg
  , AS.ProofGoal(..)
  , AS.AssumptionStack
  , AS.FrameIdentifier
  , AS.ProofGoals
  , AS.Goals(..)
  , AS.proofGoalsToList

    -- ** Aborting execution
  , AbortExecReason(..)
  , abortExecBecause
  , ppAbortExecReason

    -- * Utilities
  , addAssertion
  , addAssertionM
  , addFailedAssertion
  , assertIsInteger
  , readPartExpr
  ) where

import           Data.Sequence (Seq)
import           Control.Exception(Exception(..), throwIO)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Interface
import           What4.Partial
import           What4.ProgramLoc

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import           Lang.Crucible.Simulator.SimError

data AssumptionReason =
    AssumptionReason ProgramLoc String
    -- ^ An unstructured description of the source of an assumption.

  | ExploringAPath ProgramLoc (Maybe ProgramLoc)
    -- ^ This arose because we want to explore a specific path.
    -- The first location is the location of the branch predicate.
    -- The second one is the location of the branch target.

  | AssumingNoError SimError
    -- ^ An assumption justified by a proof of the impossibility of
    -- a certain simulator error.
    deriving Show


assumptionLoc :: AssumptionReason -> ProgramLoc
assumptionLoc r =
  case r of
    AssumptionReason l _ -> l
    ExploringAPath l _   -> l
    AssumingNoError s    -> simErrorLoc s

instance AS.AssumeAssert AssumptionReason SimError where
  assertToAssume = AssumingNoError


type Assertion sym  = AS.LabeledPred (Pred sym) SimError
type Assumption sym = AS.LabeledPred (Pred sym) AssumptionReason
type ProofObligation sym = AS.ProofGoal (Assumption sym) (Assertion sym)
type ProofObligations sym = Maybe (AS.ProofGoals (Pred sym) AssumptionReason SimError)
type AssumptionState sym = AS.LabeledGoalCollector (Pred sym) AssumptionReason SimError

-- | This is used to signal that current execution path is infeasible.
data AbortExecReason =
    InfeasibleBranch
    -- ^ We tried to decide which way to go at a branch point,
    -- but neither option is viable.

  | AssumedFalse AssumptionReason
    -- ^ We assumed false on some branch

  | VariantOptionsExhaused ProgramLoc
    -- ^ We tried all possible cases for a variant, and now we should
    -- do something else.

    deriving Show

instance Exception AbortExecReason


ppAbortExecReason :: AbortExecReason -> PP.Doc
ppAbortExecReason e =
  case e of
    InfeasibleBranch -> "Abort an infeasible branch."
    AssumedFalse reason ->
      "Abort due to false assumption:" PP.<$$>
      PP.indent 2 (ppAssumptionReason reason)
    VariantOptionsExhaused l -> ppLocated l "Variant options exhaused."

ppAssumptionReason :: AssumptionReason -> PP.Doc
ppAssumptionReason e =
  case e of
    AssumptionReason l msg -> ppLocated l (PP.text msg)
    ExploringAPath l Nothing -> "The branch at " PP.<+> ppLoc l
    ExploringAPath l (Just t) ->
        "The branch from" PP.<+> ppLoc l PP.<+> "to" PP.<+> ppLoc t
    AssumingNoError simErr -> ppSimError simErr

ppLocated :: ProgramLoc -> PP.Doc -> PP.Doc
ppLocated l x = ppLoc l PP.<> ":" PP.<+> x

ppLoc :: ProgramLoc -> PP.Doc
ppLoc l = PP.pretty (plSourceLoc l)

-- | Result of attempting to branch on a predicate.
data BranchResult
     -- | Branch is symbolic.
     --
     -- The Boolean value indicates whether the backend suggests that the active
     -- path should be the case where the condition is true or false.
   = SymbolicBranch !Bool

     -- | No branch is needed, and the predicate is evaluated to the
     -- given value.
   | NoBranch !Bool

type IsSymInterface sym = (IsBoolSolver sym, IsSymExprBuilder sym)

-- | This class provides operations that interact with the symbolic simulator.
--   It allows for logical assumptions/assertions to be added to the current
--   path condition, and allows queries to be asked about branch conditions.
class IsBoolSolver sym where

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Given a Boolean predicate that the simulator wishes to branch on,
  --   this decides what the next course of action should be for the branch.
  evalBranch :: sym
             -> Pred sym -- Predicate to branch on.
             -> IO BranchResult

  -- | Push a new assumption frame onto the stack.  Assumptions and assertions
  --   made will now be associated with this frame on the stack until a new
  --   frame is pushed onto the stack, or until this one is popped.
  pushAssumptionFrame :: sym -> IO AS.FrameIdentifier

  -- | Pop an assumption frame from the stack.  The collected assumptions
  --   in this frame are returned.  Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
  popAssumptionFrame :: sym -> AS.FrameIdentifier -> IO (Seq (Assumption sym))

  ----------------------------------------------------------------------
  -- Assertions

  -- | Add an assumption to the current state.  Like assertions, assumptions
  --   add logical facts to the current path condition.  However, assumptions
  --   do not produce proof obligations the way assertions do.
  addAssumption :: sym -> Assumption sym -> IO ()

  -- | Add a collection of assumptions to the current state.
  addAssumptions :: sym -> Seq (Assumption sym) -> IO ()

  -- | Get the current path condition as a predicate.  This consists of the conjunction
  --   of all the assumptions currently in scope.
  getPathCondition :: sym -> IO (Pred sym)

  collectAssumptions :: sym -> IO (Seq (Assumption sym))

  -- | Add a new proof obligation to the system.
  -- The proof may use the current path condition and assumptions.
  -- Note that this *DOES NOT* add the goal as an assumption.
  -- See also 'addAssertion'.
  addProofObligation :: sym -> Assertion sym -> IO ()

  -- | Get the collection of proof obligations.
  getProofObligations :: sym -> IO (ProofObligations sym)

  -- | Forget the current collection of proof obligations.
  -- Presumably, we've already used 'getPathConditions' to save them
  -- somewhere else.
  clearProofObligations :: sym -> IO ()

  -- | Create a snapshot of the current assumption state, that may later be restored.
  --   This is useful for supporting control-flow patterns that don't neatly fit into
  --   the stack push/pop model.
  saveAssumptionState :: sym -> IO (AssumptionState sym)

  -- | Restore the assumption state to a previous snapshot.
  restoreAssumptionState :: sym -> AssumptionState sym -> IO ()


-- | Add a proof obligation for the given predicate, and then assume it.
-- Note that assuming the prediate might cause the current execution
-- path to abort, if we happened to assume something that is obviously false.
addAssertion :: IsSymInterface sym => sym -> Assertion sym -> IO ()
addAssertion sym a@(AS.LabeledPred p msg) =
  do addProofObligation sym a
     addAssumption sym (AS.LabeledPred p (AssumingNoError msg))


-- | Throw an exception, thus aborting the current execution path.
abortExecBecause :: AbortExecReason -> IO a
abortExecBecause err = throwIO err

-- | Add a proof obligation using the current program location.
--   Afterwards, assume the given fact.
assert ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  SimErrorReason ->
  IO ()
assert sym p msg =
  do loc <- getCurrentProgramLoc sym
     addAssertion sym (AS.LabeledPred p (SimError loc msg))

-- | Add a proof obligation for False. This always aborts execution
-- of the current path, because after asserting false, we get to assume it,
-- and so there is no need to check anything after.  This is why the resulting
-- IO computation can have the fully polymorphic type.
addFailedAssertion :: IsSymInterface sym => sym -> SimErrorReason -> IO a
addFailedAssertion sym msg =
  do loc <- getCurrentProgramLoc sym
     let err = AS.LabeledPred (falsePred sym) (SimError loc msg)
     addProofObligation sym err
     abortExecBecause $ AssumedFalse
                      $ AssumingNoError
                        SimError { simErrorLoc = loc, simErrorReason = msg }




-- | Run the given action to compute a predicate, and assert it.
addAssertionM :: IsSymInterface sym
              => sym
              -> IO (Pred sym)
              -> SimErrorReason
              -> IO ()
addAssertionM sym pf msg = do
  p <- pf
  assert sym p msg

-- | Assert that the given real-valued expression is an integer.
assertIsInteger :: IsSymInterface sym
                => sym
                -> SymReal sym
                -> SimErrorReason
                -> IO ()
assertIsInteger sym v msg = do
  addAssertionM sym (isInteger sym v) msg

-- | Given a partial expression, assert that it is defined
--   and return the underlying value.
readPartExpr :: IsSymInterface sym
             => sym
             -> PartExpr (Pred sym) v
             -> SimErrorReason
             -> IO v
readPartExpr sym Unassigned msg = do
  addFailedAssertion sym msg
readPartExpr sym (PE p v) msg = do
  loc <- getCurrentProgramLoc sym
  addAssertion sym (AS.LabeledPred p (SimError loc msg))
  return v
