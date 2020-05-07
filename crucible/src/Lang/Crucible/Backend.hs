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
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Backend
  ( IsBoolSolver(..)
  , IsSymInterface
  , CrucibleBackend
  , CrucibleFloatMode

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
  , addDurableAssertion
  , addAssertionM
  , addFailedAssertion
  , assertIsInteger
  , readPartExpr
  , ppProofObligation
  , backendOptions
  , assertThenAssumeConfigOption

    -- * Re-exports
  , FloatMode
  , FloatIEEE
  , FloatUninterpreted
  , FloatReal
  , FloatModeRepr(..)
  ) where

import           Control.Exception(Exception(..), throwIO)
import           Control.Lens ((^.))
import           Control.Monad
import           Data.Kind (Type)
import           Data.Foldable (toList)
import           Data.Sequence (Seq)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Concrete
import           What4.Config
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Partial
import           What4.ProgramLoc
import           What4.Expr

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import qualified Lang.Crucible.Backend.ProofGoals as PG
import           Lang.Crucible.Simulator.SimError

data CrucibleBackend (s :: Type) (fm :: FloatMode)
type family CrucibleFloatMode (t :: Type) :: FloatMode

type instance ExprLoc (CrucibleBackend s fm) = ProgramLoc
type instance ExprNonceBrand (CrucibleBackend s fm) = s

type instance CrucibleFloatMode (CrucibleBackend s fm) = fm
type instance CrucibleFloatMode (ExprBuilder t st) = CrucibleFloatMode t

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

  | VariantOptionsExhausted ProgramLoc
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
    VariantOptionsExhausted l -> ppLocated l "Variant options exhausted."

ppAssumptionReason :: AssumptionReason -> PP.Doc
ppAssumptionReason e =
  case e of
    AssumptionReason l msg -> ppLocated l (PP.text msg)
    ExploringAPath l Nothing -> "The branch in" PP.<+> ppFn l PP.<+> "at" PP.<+> ppLoc l
    ExploringAPath l (Just t) ->
        "The branch in" PP.<+> ppFn l PP.<+> "from" PP.<+> ppLoc l PP.<+> "to" PP.<+> ppLoc t
    AssumingNoError simErr -> ppSimError simErr

ppLocated :: ProgramLoc -> PP.Doc -> PP.Doc
ppLocated l x = "in" PP.<+> ppFn l PP.<+> ppLoc l PP.<> ":" PP.<+> x

ppFn :: ProgramLoc -> PP.Doc
ppFn l = PP.pretty (plFunction l)

ppLoc :: ProgramLoc -> PP.Doc
ppLoc l = PP.pretty (plSourceLoc l)

type IsSymInterface sym =
  ( IsBoolSolver sym
  , IsSymExprBuilder sym
  , PrintExpr (SymExpr sym)
  , SymLoc sym ~ ProgramLoc
  , IsInterpretedFloatExprBuilder sym (CrucibleFloatMode sym)
  )

-- | This class provides operations that interact with the symbolic simulator.
--   It allows for logical assumptions/assertions to be added to the current
--   path condition, and allows queries to be asked about branch conditions.
class IsBoolSolver sym where
  getFloatMode :: sym -> IO (FloatModeRepr (CrucibleFloatMode sym))

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Push a new assumption frame onto the stack.  Assumptions and assertions
  --   made will now be associated with this frame on the stack until a new
  --   frame is pushed onto the stack, or until this one is popped.
  pushAssumptionFrame :: sym -> IO AS.FrameIdentifier

  -- | Pop an assumption frame from the stack.  The collected assumptions
  --   in this frame are returned.  Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
  popAssumptionFrame :: sym -> AS.FrameIdentifier -> IO (Seq (Assumption sym))

  -- | Pop all assumption frames up to and including the frame with the given
  --   frame identifier.  This operation will panic if the named frame does
  --   not exist on the stack.
  popUntilAssumptionFrame :: sym -> AS.FrameIdentifier -> IO ()

  -- | Pop an assumption frame from the stack.  The collected assummptions
  --   in this frame are returned, along with any proof obligations that were
  --   incurred while the frame was active. Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
  popAssumptionFrameAndObligations ::
    sym -> AS.FrameIdentifier -> IO (Seq (Assumption sym), ProofObligations sym)

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
  -- The proof may use the current path condition and assumptions. Note
  -- that this *DOES NOT* add the goal as an assumption. See also
  -- 'addAssertion'. Also note that predicates that concretely evaluate
  -- to True will be silently discarded. See 'addDurableProofObligation'
  -- to avoid discarding goals.
  addProofObligation ::
    (IsExprBuilder sym) =>
    sym -> Assertion sym -> IO ()
  addProofObligation sym a =
    case asConstantPred (a ^. AS.labeledPred) of
      Just True -> return ()
      _ -> addDurableProofObligation sym a

  -- | Add a new proof obligation to the system which will persist
  -- throughout symbolic execution even if it is concretely valid.
  -- The proof may use the current path condition and assumptions. Note
  -- that this *DOES NOT* add the goal as an assumption. See also
  -- 'addDurableAssertion'.
  addDurableProofObligation :: sym -> Assertion sym -> IO ()

  -- | Get the collection of proof obligations.
  getProofObligations :: sym -> IO (ProofObligations sym)

  -- | Forget the current collection of proof obligations.
  -- Presumably, we've already used 'getProofObligations' to save them
  -- somewhere else.
  clearProofObligations :: sym -> IO ()

  -- | Create a snapshot of the current assumption state, that may later be restored.
  --   This is useful for supporting control-flow patterns that don't neatly fit into
  --   the stack push/pop model.
  saveAssumptionState :: sym -> IO (AssumptionState sym)

  -- | Restore the assumption state to a previous snapshot.
  restoreAssumptionState :: sym -> AssumptionState sym -> IO ()

  -- | Reset the assumption state to a fresh, blank state
  resetAssumptionState :: sym -> IO ()
  resetAssumptionState sym = restoreAssumptionState sym PG.emptyGoalCollector

assertThenAssumeConfigOption :: ConfigOption BaseBoolType
assertThenAssumeConfigOption = configOption knownRepr "assertThenAssume"

assertThenAssumeOption :: ConfigDesc
assertThenAssumeOption = mkOpt
  assertThenAssumeConfigOption
  boolOptSty
  (Just (PP.text "Assume a predicate after asserting it."))
  (Just (ConcreteBool False))

backendOptions :: [ConfigDesc]
backendOptions = [assertThenAssumeOption]

-- | Add a proof obligation for the given predicate, and then assume it
-- (when the assertThenAssume option is true).
-- Note that assuming the prediate might cause the current execution
-- path to abort, if we happened to assume something that is obviously false.
addAssertion ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym -> Assertion sym -> IO ()
addAssertion sym a =
  do addProofObligation sym a
     assumeAssertion sym a

-- | Add a durable proof obligation for the given predicate, and then
-- assume it (when the assertThenAssume option is true).
-- Note that assuming the prediate might cause the current execution
-- path to abort, if we happened to assume something that is obviously false.
addDurableAssertion ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym -> Assertion sym -> IO ()
addDurableAssertion sym a =
  do addDurableProofObligation sym a
     assumeAssertion sym a

-- | Assume assertion when the assertThenAssume option is true.
assumeAssertion ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym -> Assertion sym -> IO ()
assumeAssertion sym (AS.LabeledPred p msg) =
  do assert_then_assume_opt <- getOpt
       =<< getOptionSetting assertThenAssumeConfigOption (getConfiguration sym)
     when assert_then_assume_opt $
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
addAssertionM ::
  IsSymInterface sym =>
  sym ->
  IO (Pred sym) ->
  SimErrorReason ->
  IO ()
addAssertionM sym pf msg = do
  p <- pf
  assert sym p msg

-- | Assert that the given real-valued expression is an integer.
assertIsInteger ::
  IsSymInterface sym =>
  sym ->
  SymReal sym ->
  SimErrorReason ->
  IO ()
assertIsInteger sym v msg = do
  addAssertionM sym (isInteger sym v) msg

-- | Given a partial expression, assert that it is defined
--   and return the underlying value.
readPartExpr ::
  IsSymInterface sym =>
  sym ->
  PartExpr (Pred sym) v ->
  SimErrorReason ->
  IO v
readPartExpr sym Unassigned msg = do
  addFailedAssertion sym msg
readPartExpr sym (PE p v) msg = do
  loc <- getCurrentProgramLoc sym
  addAssertion sym (AS.LabeledPred p (SimError loc msg))
  return v

ppProofObligation :: IsSymInterface sym => sym -> ProofObligation sym -> PP.Doc
ppProofObligation _ (AS.ProofGoal (toList -> as) gl) =
  (if null as then PP.empty else
    PP.text "Assuming:" PP.<$$>
    PP.vcat (concatMap ppAsm (toList as)))
  PP.<$>
  PP.text "Prove:" PP.<$>
  ppGl
 where
 ppAsm asm
   | asConstantPred (asm^.AS.labeledPred) /= Just True =
      [PP.text "* " PP.<> PP.hang 2
        (ppAssumptionReason (asm^.AS.labeledPredMsg) PP.<$>
        printSymExpr (asm^.AS.labeledPred))]
   | otherwise = []

 ppGl = PP.indent 2
   (ppSimError (gl^.AS.labeledPredMsg) PP.<$>
    printSymExpr (gl^.AS.labeledPred))
