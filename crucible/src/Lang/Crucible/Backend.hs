{-|
Module      : Lang.Crucible.Backend
Copyright   : (c) Galois, Inc 2014-2022
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides the interface that the symbolic simulator uses when
interacting with symbolic backends (i.e., SMT solvers).

Compared to the solver connections provided by What4, Crucible backends provide
a facility for managing an /assumption stack/ (see 'AS.AssumptionStack').  Note
that these backends are layered on top of the 'What4.Expr.Builder.ExprBuilder';
the solver choice is still up to the user.  The
'Lang.Crucible.Backend.Simple.SimpleBackend' is designed to be used with an
offline solver connection, while the
'Lang.Crucible.Backend.Online.OnlineBackend' is designed to be used with an
online solver.

The backend tracks the assumptions that are in scope for each assertion,
accounting for the branching and merging structure of programs. After
symbolic simulation completes, the caller should traverse the collected
'ProofObligations'  (via 'getProofObligations') to discharge the resulting proof
obligations with a solver backend. See also "Lang.Crucible.Backend.Prove".
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Backend
  ( IsSymBackend(..)
  , IsSymInterface
  , HasSymInterface(..)
  , Assertion
  , SomeBackend(..)
  , ProofObligation
  , ProofObligations
  , AssumptionState
  , assert
  , impossibleAssumption

    -- ** Reexports
  , module Lang.Crucible.Backend.Assumptions
  , LabeledPred(..)
  , labeledPred
  , labeledPredMsg
  , AS.AssumptionStack
  , AS.FrameIdentifier
  , PG.ProofGoal(..)
  , PG.Goals(..)
  , PG.goalsToList

    -- ** Aborting execution
  , AbortExecReason(..)
  , abortExecBecause
  , ppAbortExecReason

    -- * Utilities
  , throwUnsupported

  , addAssertion
  , addDurableAssertion
  , addAssertionM
  , addFailedAssertion
  , assertIsInteger
  , readPartExpr
  , runCHC
  , proofObligationsAsImplications
  , convertProofObligationsAsImplications
  , proofObligationsUninterpConstants
  , pathConditionUninterpConstants
  , ppProofObligation
  , backendOptions
  , assertThenAssumeConfigOption
  , ppAssumptionState
  ) where

import           Control.Exception(Exception(..), throwIO)
import           Control.Lens ((^.))
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import           Data.Set (Set)
import qualified Prettyprinter as PP
import           GHC.Stack

import           Data.Parameterized.Map (MapF)

import           What4.Concrete
import           What4.Config
import           What4.Expr.Builder
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.LabeledPred
import           What4.Partial
import           What4.ProgramLoc

import           What4.Solver
import qualified What4.Solver.Z3 as Z3

import           Lang.Crucible.Backend.Assumptions
import qualified Lang.Crucible.Backend.AssumptionStack as AS
import qualified Lang.Crucible.Backend.ProofGoals as PG
import           Lang.Crucible.Simulator.SimError
import Lang.Crucible.Backend.ProofGoals (ppGoalCollector)

type Assertion sym = LabeledPred (Pred sym) SimError
type ProofObligation sym = AS.ProofGoal (Assumptions sym) (Assertion sym)
type ProofObligations sym = Maybe (AS.Goals (Assumptions sym) (Assertion sym))
type AssumptionState sym = PG.GoalCollector (Assumptions sym) (Assertion sym)

-- | This is used to signal that current execution path is infeasible.
data AbortExecReason =
    InfeasibleBranch ProgramLoc
    -- ^ We have discovered that the currently-executing
    --   branch is infeasible. The given program location
    --   describes the point at which infeasibility was discovered.

  | AssertionFailure SimError
    -- ^ An assertion concretely failed.

  | VariantOptionsExhausted ProgramLoc
    -- ^ We tried all possible cases for a variant, and now we should
    -- do something else.

  | EarlyExit ProgramLoc
    -- ^ We invoked a function which ends the current thread of execution
    --   (e.g., @abort()@ or @exit(1)@).

    deriving Show

instance Exception AbortExecReason


-- | If an assumption is clearly impossible, return an abort reason
--   that can be used to unwind the execution of this branch.
impossibleAssumption :: IsExpr e => CrucibleAssumption e -> Maybe AbortExecReason
impossibleAssumption (AssumingNoError err p)
  | Just False <- asConstantPred p = Just (AssertionFailure err)
impossibleAssumption (BranchCondition loc _ p)
  | Just False <- asConstantPred p = Just (InfeasibleBranch loc)
impossibleAssumption (GenericAssumption loc _ p)
  | Just False <- asConstantPred p = Just (InfeasibleBranch loc)
impossibleAssumption _ = Nothing

ppAbortExecReason :: AbortExecReason -> PP.Doc ann
ppAbortExecReason e =
  case e of
    InfeasibleBranch l -> ppLocated l "Executing branch was discovered to be infeasible."
    AssertionFailure err ->
      PP.vcat
      [ "Abort due to assertion failure:"
      , PP.indent 2 (ppSimError err)
      ]
    VariantOptionsExhausted l -> ppLocated l "Variant options exhausted."
    EarlyExit l -> ppLocated l "Program exited early."
  where
    ppLocated :: ProgramLoc -> PP.Doc ann -> PP.Doc ann
    ppLocated l x = "in" PP.<+> ppFn l PP.<+> ppLoc l PP.<> ":" PP.<+> x

    ppFn :: ProgramLoc -> PP.Doc ann
    ppFn l = PP.pretty (plFunction l)

    ppLoc :: ProgramLoc -> PP.Doc ann
    ppLoc l = PP.pretty (plSourceLoc l)

throwUnsupported :: (IsExprBuilder sym, MonadIO m, HasCallStack) => sym -> String -> m a
throwUnsupported sym msg = liftIO $
  do loc <- getCurrentProgramLoc sym
     throwIO $ SimError loc $ Unsupported callStack msg

type IsSymInterface sym =
  ( IsSymExprBuilder sym
  , IsInterpretedFloatSymExprBuilder sym
  )

data SomeBackend sym =
  forall bak. IsSymBackend sym bak => SomeBackend bak


-- | Class for backend type that can retrieve sym values.
--
--   This is separate from `IsSymBackend` specifically to avoid
--   the need for additional class constraints on the `backendGetSym`
--   operation, which is occasionally useful.
class HasSymInterface sym bak | bak -> sym where
  -- | Retrive the symbolic expression builder corresponding to this
  --   simulator backend.
  backendGetSym :: bak -> sym


-- | This class provides operations that interact with the symbolic simulator.
--   It allows for logical assumptions/assertions to be added to the current
--   path condition, and allows queries to be asked about branch conditions.
--
--   The @bak@ type contains all the datastructures necessary to
--   maintain the current program path conditions, and keep track of
--   assumptions and assertions made during program execution.  The @sym@
--   type is expected to satisfy the `IsSymInterface` constraints, which
--   provide access to the What4 expression language. A @sym@ is uniquely
--   determined by a @bak@.
--
--
--   == Note [Pushes and pops]
--
--   This class provides methods for pushing ('pushAssumptionFrame')
--   and popping ('popAssumptionFrame', 'popUntilAssumptionFrame',
--   'popAssumptionFrameAndObligations') frames. Pushes and pops must be
--   well-bracketed. In particular, @popAssumptionFrame*@ are required to throw
--   an exception if the provided frame identifier does not match the top of
--   the stack.
--
--   It is relatively easy to end up with ill-bracketed pushes and pops in the
--   presence of exceptions. When diagnosing such issues, consider popping
--   frames using methods such as 'Control.Exception.try'.
class (IsSymInterface sym, HasSymInterface sym bak) => IsSymBackend sym bak | bak -> sym where

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Push a new assumption frame onto the stack.  Assumptions and assertions
  --   made will now be associated with this frame on the stack until a new
  --   frame is pushed onto the stack, or until this one is popped.
  pushAssumptionFrame :: bak -> IO AS.FrameIdentifier

  -- | Pop an assumption frame from the stack.  The collected assumptions
  --   in this frame are returned.
  --
  --   This may throw an exception, see Note [Pushes and pops].
  popAssumptionFrame :: bak -> AS.FrameIdentifier -> IO (Assumptions sym)

  -- | Pop all assumption frames up to and including the frame with the given
  --   frame identifier.  This operation will panic if the named frame does
  --   not exist on the stack.
  popUntilAssumptionFrame :: bak -> AS.FrameIdentifier -> IO ()

  -- | Pop an assumption frame from the stack.  The collected assummptions
  --   in this frame are returned, along with any proof obligations that were
  --   incurred while the frame was active.
  --
  --   Note that the returned 'ProofObligation's only include assumptions from
  --   the popped frame, not all frames above it.
  --
  --   This may throw an exception, see Note [Pushes and pops].
  popAssumptionFrameAndObligations ::
    bak -> AS.FrameIdentifier -> IO (Assumptions sym, ProofObligations sym)

  ----------------------------------------------------------------------
  -- Assertions

  -- | Add an assumption to the current state.
  addAssumption :: bak -> Assumption sym -> IO ()

  -- | Add a collection of assumptions to the current state.
  addAssumptions :: bak -> Assumptions sym -> IO ()

  -- | Get the current path condition as a predicate.  This consists of the conjunction
  --   of all the assumptions currently in scope.
  getPathCondition :: bak -> IO (Pred sym)
  getPathCondition bak = do
    let sym = backendGetSym bak
    ps <- collectAssumptions bak
    assumptionsPred sym ps

  -- | Collect all the assumptions currently in scope
  collectAssumptions :: bak -> IO (Assumptions sym)

  -- | Add a new proof obligation to the system.
  -- The proof may use the current path condition and assumptions. Note
  -- that this *DOES NOT* add the goal as an assumption. See also
  -- 'addAssertion'. Also note that predicates that concretely evaluate
  -- to True will be silently discarded. See 'addDurableProofObligation'
  -- to avoid discarding goals.
  addProofObligation :: bak -> Assertion sym -> IO ()
  addProofObligation bak a =
    case asConstantPred (a ^. labeledPred) of
      Just True -> return ()
      _ -> addDurableProofObligation bak a

  -- | Add a new proof obligation to the system which will persist
  -- throughout symbolic execution even if it is concretely valid.
  -- The proof may use the current path condition and assumptions. Note
  -- that this *DOES NOT* add the goal as an assumption. See also
  -- 'addDurableAssertion'.
  addDurableProofObligation :: bak -> Assertion sym -> IO ()

  -- | Get the collection of proof obligations.
  getProofObligations :: bak -> IO (ProofObligations sym)

  -- | Forget the current collection of proof obligations.
  -- Presumably, we've already used 'getProofObligations' to save them
  -- somewhere else.
  clearProofObligations :: bak -> IO ()

  -- | Create a snapshot of the current assumption state, that may later be restored.
  --   This is useful for supporting control-flow patterns that don't neatly fit into
  --   the stack push/pop model.
  saveAssumptionState :: bak -> IO (AssumptionState sym)

  -- | Restore the assumption state to a previous snapshot.
  restoreAssumptionState :: bak -> AssumptionState sym -> IO ()

  -- | Reset the assumption state to a fresh, blank state
  resetAssumptionState :: bak -> IO ()
  resetAssumptionState bak = restoreAssumptionState bak PG.emptyGoalCollector

  -- | Get the state of the backend
  getBackendState :: bak -> IO (AssumptionState sym)

assertThenAssumeConfigOption :: ConfigOption BaseBoolType
assertThenAssumeConfigOption = configOption knownRepr "assertThenAssume"

assertThenAssumeOption :: ConfigDesc
assertThenAssumeOption = mkOpt
  assertThenAssumeConfigOption
  boolOptSty
  (Just "Assume a predicate after asserting it.")
  (Just (ConcreteBool False))

backendOptions :: [ConfigDesc]
backendOptions = [assertThenAssumeOption]

-- | Add a proof obligation for the given predicate, and then assume it
-- (when the assertThenAssume option is true).
-- Note that assuming the prediate might cause the current execution
-- path to abort, if we happened to assume something that is obviously false.
addAssertion ::
  IsSymBackend sym bak =>
  bak -> Assertion sym -> IO ()
addAssertion bak a =
  do addProofObligation bak a
     assumeAssertion bak a

-- | Add a durable proof obligation for the given predicate, and then
-- assume it (when the assertThenAssume option is true).
-- Note that assuming the prediate might cause the current execution
-- path to abort, if we happened to assume something that is obviously false.
addDurableAssertion :: IsSymBackend sym bak => bak -> Assertion sym -> IO ()
addDurableAssertion bak a =
  do addDurableProofObligation bak a
     assumeAssertion bak a

-- | Assume assertion when the assertThenAssume option is true.
assumeAssertion :: IsSymBackend sym bak => bak -> Assertion sym -> IO ()
assumeAssertion bak (LabeledPred p msg) =
  do let sym = backendGetSym bak
     assert_then_assume_opt <- getOpt
       =<< getOptionSetting assertThenAssumeConfigOption (getConfiguration sym)
     when assert_then_assume_opt $
       addAssumption bak (AssumingNoError msg p)

-- | Throw an exception, thus aborting the current execution path.
abortExecBecause :: AbortExecReason -> IO a
abortExecBecause err = throwIO err

-- | Add a proof obligation using the current program location.
--   Afterwards, assume the given fact.
assert ::
  IsSymBackend sym bak =>
  bak ->
  Pred sym ->
  SimErrorReason ->
  IO ()
assert bak p msg =
  do let sym = backendGetSym bak
     loc <- getCurrentProgramLoc sym
     addAssertion bak (LabeledPred p (SimError loc msg))

-- | Add a proof obligation for False. This always aborts execution
-- of the current path, because after asserting false, we get to assume it,
-- and so there is no need to check anything after.  This is why the resulting
-- IO computation can have the fully polymorphic type.
addFailedAssertion :: IsSymBackend sym bak => bak -> SimErrorReason -> IO a
addFailedAssertion bak msg =
  do let sym = backendGetSym bak
     loc <- getCurrentProgramLoc sym
     let err = SimError loc msg
     addProofObligation bak (LabeledPred (falsePred sym) err)
     abortExecBecause (AssertionFailure err)

-- | Run the given action to compute a predicate, and assert it.
addAssertionM ::
  IsSymBackend sym bak =>
  bak ->
  IO (Pred sym) ->
  SimErrorReason ->
  IO ()
addAssertionM bak pf msg = do
  p <- pf
  assert bak p msg

-- | Assert that the given real-valued expression is an integer.
assertIsInteger ::
  IsSymBackend sym bak =>
  bak ->
  SymReal sym ->
  SimErrorReason ->
  IO ()
assertIsInteger bak v msg = do
  let sym = backendGetSym bak
  addAssertionM bak (isInteger sym v) msg

-- | Given a partial expression, assert that it is defined
--   and return the underlying value.
readPartExpr ::
  IsSymBackend sym bak =>
  bak ->
  PartExpr (Pred sym) v ->
  SimErrorReason ->
  IO v
readPartExpr bak Unassigned msg = do
  addFailedAssertion bak msg
readPartExpr bak (PE p v) msg = do
  let sym = backendGetSym bak
  loc <- getCurrentProgramLoc sym
  addAssertion bak (LabeledPred p (SimError loc msg))
  return v


-- | Run the CHC solver on the current proof obligations, and return the
-- solution as a substitution from the uninterpreted functions to their
-- definitions.
runCHC ::
  (IsSymBackend sym bak, sym ~ ExprBuilder t st fs, MonadIO m) =>
  bak ->
  [SomeSymFn sym] ->
  m (MapF (SymFnWrapper sym) (SymFnWrapper sym))
runCHC bak uninterp_inv_fns  = liftIO $ do
  let sym = backendGetSym bak

  implications <- proofObligationsAsImplications bak
  clearProofObligations bak

  -- log to stdout
  let logData = defaultLogData
        { logCallbackVerbose = \_ -> putStrLn
        , logReason = "Crucible inv"
        }
  Z3.runZ3Horn sym True logData uninterp_inv_fns implications >>= \case
    Sat sub -> return sub
    Unsat{} -> fail "Prover returned Unsat"
    Unknown -> fail "Prover returned Unknown"


-- | Get proof obligations as What4 implications.
proofObligationsAsImplications :: IsSymBackend sym bak => bak -> IO [Pred sym]
proofObligationsAsImplications bak = do
  let sym = backendGetSym bak
  convertProofObligationsAsImplications sym =<< getProofObligations bak

-- | Convert proof obligations to What4 implications.
convertProofObligationsAsImplications :: IsSymInterface sym => sym -> ProofObligations sym -> IO [Pred sym]
convertProofObligationsAsImplications sym goals = do
  let obligations = maybe [] PG.goalsToList goals
  forM obligations $ \(AS.ProofGoal hyps (LabeledPred concl _err)) -> do
    hyp <- assumptionsPred sym hyps
    impliesPred sym hyp concl

-- | Get the set of uninterpreted constants that appear in the path condition.
pathConditionUninterpConstants :: IsSymBackend sym bak => bak -> IO (Set (Some (BoundVar sym)))
pathConditionUninterpConstants bak = do
  let sym = backendGetSym bak
  exprUninterpConstants sym <$> getPathCondition bak

-- | Get the set of uninterpreted constants that appear in the proof obligations.
proofObligationsUninterpConstants :: IsSymBackend sym bak => bak -> IO (Set (Some (BoundVar sym)))
proofObligationsUninterpConstants bak = do
  let sym = backendGetSym bak
  foldMap (exprUninterpConstants sym) <$> proofObligationsAsImplications bak


ppProofObligation :: IsExprBuilder sym => sym -> ProofObligation sym -> IO (PP.Doc ann)
ppProofObligation sym (AS.ProofGoal asmps gl) =
  do as <- flattenAssumptions sym asmps
     return $ PP.vsep
       [ if null as then mempty else
           PP.vcat ("Assuming:" : concatMap ppAsm (toList as))
       , "Prove:"
       , ppGl
       ]
 where
 ppAsm asm
   | not (trivialAssumption asm) = ["* " PP.<> PP.hang 2 (ppAssumption printSymExpr asm)]
   | otherwise = []

 ppGl =
   PP.indent 2 $
   PP.vsep [ppSimError (gl^.labeledPredMsg), printSymExpr (gl^.labeledPred)]

-- | Pretty-printer for 'AssumptionState'.
ppAssumptionState ::
  IsExpr (SymExpr sym) =>
  proxy sym ->
  AssumptionState sym ->
  PP.Doc ann
ppAssumptionState _proxy = ppGoalCollector ppAssumptions ppPred
  where
  ppPred (LabeledPred p simErr) =
    PP.vcat
    [ "Labeled predicate:"
    , PP.indent 2 $
        PP.vcat
        [ printSymExpr p
        , ppSimError simErr
        ]
    ]
