{-|
Module      : Lang.Crucible.Backend
Copyright   : (c) Galois, Inc 2014-2022
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This module provides an interface that symbolic backends must provide
for interacting with the symbolic simulator.

Compared to the solver connections provided by What4, Crucible backends provide
a facility for managing an /assumption stack/ (see 'AS.AssumptionStack').  Note
that these backends are layered on top of the 'What4.Expr.Builder.ExprBuilder';
the solver choice is still up to the user.  The
'Lang.Crucible.Backend.Simple.SimpleBackend' is designed to be used with an
offline solver connection, while the
'Lang.Crucible.Backend.Online.OnlineBackend' is designed to be used with an
online solver.

The 'AS.AssumptionStack' tracks the assumptions that are in scope for each
assertion, accounting for the branching and merging structure of programs.  The
symbolic simulator manages the 'AS.AssumptionStack'. After symbolic simulation
completes, the caller should traverse the 'AS.AssumptionStack' (or use
combinators like 'AS.proofGoalsToList') to discharge the resulting proof
obligations with a solver backend.

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
  , SomeBackend(..)

    -- * Assumption management
  , CrucibleAssumption(..)
  , CrucibleEvent(..)
  , CrucibleAssumptions(..)
  , Assumption
  , Assertion
  , Assumptions

  , concretizeEvents
  , ppEvent
  , singleEvent
  , singleAssumption
  , trivialAssumption
  , impossibleAssumption
  , ppAssumption
  , assumptionLoc
  , eventLoc
  , mergeAssumptions
  , assumptionPred
  , forgetAssumption
  , assumptionsPred
  , flattenAssumptions
  , assumptionsTopLevelLocs
  , ProofObligation
  , ProofObligations
  , AssumptionState
  , assert

    -- ** Reexports
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
  ) where

import           Control.Exception(Exception(..), throwIO)
import           Control.Lens ((^.), Traversal, folded)
import           Control.Monad
import           Control.Monad.IO.Class
import           Data.Kind (Type)
import           Data.Foldable (toList)
import           Data.Functor.Identity
import           Data.Functor.Const
import qualified Data.Sequence as Seq
import           Data.Sequence (Seq)
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
import           What4.Expr (GroundValue, GroundValueWrapper(..))
import           What4.Solver
import qualified What4.Solver.Z3 as Z3

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import qualified Lang.Crucible.Backend.ProofGoals as PG
import           Lang.Crucible.Simulator.SimError

-- | This type describes assumptions made at some point during program execution.
data CrucibleAssumption (e :: BaseType -> Type)
  = GenericAssumption ProgramLoc String (e BaseBoolType)
    -- ^ An unstructured description of the source of an assumption.

  | BranchCondition ProgramLoc (Maybe ProgramLoc) (e BaseBoolType)
    -- ^ This arose because we want to explore a specific path.
    -- The first location is the location of the branch predicate.
    -- The second one is the location of the branch target.

  | AssumingNoError SimError (e BaseBoolType)
    -- ^ An assumption justified by a proof of the impossibility of
    -- a certain simulator error.

-- | This type describes events we can track during program execution.
data CrucibleEvent (e :: BaseType -> Type) where
  -- | This event describes the creation of a symbolic variable.
  CreateVariableEvent ::
    ProgramLoc {- ^ location where the variable was created -} ->
    String {- ^ user-provided name for the variable -} ->
    BaseTypeRepr tp {- ^ type of the variable -} ->
    e tp {- ^ the variable expression -} ->
    CrucibleEvent e

  -- | This event describes reaching a particular program location.
  LocationReachedEvent ::
    ProgramLoc ->
    CrucibleEvent e

-- | Pretty print an event
ppEvent :: IsExpr e => CrucibleEvent e -> PP.Doc ann
ppEvent (CreateVariableEvent loc nm _tpr v) =
  "create var" PP.<+> PP.pretty nm PP.<+> "=" PP.<+> printSymExpr v PP.<+> "at" PP.<+> PP.pretty (plSourceLoc loc)
ppEvent (LocationReachedEvent loc) =
  "reached" PP.<+> PP.pretty (plSourceLoc loc) PP.<+> "in" PP.<+> PP.pretty (plFunction loc)

-- | Return the program location associated with an event
eventLoc :: CrucibleEvent e -> ProgramLoc
eventLoc (CreateVariableEvent loc _ _ _) = loc
eventLoc (LocationReachedEvent loc) = loc

-- | Return the program location associated with an assumption
assumptionLoc :: CrucibleAssumption e -> ProgramLoc
assumptionLoc r =
  case r of
    GenericAssumption l _ _ -> l
    BranchCondition  l _ _   -> l
    AssumingNoError s _    -> simErrorLoc s

-- | Get the predicate associated with this assumption
assumptionPred :: CrucibleAssumption e -> e BaseBoolType
assumptionPred (AssumingNoError _ p) = p
assumptionPred (BranchCondition _ _ p) = p
assumptionPred (GenericAssumption _ _ p) = p

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

forgetAssumption :: CrucibleAssumption e -> CrucibleAssumption (Const ())
forgetAssumption = runIdentity . traverseAssumption (\_ -> Identity (Const ()))

traverseAssumption :: Traversal (CrucibleAssumption e) (CrucibleAssumption e') (e BaseBoolType) (e' BaseBoolType)
traverseAssumption f = \case
  GenericAssumption loc msg p -> GenericAssumption loc msg <$> f p
  BranchCondition l t p -> BranchCondition l t <$> f p
  AssumingNoError err p -> AssumingNoError err <$> f p

-- | This type tracks both logical assumptions and program events
--   that are relevant when evaluating proof obligations arising
--   from simulation.
data CrucibleAssumptions (e :: BaseType -> Type) where
  SingleAssumption :: CrucibleAssumption e -> CrucibleAssumptions e
  SingleEvent      :: CrucibleEvent e -> CrucibleAssumptions e
  ManyAssumptions  :: Seq (CrucibleAssumptions e) -> CrucibleAssumptions e
  MergeAssumptions ::
    e BaseBoolType {- ^ branch condition -} ->
    CrucibleAssumptions e {- ^ "then" assumptions -} ->
    CrucibleAssumptions e {- ^ "else" assumptions -} ->
    CrucibleAssumptions e

instance Semigroup (CrucibleAssumptions e) where
  ManyAssumptions xs <> ManyAssumptions ys = ManyAssumptions (xs <> ys)
  ManyAssumptions xs <> y = ManyAssumptions (xs Seq.|> y)
  x <> ManyAssumptions ys = ManyAssumptions (x Seq.<| ys)
  x <> y = ManyAssumptions (Seq.fromList [x,y])

instance Monoid (CrucibleAssumptions e) where
  mempty = ManyAssumptions mempty

singleAssumption :: CrucibleAssumption e -> CrucibleAssumptions e
singleAssumption x = SingleAssumption x

singleEvent :: CrucibleEvent e -> CrucibleAssumptions e
singleEvent x = SingleEvent x

-- | Collect the program locations of all assumptions and
--   events that did not occur in the context of a symbolic branch.
--   These are locations that every program path represented by
--   this @CrucibleAssumptions@ structure must have passed through.
assumptionsTopLevelLocs :: CrucibleAssumptions e -> [ProgramLoc]
assumptionsTopLevelLocs (SingleEvent e)      = [eventLoc e]
assumptionsTopLevelLocs (SingleAssumption a) = [assumptionLoc a]
assumptionsTopLevelLocs (ManyAssumptions as) = concatMap assumptionsTopLevelLocs as
assumptionsTopLevelLocs MergeAssumptions{}   = []

-- | Compute the logical predicate corresponding to this collection of assumptions.
assumptionsPred :: IsExprBuilder sym => sym -> Assumptions sym -> IO (Pred sym)
assumptionsPred sym (SingleEvent _) =
  return (truePred sym)
assumptionsPred _sym (SingleAssumption a) =
  return (assumptionPred a)
assumptionsPred sym (ManyAssumptions xs) =
  andAllOf sym folded =<< traverse (assumptionsPred sym) xs
assumptionsPred sym (MergeAssumptions c xs ys) =
  do xs' <- assumptionsPred sym xs
     ys' <- assumptionsPred sym ys
     itePred sym c xs' ys'

traverseEvent :: Applicative m =>
  (forall tp. e tp -> m (e' tp)) ->
  CrucibleEvent e -> m (CrucibleEvent e')
traverseEvent f (CreateVariableEvent loc nm tpr v) = CreateVariableEvent loc nm tpr <$> f v
traverseEvent _ (LocationReachedEvent loc) = pure (LocationReachedEvent loc)

-- | Given a ground evaluation function, compute a linear, ground-valued
--   sequence of events corresponding to this program run.
concretizeEvents ::
  IsExpr e =>
  (forall tp. e tp -> IO (GroundValue tp)) ->
  CrucibleAssumptions e ->
  IO [CrucibleEvent GroundValueWrapper]
concretizeEvents f = loop
  where
    loop (SingleEvent e) =
      do e' <- traverseEvent (\v -> GVW <$> f v) e
         return [e']
    loop (SingleAssumption _) = return []
    loop (ManyAssumptions as) = concat <$> traverse loop as
    loop (MergeAssumptions p xs ys) =
      do b <- f p
         if b then loop xs else loop ys

-- | Given a @CrucibleAssumptions@ structure, flatten all the muxed assumptions into
--   a flat sequence of assumptions that have been appropriately weakened.
--   Note, once these assumptions have been flattened, their order might no longer
--   strictly correspond to any concrete program run.
flattenAssumptions :: IsExprBuilder sym => sym -> Assumptions sym -> IO [Assumption sym]
flattenAssumptions sym = loop Nothing
  where
    loop _mz (SingleEvent _) = return []
    loop mz (SingleAssumption a) =
      do a' <- maybe (pure a) (\z -> traverseAssumption (impliesPred sym z) a) mz
         if trivialAssumption a' then return [] else return [a']
    loop mz (ManyAssumptions as) =
      concat <$> traverse (loop mz) as
    loop mz (MergeAssumptions p xs ys) =
      do pnot <- notPred sym p
         px <- maybe (pure p) (andPred sym p) mz
         py <- maybe (pure pnot) (andPred sym pnot) mz
         xs' <- loop (Just px) xs
         ys' <- loop (Just py) ys
         return (xs' <> ys')

-- | Merge the assumptions collected from the branches of a conditional.
mergeAssumptions ::
  IsExprBuilder sym =>
  sym ->
  Pred sym ->
  Assumptions sym ->
  Assumptions sym ->
  IO (Assumptions sym)
mergeAssumptions _sym p thens elses =
  return (MergeAssumptions p thens elses)

type Assertion sym  = LabeledPred (Pred sym) SimError
type Assumption sym = CrucibleAssumption (SymExpr sym)
type Assumptions sym = CrucibleAssumptions (SymExpr sym)
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

ppAssumption :: (forall tp. e tp -> PP.Doc ann) -> CrucibleAssumption e -> PP.Doc ann
ppAssumption ppDoc e =
  case e of
    GenericAssumption l msg p ->
      PP.vsep [ ppLocated l (PP.pretty msg)
              , ppDoc p
              ]
    BranchCondition l Nothing p ->
      PP.vsep [ "The branch in" PP.<+> ppFn l PP.<+> "at" PP.<+> ppLoc l
              , ppDoc p
              ]
    BranchCondition l (Just t) p ->
      PP.vsep [ "The branch in" PP.<+> ppFn l PP.<+> "from" PP.<+> ppLoc l PP.<+> "to" PP.<+> ppLoc t
              , ppDoc p
              ]
    AssumingNoError simErr p ->
      PP.vsep [ "Assuming the following error does not occur:"
              , PP.indent 2 (ppSimError simErr)
              , ppDoc p
              ]

throwUnsupported :: (IsExprBuilder sym, MonadIO m, HasCallStack) => sym -> String -> m a
throwUnsupported sym msg = liftIO $
  do loc <- getCurrentProgramLoc sym
     throwIO $ SimError loc $ Unsupported callStack msg


-- | Check if an assumption is trivial (always true)
trivialAssumption :: IsExpr e => CrucibleAssumption e -> Bool
trivialAssumption a = asConstantPred (assumptionPred a) == Just True

ppLocated :: ProgramLoc -> PP.Doc ann -> PP.Doc ann
ppLocated l x = "in" PP.<+> ppFn l PP.<+> ppLoc l PP.<> ":" PP.<+> x

ppFn :: ProgramLoc -> PP.Doc ann
ppFn l = PP.pretty (plFunction l)

ppLoc :: ProgramLoc -> PP.Doc ann
ppLoc l = PP.pretty (plSourceLoc l)

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
class (IsSymInterface sym, HasSymInterface sym bak) => IsSymBackend sym bak | bak -> sym where

  ----------------------------------------------------------------------
  -- Branch manipulations

  -- | Push a new assumption frame onto the stack.  Assumptions and assertions
  --   made will now be associated with this frame on the stack until a new
  --   frame is pushed onto the stack, or until this one is popped.
  pushAssumptionFrame :: bak -> IO AS.FrameIdentifier

  -- | Pop an assumption frame from the stack.  The collected assumptions
  --   in this frame are returned.  Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
  popAssumptionFrame :: bak -> AS.FrameIdentifier -> IO (Assumptions sym)

  -- | Pop all assumption frames up to and including the frame with the given
  --   frame identifier.  This operation will panic if the named frame does
  --   not exist on the stack.
  popUntilAssumptionFrame :: bak -> AS.FrameIdentifier -> IO ()

  -- | Pop an assumption frame from the stack.  The collected assummptions
  --   in this frame are returned, along with any proof obligations that were
  --   incurred while the frame was active. Pops are required to be well-bracketed
  --   with pushes.  In particular, if the given frame identifier is not
  --   the identifier of the top frame on the stack, an error will be raised.
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

  withFile "foo.smt2" WriteMode $ \handle ->
    Z3.writeZ3HornSMT2File sym True handle uninterp_inv_fns implications
  withFile "foo.sy" WriteMode $ \handle ->
    CVC5.writeCVC5SyFile sym handle uninterp_inv_fns implications

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
