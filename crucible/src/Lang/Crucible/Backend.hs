{-|
Module      : Lang.Crucible.Backend
Copyright   : (c) Galois, Inc 2014-2016
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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.Crucible.Backend
  ( IsBoolSolver(..)
  , IsSymInterface

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
  , foldAssumption
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
  , addAssertion
  , addDurableAssertion
  , addAssertionM
  , addFailedAssertion
  , assertIsInteger
  , readPartExpr
  , ppProofObligation
  , backendOptions
  , assertThenAssumeConfigOption
  ) where

import           Control.Exception(Exception(..), throwIO)
import           Control.Lens ((^.), Fold, Traversal, folded)
import           Control.Monad
import           Data.Kind (Type)
import           Data.Foldable (toList)
import           Data.Functor.Identity
import           Data.Functor.Const
import qualified Data.Sequence as Seq
import           Data.Sequence (Seq)
import qualified Prettyprinter as PP

import           What4.Concrete
import           What4.Config
import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.LabeledPred
import           What4.Partial
import           What4.ProgramLoc
import           What4.Expr (GroundValue, GroundValueWrapper(..))

import qualified Lang.Crucible.Backend.AssumptionStack as AS
import qualified Lang.Crucible.Backend.ProofGoals as PG
import           Lang.Crucible.Simulator.SimError

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

data CrucibleEvent (e :: BaseType -> Type) where
  CreateVariableEvent ::
    ProgramLoc -> String -> BaseTypeRepr tp -> e tp -> CrucibleEvent e
  LocationReachedEvent ::
    ProgramLoc -> CrucibleEvent e

ppEvent :: IsExpr e => CrucibleEvent e -> PP.Doc ann
ppEvent (CreateVariableEvent loc nm _tpr v) =
  "create var" PP.<+> PP.pretty nm PP.<+> "=" PP.<+> printSymExpr v PP.<+> "at" PP.<+> PP.pretty (plSourceLoc loc)
ppEvent (LocationReachedEvent loc) =
  "reached" PP.<+> PP.pretty (plSourceLoc loc) PP.<+> "in" PP.<+> PP.pretty (plFunction loc)

eventLoc :: CrucibleEvent e -> ProgramLoc
eventLoc (CreateVariableEvent loc _ _ _) = loc
eventLoc (LocationReachedEvent loc) = loc

assumptionLoc :: CrucibleAssumption e -> ProgramLoc
assumptionLoc r =
  case r of
    GenericAssumption l _ _ -> l
    BranchCondition  l _ _   -> l
    AssumingNoError s _    -> simErrorLoc s

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

foldAssumption :: Fold (CrucibleAssumption e) (e BaseBoolType)
foldAssumption = traverseAssumption

traverseAssumption :: Traversal (CrucibleAssumption e) (CrucibleAssumption e') (e BaseBoolType) (e' BaseBoolType)
traverseAssumption f = \case
  GenericAssumption loc msg p -> GenericAssumption loc msg <$> f p
  BranchCondition l t p -> BranchCondition l t <$> f p
  AssumingNoError err p -> AssumingNoError err <$> f p

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

assumptionsTopLevelLocs :: CrucibleAssumptions e -> [ProgramLoc]
assumptionsTopLevelLocs (SingleEvent e)      = [eventLoc e]
assumptionsTopLevelLocs (SingleAssumption a) = [assumptionLoc a]
assumptionsTopLevelLocs (ManyAssumptions as) = concatMap assumptionsTopLevelLocs as
assumptionsTopLevelLocs MergeAssumptions{}   = []

assumptionsPred :: IsExprBuilder sym => sym -> Assumptions sym -> IO (Pred sym)
assumptionsPred sym (SingleEvent _) =
  return (truePred sym)
assumptionsPred sym (SingleAssumption a) =
  andAllOf sym foldAssumption a
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


{- | Merge the assumptions collected from the branches of a conditional.
The result is a bunch of qualified assumptions: if the branch condition
is @p@, then the true assumptions become @p => a@, while the false ones
beome @not p => a@.
-}
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

trivialAssumption :: IsExpr e => CrucibleAssumption e -> Bool
trivialAssumption (GenericAssumption _ _ p) = asConstantPred p == Just True
trivialAssumption (BranchCondition _ _ p) = asConstantPred p == Just True
trivialAssumption (AssumingNoError _ p) = asConstantPred p == Just True


ppLocated :: ProgramLoc -> PP.Doc ann -> PP.Doc ann
ppLocated l x = "in" PP.<+> ppFn l PP.<+> ppLoc l PP.<> ":" PP.<+> x

ppFn :: ProgramLoc -> PP.Doc ann
ppFn l = PP.pretty (plFunction l)

ppLoc :: ProgramLoc -> PP.Doc ann
ppLoc l = PP.pretty (plSourceLoc l)

type IsSymInterface sym =
  ( IsBoolSolver sym
  , IsSymExprBuilder sym
  , IsInterpretedFloatSymExprBuilder sym
  )

-- | This class provides operations that interact with the symbolic simulator.
--   It allows for logical assumptions/assertions to be added to the current
--   path condition, and allows queries to be asked about branch conditions.
class IsBoolSolver sym where

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
  popAssumptionFrame :: sym -> AS.FrameIdentifier -> IO (Assumptions sym)

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
    sym -> AS.FrameIdentifier -> IO (Assumptions sym, ProofObligations sym)

  ----------------------------------------------------------------------
  -- Assertions

  -- | Add an assumption to the current state.  Like assertions, assumptions
  --   add logical facts to the current path condition.  However, assumptions
  --   do not produce proof obligations the way assertions do.
  addAssumption :: sym -> Assumption sym -> IO ()

  -- | Add a collection of assumptions to the current state.
  addAssumptions :: sym -> Assumptions sym -> IO ()

  -- | Get the current path condition as a predicate.  This consists of the conjunction
  --   of all the assumptions currently in scope.
  getPathCondition :: sym -> IO (Pred sym)

  collectAssumptions :: sym -> IO (Assumptions sym)

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
    case asConstantPred (a ^. labeledPred) of
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
  (Just "Assume a predicate after asserting it.")
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
assumeAssertion sym (LabeledPred p msg) =
  do assert_then_assume_opt <- getOpt
       =<< getOptionSetting assertThenAssumeConfigOption (getConfiguration sym)
     when assert_then_assume_opt $
       addAssumption sym (AssumingNoError msg p)

-- | Throw an exception, thus aborting the current execution path.
abortExecBecause :: AbortExecReason -> IO a
abortExecBecause err = throwIO err

-- | Add a proof obligation using the current program location.
--   Afterwards, assume the given fact.
assert ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym ->
  Pred sym ->
  SimErrorReason ->
  IO ()
assert sym p msg =
  do loc <- getCurrentProgramLoc sym
     addAssertion sym (LabeledPred p (SimError loc msg))

-- | Add a proof obligation for False. This always aborts execution
-- of the current path, because after asserting false, we get to assume it,
-- and so there is no need to check anything after.  This is why the resulting
-- IO computation can have the fully polymorphic type.
addFailedAssertion :: (IsExprBuilder sym, IsBoolSolver sym) => sym -> SimErrorReason -> IO a
addFailedAssertion sym msg =
  do loc <- getCurrentProgramLoc sym
     let err = SimError loc msg
     addProofObligation sym (LabeledPred (falsePred sym) err)
     abortExecBecause (AssertionFailure err)

-- | Run the given action to compute a predicate, and assert it.
addAssertionM ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym ->
  IO (Pred sym) ->
  SimErrorReason ->
  IO ()
addAssertionM sym pf msg = do
  p <- pf
  assert sym p msg

-- | Assert that the given real-valued expression is an integer.
assertIsInteger ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym ->
  SymReal sym ->
  SimErrorReason ->
  IO ()
assertIsInteger sym v msg = do
  addAssertionM sym (isInteger sym v) msg

-- | Given a partial expression, assert that it is defined
--   and return the underlying value.
readPartExpr ::
  (IsExprBuilder sym, IsBoolSolver sym) =>
  sym ->
  PartExpr (Pred sym) v ->
  SimErrorReason ->
  IO v
readPartExpr sym Unassigned msg = do
  addFailedAssertion sym msg
readPartExpr sym (PE p v) msg = do
  loc <- getCurrentProgramLoc sym
  addAssertion sym (LabeledPred p (SimError loc msg))
  return v

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
