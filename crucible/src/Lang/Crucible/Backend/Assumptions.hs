{-|
Module      : Lang.Crucible.Backend.Assumptions
Copyright   : (c) Galois, Inc 2014-2024
License     : BSD3
Maintainer  : Langston Barrett <langston@galois.com>
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

module Lang.Crucible.Backend.Assumptions
  ( CrucibleAssumption(..)
  , CrucibleEvent(..)
  , CrucibleAssumptions(..)
  , Assumption
  , Assumptions

  , concretizeEvents
  , ppEvent
  , singleEvent
  , singleAssumption
  , trivialAssumption
  , ppAssumption
  , assumptionLoc
  , eventLoc
  , mergeAssumptions
  , assumptionPred
  , forgetAssumption
  , assumptionsPred
  , flattenAssumptions
  , assumptionsTopLevelLocs
  ) where


import           Control.Lens (Traversal, folded)
import           Data.Kind (Type)
import           Data.Functor.Identity
import           Data.Functor.Const
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Sequence as Seq
import           Data.Sequence (Seq)
import qualified Prettyprinter as PP

import           What4.Expr.Builder
import           What4.Interface
import           What4.ProgramLoc
import           What4.Expr (GroundValue, GroundValueWrapper(..))

import           Lang.Crucible.Simulator.SimError

type Assumption sym = CrucibleAssumption (SymExpr sym)
type Assumptions sym = CrucibleAssumptions (SymExpr sym)

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

instance TF.FunctorF CrucibleAssumption where
  fmapF = TF.fmapFDefault
instance TF.FoldableF CrucibleAssumption where
  foldMapF = TF.foldMapFDefault
instance TF.TraversableF CrucibleAssumption where
  traverseF = traverseAssumption

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

instance TF.FunctorF CrucibleEvent where
  fmapF = TF.fmapFDefault
instance TF.FoldableF CrucibleEvent where
  foldMapF = TF.foldMapFDefault
instance TF.TraversableF CrucibleEvent where
  traverseF = traverseEvent

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

forgetAssumption :: CrucibleAssumption e -> CrucibleAssumption (Const ())
forgetAssumption = runIdentity . traverseAssumption (\_ -> Identity (Const ()))

-- | Check if an assumption is trivial (always true)
trivialAssumption :: IsExpr e => CrucibleAssumption e -> Bool
trivialAssumption a = asConstantPred (assumptionPred a) == Just True

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

instance TF.FunctorF CrucibleAssumptions where
  fmapF = TF.fmapFDefault
instance TF.FoldableF CrucibleAssumptions where
  foldMapF = TF.foldMapFDefault
instance TF.TraversableF CrucibleAssumptions where
  traverseF f = \case
    SingleAssumption a ->
      SingleAssumption <$> TF.traverseF f a
    SingleEvent e ->
      SingleEvent <$> TF.traverseF f e
    ManyAssumptions xs ->
      ManyAssumptions <$> traverse (TF.traverseF f) xs
    MergeAssumptions c xs ys ->
      MergeAssumptions <$> f c <*> TF.traverseF f xs <*> TF.traverseF f ys

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
  where
    ppLocated :: ProgramLoc -> PP.Doc ann -> PP.Doc ann
    ppLocated l x = "in" PP.<+> ppFn l PP.<+> ppLoc l PP.<> ":" PP.<+> x

    ppFn :: ProgramLoc -> PP.Doc ann
    ppFn l = PP.pretty (plFunction l)

    ppLoc :: ProgramLoc -> PP.Doc ann
    ppLoc l = PP.pretty (plSourceLoc l)
