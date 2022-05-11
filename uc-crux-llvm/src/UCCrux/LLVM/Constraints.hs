{-
Module       : UCCrux.LLVM.Constraints
Description  : Constraints
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Constraints
  ( -- * Types of constraints
    ShapeConstraint (..),
    ppShapeConstraint,
    Constraint (..),
    ppConstraint,
    RelationalConstraint (..),
    ConstrainedTypedValue (..),

    -- * 'ConstrainedShape'
    ConstrainedShape (..),
    minimalConstrainedShape,
  )
where

{- ORMOLU_DISABLE -}
import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Functor.Compose (Compose(..))
import           Data.Kind (Type)
import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Context (Ctx)
import           Data.Parameterized.NatRepr (NatRepr, type (<=))
import           Data.Parameterized.TraversableFC (fmapFC)

import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment)

import           UCCrux.LLVM.Cursor (Selector(..))
import           UCCrux.LLVM.Shape (Shape)
import qualified UCCrux.LLVM.Shape as Shape
import           UCCrux.LLVM.FullType.Type (FullType(..), FullTypeRepr)
{- ORMOLU_ENABLE -}

--------------------------------------------------------------------------------

-- * Types of constraints

-- | A 'ShapeConstraint' describes a constraint on a part of a value\'s memory
-- layout. They're generated in "UCCrux.LLVM.Classify", and applied to a 'Shape'
-- in 'expand'. Basically, if 'UCCrux.LLVM.Classify.classifyBadBehavior' runs
-- into an error that would be fixed by allocating more memory or initializing
-- more memory, it will return one of these to indicate that the appropriate
-- memory model operation should happen next time in
-- "UCCrux.LLVM.Classify.generate".
data ShapeConstraint (m :: Type) (atTy :: FullType m) where
  -- | This pointer is not null, and has space for at least this many elements
  --
  -- Invariant: argument should be positive.
  Allocated :: !Int -> ShapeConstraint m ('FTPtr ft)
  -- | This pointer points to initialized memory with at least this many elements
  --
  -- Invariant: argument should be positive.
  Initialized :: !Int -> ShapeConstraint m ('FTPtr ft)

deriving instance Eq (ShapeConstraint m atTy)

ppShapeConstraint :: ShapeConstraint m atTy -> Doc ann
ppShapeConstraint =
  \case
    Allocated sz ->
      PP.pretty "points to allocated space for"
      PP.<+> PP.viaShow sz
      PP.<+> PP.pretty "elements"
    Initialized sz ->
      PP.pretty "points to"
      PP.<+> PP.viaShow sz
      PP.<+> PP.pretty "initialized elements"

-- | A 'Constraint' is in general, something that can be \"applied\" to a
-- symbolic value to produce a predicate. In practice, these represent
-- \"missing\" function preconditions that are deduced by
-- 'UCCrux.LLVM.Classify.classifyBadBehavior', and are then turned into
-- predicates when generating those arguments in
-- "UCCrux.LLVM.Classify.generate", and assumed in "UCCrux.LLVM.Run.Simulate".
data Constraint (m :: Type) (atTy :: FullType m) where
  -- | This pointer has at least this alignment
  Aligned :: !Alignment -> Constraint m ('FTPtr ft)
  -- | This comparison holds.
  BVCmp :: (1 <= w) => !L.ICmpOp -> !(NatRepr w) -> !(BV w) -> Constraint m ('FTInt w)

instance Eq (Constraint m atTy) where
  c1 == c2 =
    case (c1, c2) of
      (Aligned n1, Aligned n2) -> n1 == n2
      (BVCmp op1 _ bv1, BVCmp op2 _ bv2) -> op1 == op2 && bv1 == bv2

ppConstraint :: Constraint m ft -> Doc ann
ppConstraint =
  \case
    Aligned alignment ->
      PP.pretty "is aligned to " <> PP.viaShow (fromAlignment alignment)
    BVCmp L.Ieq w bv -> PP.pretty "is equal to " <> unsigned w bv
    BVCmp L.Ine w bv -> PP.pretty "is not equal to " <> unsigned w bv
    BVCmp L.Iult w bv -> PP.pretty "is (unsigned) less than " <> unsigned w bv
    BVCmp L.Iule w bv -> PP.pretty "is (unsigned) less than or equal to " <> unsigned w bv
    BVCmp L.Iugt w bv -> PP.pretty "is (unsigned) greater than " <> unsigned w bv
    BVCmp L.Iuge w bv -> PP.pretty "is (unsigned) greater than or equal to " <> unsigned w bv
    BVCmp L.Islt w bv -> PP.pretty "is (signed) less than " <> signed w bv
    BVCmp L.Isle w bv -> PP.pretty "is (signed) less than or equal to " <> signed w bv
    BVCmp L.Isgt w bv -> PP.pretty "is (signed) greater than " <> signed w bv
    BVCmp L.Isge w bv -> PP.pretty "is (signed) greater than or equal to " <> signed w bv
  where
    signed :: forall ann w. (1 <= w) => NatRepr w -> BV w -> PP.Doc ann
    signed w bv =
      PP.viaShow (BV.asSigned w bv) PP.<+> PP.parens (PP.pretty (BV.ppHex w bv))
    unsigned :: forall ann w. (1 <= w) => NatRepr w -> BV w -> PP.Doc ann
    unsigned w bv =
      PP.viaShow (BV.asUnsigned bv) PP.<+> PP.parens (PP.pretty (BV.ppHex w bv))

-- | A \"relational\" constraint across several values.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data RelationalConstraint m (argTypes :: Ctx (FullType m))
  = -- | The first argument (a bitvector) is equal to the size of the allocation
    -- pointed to by the second.
    --
    -- @inTy@ and @inTy'@ are the overall types of the global variables or
    -- arguments to which this constraint applies. It's enforced that this
    -- constraint only applies to a value of integer type and a value of pointer
    -- type.
    forall inTy inTy' ft ft'.
    SizeOfAllocation
      (Selector m argTypes inTy ('FTInt ft))
      (Selector m argTypes inTy' ('FTPtr ft'))

--------------------------------------------------------------------------------

-- * Collections of constraints

data ConstrainedTypedValue m = forall ft.
  ConstrainedTypedValue
  { constrainedType :: FullTypeRepr m ft,
    constrainedValue :: ConstrainedShape m ft
  }

--------------------------------------------------------------------------------

-- * 'ConstrainedShape'

-- | A specification of the shape (memory layout) of a value and constraints on
-- it. See also the comment on 'Constraint'.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
newtype ConstrainedShape m (ft :: FullType m) = ConstrainedShape
  {getConstrainedShape :: Shape m (Compose [] (Constraint m)) ft}

minimalConstrainedShape :: FullTypeRepr m ft -> ConstrainedShape m ft
minimalConstrainedShape =
  ConstrainedShape . fmapFC (\_ -> Compose []) . Shape.minimal

instance Eq (ConstrainedShape m ft) where
  ConstrainedShape shape1 == ConstrainedShape shape2 =
    Shape.eqShape (\(Compose c1) (Compose c2) -> c1 == c2) shape1 shape2
