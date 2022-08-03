{-
Module           : UCCrux.LLVM.View.Constraint
Description      : See "UCCrux.LLVM.View".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module UCCrux.LLVM.View.Constraint
  ( -- * Constraint
    ViewConstraintError,
    ppViewConstraintError,
    ConstraintView(..),
    constraintView,
    viewConstraint,
    -- * ConstrainedShape
    ViewConstrainedShapeError,
    ppViewConstrainedShapeError,
    ConstrainedShapeView(..),
    constrainedShapeView,
    viewConstrainedShape,
    -- * ConstrainedTypedValue
    ConstrainedTypedValueViewError(..),
    ppConstrainedTypedValueViewError,
    ConstrainedTypedValueView(..),
    constrainedTypedValueView,
    viewConstrainedTypedValue,
  )
where

import           Control.Monad (when)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import qualified Data.BitVector.Sized as BV
import           Data.Functor.Compose (Compose(Compose, getCompose))
import           Data.Type.Equality (testEquality)
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some (Some(Some))

import           Lang.Crucible.LLVM.DataLayout (Alignment)

import           UCCrux.LLVM.Constraints (Constraint(..), ConstrainedShape(..), ConstrainedTypedValue(..))
import           UCCrux.LLVM.FullType.PP (ppFullTypeRepr)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), SomeFullTypeRepr(..), ModuleTypes)
import           UCCrux.LLVM.View.FullType (FullTypeReprView, FullTypeReprViewError, fullTypeReprView, viewFullTypeRepr, ppFullTypeReprViewError)
import qualified UCCrux.LLVM.View.Idioms as Idioms
import           UCCrux.LLVM.View.Shape (ShapeView, ViewShapeError, shapeView, viewShape, ppViewShapeError)
import           UCCrux.LLVM.View.Util () -- Alignment, ICmpOp instance

-- Helper, not exported. Equivalent to Data.Bifunctor.first.
liftError :: (e -> i) -> Either e a -> Either i a
liftError l =
  \case
    Left e -> Left (l e)
    Right v -> Right v

--------------------------------------------------------------------------------
-- * Constraint

data ViewConstraintError
  = BVNegative Integer
  | BVOutOfRange Natural Integer
  | BVZeroWidth Integer
  deriving (Eq, Ord, Show)

ppViewConstraintError :: ViewConstraintError -> Doc ann
ppViewConstraintError =
  \case
    BVNegative vbv ->
      "Negative unsigned bitvector: " <> PP.viaShow vbv
    BVOutOfRange vwidth vbv ->
      PP.hsep
        [ "Bitvector",
          PP.viaShow vbv,
          "out of range for width",
          PP.viaShow vwidth
        ]
    BVZeroWidth vbv ->
      PP.hsep
        [ "Bitvector",
          PP.viaShow vbv,
          "had a specified width of 0"
        ]

data ConstraintView
  = AlignedView Alignment
  | BVCmpView L.ICmpOp Natural Integer
  deriving (Eq, Ord, Generic, Show)

constraintView :: Constraint m atTy -> ConstraintView
constraintView =
  \case
    Aligned align -> AlignedView align
    BVCmp op width bv ->
      BVCmpView op (NatRepr.natValue width) (BV.asUnsigned bv)

viewConstraint ::
  ConstraintView ->
  Either ViewConstraintError (Some (Constraint m))
viewConstraint =
  \case
    AlignedView align -> Right (Some (Aligned align))
    BVCmpView op vwidth vbv ->
      do check (vbv < 0) (BVNegative vbv)
         Some width <- return (NatRepr.mkNatRepr vwidth)
         let clamped = BV.unsignedClamp width vbv
         check (BV.asUnsigned clamped /= vbv) (BVOutOfRange vwidth vbv)
         NatRepr.LeqProof <-
           liftMaybe (BVZeroWidth vbv) (NatRepr.testLeq (NatRepr.knownNat @1) width)
         Right (Some (BVCmp op width clamped))
  where
    check cond err = when cond (Left err)
    liftMaybe err =
      \case
        Nothing -> Left err
        Just v -> Right v

--------------------------------------------------------------------------------
-- * ConstrainedShape

data ViewConstrainedShapeError
  = BadBitvectorWidth Natural Natural
  | BadConstraint SomeFullTypeRepr ConstraintView
  | ViewConstraintError ViewConstraintError

ppViewConstrainedShapeError :: ViewConstrainedShapeError -> Doc ann
ppViewConstrainedShapeError =
  \case
    BadBitvectorWidth expect found ->
      PP.hsep
        [ "Incorrect bitvector width in constraint, found"
        , PP.viaShow found
        , "but expected"
        , PP.viaShow expect
        ]
    BadConstraint (SomeFullTypeRepr t) vc ->
      PP.hsep
        [  "Invalid constraint for type:"
        , PP.viaShow vc
        , ppFullTypeRepr t
        ]
    ViewConstraintError err -> ppViewConstraintError err

newtype ConstrainedShapeView =
  ConstrainedShapeView
    { getConstrainedShapeView :: ShapeView [ConstraintView] }
  deriving (Eq, Ord, Generic, Show)

constrainedShapeView :: ConstrainedShape m ft -> ConstrainedShapeView
constrainedShapeView =
  ConstrainedShapeView .
    shapeView (map constraintView . getCompose) .
    getConstrainedShape

viewConstrainedShape ::
  forall m ft.
  ModuleTypes m ->
  FullTypeRepr m ft ->
  ConstrainedShapeView ->
  Either (ViewShapeError ViewConstrainedShapeError) (ConstrainedShape m ft)
viewConstrainedShape mts ft =
  fmap ConstrainedShape .
    viewShape mts tag ft .
    getConstrainedShapeView
  where
    tag ::
      forall t.
      FullTypeRepr m t ->
      [ConstraintView] ->
      Either ViewConstrainedShapeError (Compose [] (Constraint m) t)
    tag t cs = Compose <$> traverse (go t) cs

    go ::
      forall t.
      FullTypeRepr m t ->
      ConstraintView ->
      Either ViewConstrainedShapeError (Constraint m t)
    go t vc =
      do c <- liftError ViewConstraintError (viewConstraint vc)
         case (t, c) of
           (FTIntRepr width, Some (BVCmp op width' bv)) ->
             case testEquality width width' of
               Just NatRepr.Refl -> Right (BVCmp op width bv)
               Nothing ->
                 Left (BadBitvectorWidth (NatRepr.natValue width) (NatRepr.natValue width'))
           (FTPtrRepr{}, Some (Aligned align)) -> Right (Aligned align)
           _ -> Left (BadConstraint (SomeFullTypeRepr t) vc)

--------------------------------------------------------------------------------
-- * ConstrainedTypedValue

data ConstrainedTypedValueViewError
  = FullTypeReprViewError FullTypeReprViewError
  | ViewConstrainedShapeError (ViewShapeError ViewConstrainedShapeError)

ppConstrainedTypedValueViewError ::
  ConstrainedTypedValueViewError ->
  Doc ann
ppConstrainedTypedValueViewError =
  \case
    FullTypeReprViewError err ->
      ppFullTypeReprViewError err
    ViewConstrainedShapeError err ->
      ppViewShapeError ppViewConstrainedShapeError err

data ConstrainedTypedValueView =
  ConstrainedTypedValueView
  { vConstrainedType :: FullTypeReprView,
    vConstrainedValue :: ConstrainedShapeView
  }
  deriving (Eq, Ord, Generic, Show)

constrainedTypedValueView :: ConstrainedTypedValue m -> ConstrainedTypedValueView
constrainedTypedValueView (ConstrainedTypedValue ty val) =
  ConstrainedTypedValueView (fullTypeReprView ty) (constrainedShapeView val)

viewConstrainedTypedValue ::
  ModuleTypes m ->
  ConstrainedTypedValueView ->
  Either ConstrainedTypedValueViewError (ConstrainedTypedValue m)
viewConstrainedTypedValue mts (ConstrainedTypedValueView vty vval) =
  do Some ft <- liftError FullTypeReprViewError (viewFullTypeRepr mts vty)
     shape <-
       liftError ViewConstrainedShapeError (viewConstrainedShape mts ft vval)
     return (ConstrainedTypedValue ft shape)

-- See module docs for "UCCrux.LLVM.View.Idioms".
$(Aeson.TH.deriveJSON
  (Idioms.constructorSuffix "View" Aeson.defaultOptions)
  ''ConstraintView)
$(Aeson.TH.deriveJSON
  Aeson.defaultOptions { Aeson.unwrapUnaryRecords = True }
  ''ConstrainedShapeView)
$(Aeson.TH.deriveJSON
  (Idioms.recordSelectorPrefix "vConstrained" Aeson.defaultOptions)
  ''ConstrainedTypedValueView)
