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
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module UCCrux.LLVM.View.Constraint
  ( ViewConstraintError,
    ppViewConstraintError,
    ConstraintView(..),
    constraintView,
    viewConstraint,
  )
where

import           Control.Monad (when)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import qualified Data.BitVector.Sized as BV
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some (Some(Some))

import           Lang.Crucible.LLVM.DataLayout (Alignment)

import           UCCrux.LLVM.Constraints (Constraint(..))
import           UCCrux.LLVM.View.Util () -- Alignment, ICmpOp instance

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
  = VAligned Alignment
  | VBVCmp L.ICmpOp Natural Integer
  deriving (Eq, Ord, Generic, Show)

constraintView :: Constraint m atTy -> ConstraintView
constraintView =
  \case
    Aligned align -> VAligned align
    BVCmp op width bv ->
      VBVCmp op (NatRepr.natValue width) (BV.asUnsigned bv)

viewConstraint ::
  ConstraintView ->
  Either ViewConstraintError (Some (Constraint m))
viewConstraint =
  \case
    VAligned align -> Right (Some (Aligned align))
    VBVCmp op vwidth vbv ->
      do guard (vbv < 0) (BVNegative vbv)
         Some width <- return (NatRepr.mkNatRepr vwidth)
         let clamped = BV.unsignedClamp width vbv
         guard (BV.asUnsigned clamped /= vbv) (BVOutOfRange vwidth vbv)
         NatRepr.LeqProof <-
           liftMaybe (BVZeroWidth vbv) (NatRepr.testLeq (NatRepr.knownNat @1) width)
         Right (Some (BVCmp op width clamped))
  where
    guard cond err = when cond (Left err)
    liftMaybe err =
      \case
        Nothing -> Left err
        Just v -> Right v

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''ConstraintView)
