{-
Module       : UCCrux.LLVM.Classify.Poison
Description  : Classify errors as true positives or due to missing preconditions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Classify.Poison (classifyPoison) where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.))
import           Control.Monad.IO.Class (MonadIO, liftIO)

import           Data.Bifunctor (bimap)
import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import           Data.Parameterized.NatRepr (NatRepr, type (<=))
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Concrete as What4
import qualified What4.Interface as What4

import qualified Lang.Crucible.Simulator as Crucible

import qualified Lang.Crucible.LLVM.Errors.Poison as Poison

import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Classify.Types
import           UCCrux.LLVM.Cursor (ppCursor, SomeInSelector(SomeInSelector), Where, selectWhere, selectorCursor)
import           UCCrux.LLVM.Constraints (Constraint(BVCmp), NewConstraint(..))
import           UCCrux.LLVM.FullType.Type (FullType(FTInt), FullTypeRepr(FTIntRepr))
import           UCCrux.LLVM.Logging (Verbosity(Hi))
import           UCCrux.LLVM.Setup.Monad (TypedSelector(..))
{- ORMOLU_ENABLE -}

getTermAnn ::
  What4.IsExprBuilder sym =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  What4.SymExpr sym tp ->
  Maybe (Some (TypedSelector m arch argTypes))
getTermAnn sym annotations expr =
  do
    ann <- What4.getAnnotation sym expr
    Map.lookup (Some ann) annotations

-- | For poison values created via arithmetic operations, it's easy to deduce a
-- precondition when one of the operands is an argument to the function, and the
-- other is concrete. For example, if the operation is 32-bit signed addition
-- overflow and the concrete operand is @1@, then the argument should be bounded
-- above by @MAX_SIGNED_32 - 1@ so that the addition doesn't overflow.
--
-- This function has a weird return type because the \"handedness\" of the
-- result is significant - whether the argument was on the LHS or RHS of a
-- subtraction, division, or any other non-commutative operation.
annotationAndValue ::
  What4.IsExprBuilder sym =>
  sym ->
  -- | Term annotations (origins), see comment on
  -- 'UCCrux.LLVM.Setup.Monad.resultAnnotations'.
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  What4.SymBV sym w ->
  What4.SymBV sym w ->
  Maybe (Some (TypedSelector m arch argTypes), Either (BV w) (BV w))
annotationAndValue sym annotations op1 op2 =
  case ( getTermAnn sym annotations op1,
         What4.asConcrete op1,
         getTermAnn sym annotations op2,
         What4.asConcrete op2
       ) of
    (Just ann, Nothing, Nothing, Just val) ->
      Just (ann, Left (What4.fromConcreteBV val))
    (Nothing, Just val, Just ann, _) ->
      Just (ann, Right (What4.fromConcreteBV val))
    _ -> Nothing

-- | Handle signed overflow by adding bounds on input bitvectors.
handleBVOp ::
  (MonadIO f, What4.IsExprBuilder sym) =>
  AppContext ->
  sym ->
  -- | Term annotations (origins), see comment on
  -- 'UCCrux.LLVM.Setup.Monad.resultAnnotations'.
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  (Where -> Diagnosis) ->
  What4.SymBV sym w ->
  What4.SymBV sym w ->
  -- | See comment on 'annotationAndValue' - the 'Either' indicates whether the
  -- concrete bitvector was on the LHS or RHS of the bitvector operation.
  ( forall w'.
    1 <= w' =>
    NatRepr w' ->
    Either (BV w') (BV w') ->
    Maybe (Constraint m ('FTInt w'))
  ) ->
  f (Maybe (Explanation m arch argTypes))
handleBVOp appCtx sym annotations diagnosis op1 op2 constraint =
  case annotationAndValue sym annotations op1 op2 of
    -- The argument was on the LHS of the operation
    Just (Some (TypedSelector ftRepr (SomeInSelector selector)), concreteSummand) ->
      do
        let d = diagnosis (selectWhere selector)
        liftIO $
          (appCtx ^. log) Hi $
            Text.unwords
              [ "Diagnosis:",
                Text.pack (show (diagnose d)),
                "at",
                Text.pack (show (ppCursor "<top>" (selector ^. selectorCursor)))
              ]
        liftIO $ (appCtx ^. log) Hi (prescribe (diagnosisTag d))
        case ftRepr of
          FTIntRepr w ->
            pure $
              ExDiagnosis
                . (d,)
                . (: [])
                . NewConstraint (SomeInSelector selector)
                <$>
                -- NOTE(lb): The trunc' operation here *should* be a
                -- no-op, but since the Poison constructors don't have a
                -- NatRepr, we can't check. That's fixable, but not high
                -- priority since we'd just panic anyway if the widths
                -- didn't match.
                constraint w (bimap (BV.trunc' w) (BV.trunc' w) concreteSummand)
          _ -> pure Nothing
    _ -> pure Nothing

classifyPoison ::
  forall f sym m arch argTypes.
  (MonadIO f, What4.IsExprBuilder sym) =>
  AppContext ->
  sym ->
  -- | Term annotations (origins), see comment on
  -- 'UCCrux.LLVM.Setup.Monad.resultAnnotations'.
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  Poison.Poison (Crucible.RegValue' sym) ->
  f (Maybe (Explanation m arch argTypes))
classifyPoison appCtx sym annotations =
  \case
    Poison.AddNoSignedWrap (Crucible.RV op1) (Crucible.RV op2) ->
      handleBVOp
        appCtx
        sym
        annotations
        (Diagnosis DiagnoseAddSignedWrap)
        op1
        op2
        ( \w concreteSummand ->
            let bv = commutative concreteSummand
                zeroBv = BV.mkBV w 0
             in if BV.sle w zeroBv bv
                  then -- If the concrete summand was positive, we need to
                  -- ensure the argument is that much less than the maximum
                  -- representable value.
                    Just $ BVCmp L.Islt w (BV.sub w (BV.maxSigned w) bv)
                  else -- If the concrete summand was negative, we need to
                  -- ensure the argument is that much greater than the minimum
                  -- representable value.
                    Just $ BVCmp L.Isgt w (BV.sub w (BV.minSigned w) bv)
        )
    Poison.SubNoSignedWrap (Crucible.RV op1) (Crucible.RV op2) ->
      handleBVOp
        appCtx
        sym
        annotations
        (Diagnosis DiagnoseSubSignedWrap)
        op1
        op2
        ( \w concreteSummand ->
            -- Similar to addition but with more cases because subtraction isn't
            -- commutative.
            let zeroBv = BV.mkBV w 0
             in case concreteSummand of
                  Left bv ->
                    if BV.sle w zeroBv bv
                      then -- Concrete BV was positive and on LHS
                        Nothing
                      else -- Concrete BV was negative and on LHS
                        Nothing
                  Right bv ->
                    if BV.sle w zeroBv bv
                      then -- Concrete BV was positive and on RHS
                        Just $ BVCmp L.Isgt w (BV.add w (BV.minSigned w) bv)
                      else -- Concrete BV was negative and on RHS
                        Just $ BVCmp L.Islt w (BV.add w (BV.maxSigned w) bv)
        )
    _ -> pure Nothing
  where
    -- Commutative operations don't care about which thing appeared on which
    -- side.
    commutative =
      \case
        Left bv -> bv
        Right bv -> bv
