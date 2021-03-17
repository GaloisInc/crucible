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
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.Classify.Poison (classifyPoison) where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Control.Lens ((^.), to)
import           Control.Monad.IO.Class (MonadIO, liftIO)

import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Functor.Const (Const(getConst))
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import           Data.Parameterized.Classes (IxedF'(ixF'))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (NatRepr, type (<=))
import           Data.Parameterized.Some (Some(Some))

import qualified What4.Concrete as What4
import qualified What4.Interface as What4

import qualified Lang.Crucible.Simulator as Crucible

import qualified Lang.Crucible.LLVM.Errors.Poison as Poison

import           UCCrux.LLVM.Context.App (AppContext, log)
import           UCCrux.LLVM.Context.Function (FunctionContext, argumentNames)
import           UCCrux.LLVM.Classify.Types
import           UCCrux.LLVM.Cursor (ppCursor, Selector(..), SomeInSelector(SomeInSelector))
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

annotationAndValue ::
  What4.IsExprBuilder sym =>
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  What4.SymBV sym w ->
  What4.SymBV sym w ->
  Maybe (Some (TypedSelector m arch argTypes), BV w)
annotationAndValue sym annotations op1 op2 =
  case ( getTermAnn sym annotations op1,
         What4.asConcrete op1,
         getTermAnn sym annotations op2,
         What4.asConcrete op2
       ) of
    (Just ann, Nothing, Nothing, Just val) ->
      Just (ann, What4.fromConcreteBV val)
    (Nothing, Just val, Just ann, _) ->
      Just (ann, What4.fromConcreteBV val)
    _ -> Nothing

handleBVOp ::
  (MonadIO f, What4.IsExprBuilder sym) =>
  AppContext ->
  FunctionContext m arch argTypes ->
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  MissingPreconditionTag ->
  What4.SymBV sym w ->
  What4.SymBV sym w ->
  (forall w'. 1 <= w' => NatRepr w' -> BV w' -> Constraint m ('FTInt w')) ->
  f (Maybe (Explanation m arch argTypes))
handleBVOp appCtx funCtx sym annotations tag op1 op2 constraint =
  case annotationAndValue sym annotations op1 op2 of
    Just (Some (TypedSelector ftRepr (SomeInSelector (SelectArgument idx cursor))), concreteSummand) ->
      do
        let argName i =
              funCtx ^. argumentNames . ixF' i . to getConst . to (maybe "<top>" Text.unpack)
        liftIO $
          (appCtx ^. log) Hi $
            Text.unwords
              [ "Diagnosis:",
                diagnose tag,
                "#" <> Text.pack (show (Ctx.indexVal idx)),
                "at",
                Text.pack (show (ppCursor (argName idx) cursor))
              ]
        liftIO $ (appCtx ^. log) Hi (prescribe tag)
        case ftRepr of
          FTIntRepr w ->
            pure $
              Just $
                ExMissingPreconditions
                  ( tag,
                    [ NewConstraint
                        (SomeInSelector (SelectArgument idx cursor))
                        (constraint w (BV.trunc' w concreteSummand))
                    ]
                  )
          _ -> pure Nothing
    _ -> pure Nothing

classifyPoison ::
  forall f sym m arch argTypes.
  (MonadIO f, What4.IsExprBuilder sym) =>
  AppContext ->
  FunctionContext m arch argTypes ->
  sym ->
  -- | Term annotations (origins)
  Map (Some (What4.SymAnnotation sym)) (Some (TypedSelector m arch argTypes)) ->
  Poison.Poison (Crucible.RegValue' sym) ->
  f (Maybe (Explanation m arch argTypes))
classifyPoison appCtx funCtx sym annotations =
  \case
    Poison.AddNoSignedWrap (Crucible.RV op1) (Crucible.RV op2) ->
      handleBVOp
        appCtx
        funCtx
        sym
        annotations
        ArgAddSignedWrap
        op1
        op2
        ( \w concreteSummand ->
            BVCmp L.Islt (BV.sub w (BV.maxSigned w) concreteSummand)
        )
    Poison.SubNoSignedWrap (Crucible.RV op1) (Crucible.RV op2) ->
      handleBVOp
        appCtx
        funCtx
        sym
        annotations
        ArgSubSignedWrap
        op1
        op2
        ( \w concreteSummand ->
            BVCmp L.Isgt (BV.add w (BV.minSigned w) concreteSummand)
        )
    _ -> pure Nothing
