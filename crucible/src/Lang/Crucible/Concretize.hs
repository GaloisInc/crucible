-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Concretize
-- Description      : Get feasible concrete values from a model
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- This module defines 'concRegValue', a function that takes a 'RegValue' (i.e.,
-- a symbolic value), and a model from the SMT solver ('W4GE.GroundEvalFn'), and
-- returns the concrete value that the symbolic value takes in the model.
--
-- This can be used to report specific values that lead to violations of
-- assertions, including safety assertions.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Concretize
  ( ConcRegValue
  , ConcRV'(..)
  , ConcAnyValue(..)
  , ConcIntrinsic
  , IntrinsicConcFn(..)
  , ConcCtx(..)
  , concRegValue
  ) where

import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word (Word16)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import           What4.Expr (Expr)
import qualified What4.Expr.GroundEval as W4GE
import           What4.Interface (SymExpr)
import qualified What4.Interface as W4I
import qualified What4.Partial as W4P

import           Lang.Crucible.FunctionHandle (FnHandle, RefCell)
import           Lang.Crucible.Simulator.Intrinsics (Intrinsic)
import           Lang.Crucible.Simulator.RegValue (RegValue, FnVal)
import qualified Lang.Crucible.Simulator.RegValue as RV
import qualified Lang.Crucible.Simulator.SymSequence as SymSeq
import qualified Lang.Crucible.Utils.MuxTree as MuxTree
import           Lang.Crucible.Types

-- | Newtype to allow partial application of 'ConcRegValue'.
--
-- Type families cannot appear partially applied.
type ConcRV' :: Type -> CrucibleType -> Type
newtype ConcRV' sym tp = ConcRV' { unConcRV' :: ConcRegValue sym tp }

-- | Defines the \"concrete\" interpretations of 'CrucibleType' (as opposed
-- to the \"symbolic\" interpretations, which are defined by 'RegValue'), as
-- returned by 'concRegValue'.
--
-- Unlike What4\'s 'W4GE.GroundValue', this type family is parameterized
-- by @sym@, the symbolic backend. This is because Crucible makes use of
-- \"interpreted\" floating point numbers ('SymInterpretedFloatType'). What4\'s
-- @SymFloat@ always uses an IEEE-754 interpretation of symbolic floats, whereas
-- 'SymInterpretedFloatType' can use IEEE-754, real numbers, or uninterpreted
-- functions depending on how the symbolic backend is configured.
type ConcRegValue :: Type -> CrucibleType -> Type
type family ConcRegValue sym tp where
  ConcRegValue sym (BaseToType bt) = W4GE.GroundValue bt
  ConcRegValue sym (FloatType fi) = W4GE.GroundValue (SymInterpretedFloatType sym fi)
  ConcRegValue sym AnyType = ConcAnyValue sym
  ConcRegValue sym UnitType = ()
  ConcRegValue sym NatType = Integer
  ConcRegValue sym CharType = Word16
  ConcRegValue sym (FunctionHandleType a r) = ConcFnVal sym a r
  ConcRegValue sym (MaybeType tp) = Maybe (ConcRegValue sym tp)
  ConcRegValue sym (VectorType tp) = V.Vector (ConcRV' sym tp)
  ConcRegValue sym (SequenceType tp) = [ConcRV' sym tp]
  ConcRegValue sym (StructType ctx) = Ctx.Assignment (ConcRV' sym) ctx
  ConcRegValue sym (VariantType ctx) = Ctx.Assignment (ConcVariantBranch sym) ctx
  ConcRegValue sym (ReferenceType tp) = [RefCell tp]
  ConcRegValue sym (WordMapType w tp) = ()  -- TODO: possible to do something meaningful?
  ConcRegValue sym (RecursiveType nm ctx) = ConcRegValue sym (UnrollType nm ctx)
  ConcRegValue sym (IntrinsicType nm ctx) = ConcIntrinsic nm ctx
  ConcRegValue sym (StringMapType tp) = Map Text (ConcRV' sym tp)

---------------------------------------------------------------------
-- * ConcCtx

-- | Context needed for 'concRegValue'
--
-- The @t@ parameter matches that on 'W4GE.GroundEvalFn' and 'Expr', namely, it
-- is a phantom type brand used to relate nonces to a specific nonce generator
-- (similar to the @s@ parameter of the @ST@ monad). It also appears as the
-- first argument to 'ExprBuilder'.
data ConcCtx sym t
  = ConcCtx
  { -- | Model returned from SMT solver
    model :: W4GE.GroundEvalFn t
    -- | How to ground intrinsics
  , intrinsicConcFuns :: MapF SymbolRepr (IntrinsicConcFn t)
  }

-- | Helper, not exported
ground ::
  ConcCtx sym t ->
  Expr t tp ->
  IO (ConcRegValue sym (BaseToType tp))
ground (ConcCtx (W4GE.GroundEvalFn ge) _) = ge

---------------------------------------------------------------------
-- * Helpers

-- | Helper, not exported
ite ::
  (SymExpr sym ~ Expr t) =>
  ConcCtx sym t ->
  W4I.Pred sym ->
  a ->
  a ->
  IO a
ite ctx p t f = do
  b <- ground ctx p
  pure (if b then t else f)

-- | Helper, not exported
iteIO ::
  (SymExpr sym ~ Expr t) =>
  ConcCtx sym t ->
  W4I.Pred sym ->
  IO a ->
  IO a ->
  IO a
iteIO ctx p t f = do
  b <- ground ctx p
  if b then t else f

-- | Helper, not exported
concPartial ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  TypeRepr tp ->
  W4P.Partial (W4I.Pred sym) (RegValue sym tp) ->
  IO (Maybe (ConcRegValue sym tp))
concPartial ctx tp (W4P.Partial p v) =
  iteIO ctx p (Just <$> concRegValue ctx tp v) (pure Nothing)

-- | Helper, not exported
concPartialWithErr ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  TypeRepr tp ->
  W4P.PartialWithErr e (W4I.Pred sym) (RegValue sym tp) ->
  IO (Maybe (ConcRegValue sym tp))
concPartialWithErr ctx tp =
  \case
    W4P.Err _ -> pure Nothing
    W4P.NoErr pv -> concPartial ctx tp pv

---------------------------------------------------------------------
-- * Intrinsics

-- | Open type family for defining how intrinsics are concretized
type ConcIntrinsic :: Symbol -> Ctx CrucibleType -> Type
type family ConcIntrinsic nm ctx

-- | Function for concretizing an intrinsic type
type IntrinsicConcFn :: Type -> Symbol -> Type
newtype IntrinsicConcFn t nm
  = IntrinsicConcFn
    (forall sym ctx.
      SymExpr sym ~ Expr t =>
      W4I.IsExprBuilder sym =>
      ConcCtx sym t ->
      Ctx.Assignment TypeRepr ctx ->
      Intrinsic sym nm ctx ->
      IO (ConcRegValue sym (IntrinsicType nm ctx)))

-- | Helper, not exported
tryConcIntrinsic ::
  forall sym nm ctx t.
  SymExpr sym ~ Expr t =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  SymbolRepr nm ->
  Ctx.Assignment TypeRepr ctx ->
  RegValue sym (IntrinsicType nm ctx) ->
  Maybe (IO (ConcRegValue sym (IntrinsicType nm ctx)))
tryConcIntrinsic ctx nm tyCtx v = do
    case MapF.lookup nm (intrinsicConcFuns ctx) of
      Nothing -> Nothing
      Just (IntrinsicConcFn f) -> Just (f @sym @ctx ctx tyCtx v)

---------------------------------------------------------------------
-- * Any

-- | An 'AnyValue' concretized by 'concRegValue'
data ConcAnyValue sym = forall tp. ConcAnyValue (TypeRepr tp) (ConcRV' sym tp)

---------------------------------------------------------------------
-- * FnVal

-- | A 'FnVal' concretized by 'concRegValue'
data ConcFnVal (sym :: Type) (args :: Ctx CrucibleType) (res :: CrucibleType) where
  ConcClosureFnVal ::
    !(ConcFnVal sym (args ::> tp) ret) ->
    !(TypeRepr tp) ->
    !(ConcRV' sym tp) ->
    ConcFnVal sym args ret

  ConcVarargsFnVal ::
    !(FnHandle (args ::> VectorType AnyType) ret) ->
    !(CtxRepr addlArgs) ->
    ConcFnVal sym (args <+> addlArgs) ret

  ConcHandleFnVal ::
    !(FnHandle a r) ->
    ConcFnVal sym a r

-- | Helper, not exported
concFnVal ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  CtxRepr args ->
  TypeRepr ret ->
  FnVal sym args ret ->
  IO (ConcFnVal sym args ret)
concFnVal ctx args ret =
  \case
    RV.ClosureFnVal fv t v -> do
      concV <- concFnVal ctx (args Ctx.:> t) ret fv
      v' <- concRegValue ctx t v
      pure (ConcClosureFnVal concV t (ConcRV' v'))
    RV.VarargsFnVal hdl extra ->
      pure (ConcVarargsFnVal hdl extra)
    RV.HandleFnVal hdl ->
      pure (ConcHandleFnVal hdl)

---------------------------------------------------------------------
-- * Reference

-- | Helper, not exported
concMux ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  MuxTree.MuxTree sym a ->
  IO [a]
concMux ctx = go . MuxTree.viewMuxTree
  where
    go [] = pure []
    go ((val, p):xs) = do
      f <- ite ctx p (val:) id
      f <$> go xs

---------------------------------------------------------------------
-- * Sequence

-- | Helper, not exported
concSymSequence ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  TypeRepr tp ->
  SymSeq.SymSequence sym (RegValue sym tp) ->
  IO [ConcRV' sym tp]
concSymSequence ctx tp =
  \case
    SymSeq.SymSequenceNil -> pure []
    SymSeq.SymSequenceCons _nonce v rest -> do
      v' <- concRegValue ctx tp v
      (ConcRV' v' :) <$> concSymSequence ctx tp rest
    SymSeq.SymSequenceAppend _nonce xs ys ->
      (++) <$> concSymSequence ctx tp xs <*> concSymSequence ctx tp ys
    SymSeq.SymSequenceMerge _nonce p ts fs ->
      concSymSequence ctx tp =<< ite ctx p ts fs

---------------------------------------------------------------------
-- * StringMap

-- | Helper, not exported
concStringMap ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  TypeRepr tp ->
  RegValue sym (StringMapType tp) ->
  IO (Map Text (ConcRV' sym tp))
concStringMap ctx tp v = Map.fromList <$> go (Map.toList v)
  where
    go [] = pure []
    go ((t, v'):xs) =
      concPartialWithErr ctx tp v' >>=
        \case
          Nothing -> go xs
          Just v'' -> ((t, ConcRV' v''):) <$> go xs

---------------------------------------------------------------------
-- * Variant

-- | Note that we do not attempt to \"normalize\" variants in 'concRegValue'
-- in any way. If the model reports that multiple branches of a variant are
-- plausible, then multiple branches might be included as 'Just's.
newtype ConcVariantBranch sym tp
  = ConcVariantBranch (Maybe (ConcRV' sym tp))

-- | Helper, not exported
concVariant ::
  forall sym variants t.
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  Ctx.Assignment TypeRepr variants ->
  RegValue sym (VariantType variants) ->
  IO (ConcRegValue sym (VariantType variants))
concVariant ctx tps vs = Ctx.zipWithM concBranch tps vs
  where
    concBranch :: forall tp. TypeRepr tp -> RV.VariantBranch sym tp -> IO (ConcVariantBranch sym tp)
    concBranch tp (RV.VB v) = do
      v' <- concPartialWithErr ctx tp v
      case v' of
        Just v'' -> pure (ConcVariantBranch (Just (ConcRV' v'')))
        Nothing -> pure (ConcVariantBranch Nothing)

---------------------------------------------------------------------
-- * 'concRegValue'

-- | Pick a feasible concrete value from the model
--
-- This function does not attempt to \"normalize\" variants nor mux trees in any
-- way. If the model reports that multiple branches of a variant or mux tree are
-- plausible, then multiple branches might be included in the result.
concRegValue ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  TypeRepr tp ->
  RegValue sym tp ->
  IO (ConcRegValue sym tp)
concRegValue ctx tp v =
  case (tp, v) of
    -- Base types
    (BoolRepr, _) -> ground ctx v
    (BVRepr _width, _) -> ground ctx v
    (ComplexRealRepr, _) -> ground ctx v
    (FloatRepr _fpp, _) -> ground ctx v
    (IEEEFloatRepr _fpp, _) -> ground ctx v
    (IntegerRepr, _) -> ground ctx v
    (NatRepr, _) -> ground ctx (W4I.natToIntegerPure v)
    (RealValRepr, _) -> ground ctx v
    (StringRepr _, _) -> ground ctx v
    (SymbolicArrayRepr _idxs _tp', _) -> ground ctx v
    (SymbolicStructRepr _tys, _) -> ground ctx v
  
    -- Trivial cases
    (UnitRepr, ()) -> pure ()
    (CharRepr, _) -> pure v

    -- Simple recursive cases
    (AnyRepr, RV.AnyValue tp' v') ->
      ConcAnyValue tp' . ConcRV' <$> concRegValue ctx tp' v'
    (RecursiveRepr symb tyCtx, RV.RolledType v') -> 
      concRegValue ctx (unrollType symb tyCtx) v'
    (StructRepr tps, _) ->
      Ctx.zipWithM (\tp' (RV.RV v') -> ConcRV' <$> concRegValue ctx tp' v') tps v
    (VectorRepr tp', _) ->
      traverse (fmap ConcRV' . concRegValue ctx tp') v

    -- Cases with helper functions
    (MaybeRepr tp', _) ->
      concPartialWithErr ctx tp' v
    (FunctionHandleRepr args ret, _) ->
      concFnVal ctx args ret v
    (IntrinsicRepr nm tyCtx, _) ->
      case tryConcIntrinsic ctx nm tyCtx v of
        Nothing -> 
          let strNm = Text.unpack (symbolRepr nm) in
          fail ("Missing concretization function for intrinsic: " ++ strNm)
        Just r -> r
    (ReferenceRepr _, _) ->
      concMux ctx v
    (SequenceRepr tp', _) ->
      concSymSequence ctx tp' v
    (StringMapRepr tp', _) ->
      concStringMap ctx tp' v
    (VariantRepr tps, _) ->
      concVariant ctx tps v

    -- Incomplete cases
    (WordMapRepr _ _, _) -> pure ()
