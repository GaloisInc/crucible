-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Concretize
-- Description      : Get feasible concrete values from a model
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- This module defines three different kinds of functions. In order of how much
-- work they perform:
--
-- * /Grounding/ functions (e.g., 'groundRegValue') take symbolic values
--   ('RegValue's) and a model from an SMT solver ('W4GE.GroundEvalFn'), and
--   return the concrete value ('ConcRegValue') that the symbolic value takes in
--   the model. These functions can be used to report specific values that lead
--   to violations of assertions, including safety assertions.
-- * /Concretization/ functions (e.g., 'concRegValue') request a model that is
--   consistent with the current assumptions (e.g., path conditions) from the
--   symbolic backend, and then ground a value in that model. These can be used
--   to reduce the size and complexity of later queries to SMT solvers, at the
--   cost of no longer being sound from a verification standpoint.
-- * /Unique concretization/ functions (e.g., 'uniquelyConcRegValue') do the
--   same thing as concretization functions, but then check if the concrete
--   value is the /only possible/ value for the given symbolic expression in
--   /any/ model.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
  , asConcRegValue
  , asConcRegEntry
  , asConcRegMap
  , ConcAnyValue(..)
  , ConcIntrinsic
  , IntrinsicConcFn(..)
  , ConcCtx(..)
    -- * Grounding
  , groundRegValue
  , groundRegEntry
  , groundRegMap
    -- * Concretization
  , concRegValue
  , concRegEntry
  , concRegMap
    -- * Unique concretization
  , uniquelyConcRegValue
  , uniquelyConcRegEntry
  , uniquelyConcRegMap
    -- * There and back again
  , IntrinsicConcToSymFn(..)
  , concToSym
  ) where

import qualified Data.Foldable as F
import           Data.Functor.Const (Const(..))
import           Data.Kind (Type)
import           Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Proxy (Proxy(Proxy))
import           Data.Sequence (Seq)
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word (Word16)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC (traverseFC, foldlMFC)

import qualified What4.Concretize as W4C
import qualified What4.Config as W4Cfg
import           What4.Expr (Expr, ExprBuilder, Flags, FloatModeRepr(..))
import qualified What4.Expr.GroundEval as W4GE
import           What4.Interface (SymExpr)
import qualified What4.Interface as W4I
import qualified What4.Partial as W4P
import qualified What4.Protocol.Online as WPO
import qualified What4.SatResult as WSat

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import           Lang.Crucible.FunctionHandle (FnHandle, RefCell)
import           Lang.Crucible.Simulator.Intrinsics (Intrinsic)
import           Lang.Crucible.Simulator.RegMap (RegEntry, RegMap)
import qualified Lang.Crucible.Simulator.RegMap as RM
import           Lang.Crucible.Simulator.RegValue (RegValue, FnVal)
import qualified Lang.Crucible.Simulator.RegValue as RV
import qualified Lang.Crucible.Simulator.SymSequence as SymSeq
import qualified Lang.Crucible.Utils.MuxTree as MuxTree
import           Lang.Crucible.Types
import           Lang.Crucible.Panic (panic)

-- | Newtype to allow partial application of 'ConcRegValue'.
--
-- Type families cannot appear partially applied.
type ConcRV' :: Type -> CrucibleType -> Type
newtype ConcRV' sym tp = ConcRV' { unConcRV' :: ConcRegValue sym tp }

-- | Defines the \"concrete\" interpretations of 'CrucibleType' (as opposed
-- to the \"symbolic\" interpretations, which are defined by 'RegValue'), as
-- returned by 'groundRegValue'.
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
  ConcRegValue sym (SequenceType tp) = Seq (ConcRV' sym tp)
  ConcRegValue sym (StructType ctx) = Ctx.Assignment (ConcRV' sym) ctx
  ConcRegValue sym (VariantType ctx) = Ctx.Assignment (ConcVariantBranch sym) ctx
  ConcRegValue sym (ReferenceType tp) = NonEmpty (RefCell tp)
  ConcRegValue sym (WordMapType w tp) = ()  -- TODO: possible to do something meaningful?
  ConcRegValue sym (RecursiveType nm ctx) = ConcRegValue sym (UnrollType nm ctx)
  ConcRegValue sym (IntrinsicType nm ctx) = ConcIntrinsic nm ctx
  ConcRegValue sym (StringMapType tp) = Map Text (ConcRV' sym tp)

-- | Check if a 'RegValue' is actually concrete
asConcRegValue ::
  W4I.IsExpr (SymExpr sym) =>
  proxy sym ->
  TypeRepr tp ->
  RegValue sym tp ->
  Maybe (ConcRegValue sym tp)
asConcRegValue _proxy tp val =
  -- TODO: More cases could be added here.
  case asBaseType tp of
    AsBaseType {} -> W4GE.asGround val
    _ -> Nothing

-- | Check if a 'RM.RegEntry' is actually concrete
asConcRegEntry ::
  forall sym tp.
  W4I.IsExpr (SymExpr sym) =>
  RM.RegEntry sym tp ->
  Maybe (ConcRegValue sym tp)
asConcRegEntry (RM.RegEntry t v) = asConcRegValue (Proxy @sym) t v

-- | Check if a 'RM.RegMap' is actually concrete
asConcRegMap ::
  forall sym tp.
  W4I.IsExpr (SymExpr sym) =>
  RM.RegMap sym tp ->
  Maybe (Ctx.Assignment (ConcRV' sym) tp)
asConcRegMap (RM.RegMap assign) =
  traverseFC (\re -> ConcRV' <$> asConcRegEntry re) assign

---------------------------------------------------------------------
-- * ConcCtx

-- | Context needed for 'groundRegValue'
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
  iteIO ctx p (Just <$> groundRegValue ctx tp v) (pure Nothing)

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

-- | An 'AnyValue' concretized by 'groundRegValue'
data ConcAnyValue sym = forall tp. ConcAnyValue (TypeRepr tp) (ConcRV' sym tp)

---------------------------------------------------------------------
-- * FnVal

-- | A 'FnVal' concretized by 'groundRegValue'
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
      v' <- groundRegValue ctx t v
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
  IO (NonEmpty a)
concMux ctx mt = do
  l <- go (MuxTree.viewMuxTree mt)
  case NE.nonEmpty l of
    -- This is impossible because the only way to make a MuxTree is with
    -- `toMuxTree`, which uses `truePred`.
    Nothing ->
      panic "Lang.Crucible.Concretize.concMux"
        [ "Impossible: Mux tree had no feasible branches?" ]
    Just ne -> pure ne
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
  IO (Seq (ConcRV' sym tp))
concSymSequence ctx tp =
  SymSeq.concretizeSymSequence
    (ground ctx)
    (fmap ConcRV' . groundRegValue ctx tp)

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

-- | Note that we do not attempt to \"normalize\" variants in 'groundRegValue'
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
-- * 'groundRegValue'

-- | Pick a feasible concrete value from the model
--
-- This function does not attempt to \"normalize\" variants nor mux trees in any
-- way. If the model reports that multiple branches of a variant or mux tree are
-- plausible, then multiple branches might be included in the result.
groundRegValue ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  TypeRepr tp ->
  RegValue sym tp ->
  IO (ConcRegValue sym tp)
groundRegValue ctx tp v =
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
      ConcAnyValue tp' . ConcRV' <$> groundRegValue ctx tp' v'
    (RecursiveRepr symb tyCtx, RV.RolledType v') ->
      groundRegValue ctx (unrollType symb tyCtx) v'
    (StructRepr tps, _) ->
      Ctx.zipWithM (\tp' (RV.RV v') -> ConcRV' <$> groundRegValue ctx tp' v') tps v
    (VectorRepr tp', _) ->
      traverse (fmap ConcRV' . groundRegValue ctx tp') v

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

-- | Like 'groundRegValue', but for 'RegEntry'
groundRegEntry ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  RegEntry sym tp ->
  IO (ConcRegValue sym tp)
groundRegEntry ctx e = groundRegValue ctx (RM.regType e) (RM.regValue e)

-- | Like 'groundRegEntry', but for a whole 'RegMap'
groundRegMap ::
  (SymExpr sym ~ Expr t) =>
  W4I.IsExprBuilder sym =>
  ConcCtx sym t ->
  RegMap sym tps ->
  IO (Ctx.Assignment (ConcRV' sym) tps)
groundRegMap ctx (RM.RegMap m) = traverseFC (fmap ConcRV' . groundRegEntry ctx) m

---------------------------------------------------------------------
-- * 'concRegValue'

-- | Generate a model and pick a feasible concrete value from it
concRegValue ::
  forall tp sym bak solver scope st fs.
  ( CB.IsSymBackend sym bak
  , sym ~ ExprBuilder scope st fs
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  MapF SymbolRepr (IntrinsicConcFn scope) ->
  TypeRepr tp ->
  RegValue sym tp ->
  IO (Either W4C.ConcretizationFailure (ConcRegValue sym tp))
concRegValue bak iFns tp v = concRegEntry bak iFns (RM.RegEntry tp v)

-- | Generate a model and pick a feasible concrete value from it
concRegEntry ::
  forall tp sym bak solver scope st fs.
  ( CB.IsSymBackend sym bak
  , sym ~ ExprBuilder scope st fs
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  MapF SymbolRepr (IntrinsicConcFn scope) ->
  RM.RegEntry sym tp ->
  IO (Either W4C.ConcretizationFailure (ConcRegValue sym tp))
concRegEntry bak iFns re = do
  res <- concRegMap bak iFns (RM.RegMap (Ctx.singleton re))
  case res of
    Left e -> pure (Left e)
    Right (Ctx.Empty Ctx.:> ConcRV' concV) -> pure (Right concV)

-- | Like 'concRegValue', but for a whole 'RegMap'
concRegMap ::
  forall tps sym bak solver scope st fs.
  ( CB.IsSymBackend sym bak
  , sym ~ ExprBuilder scope st fs
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  MapF SymbolRepr (IntrinsicConcFn scope) ->
  RegMap sym tps ->
  IO (Either W4C.ConcretizationFailure (Ctx.Assignment (ConcRV' sym) tps))
concRegMap bak iFns m = do
  case asConcRegMap m of
    Just concM -> pure (Right concM)
    Nothing ->
      withEnabledOnline $ do
        let err = panic "concRegValue" ["requires online solving to be enabled"]
        cond <- CB.getPathCondition bak
        CBO.withSolverProcess bak err $ \sp -> do
          msat <- WPO.checkWithAssumptionsAndModel sp "concRegValue" [cond]
          case msat of
            WSat.Unknown -> pure $ Left W4C.SolverUnknown
            WSat.Unsat {} -> pure $ Left W4C.UnsatInitialAssumptions
            WSat.Sat mdl -> do
              let ctx = ConcCtx { model = mdl, intrinsicConcFuns = iFns }
              expr <- groundRegMap @sym ctx m
              pure (Right expr)
  where
    withEnabledOnline f = do
      let sym = CB.backendGetSym bak
      let conf = W4I.getConfiguration sym
      enabledOpt <- W4Cfg.getOptionSetting CBO.enableOnlineBackend conf
      wasEnabled <- W4Cfg.getOpt enabledOpt
      _ <- W4Cfg.setOpt enabledOpt True
      r <- f
      _ <- W4Cfg.setOpt enabledOpt wasEnabled
      pure r

---------------------------------------------------------------------
-- * 'uniquelyConcRegValue'

-- | Generate a model and pick a feasible concrete value from it
uniquelyConcRegValue ::
  forall tp sym bak solver scope st fm.
  ( CB.IsSymBackend sym bak
  , sym ~ ExprBuilder scope st (Flags fm)
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st (Flags fm)
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  FloatModeRepr fm ->
  MapF SymbolRepr (IntrinsicConcFn scope) ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  TypeRepr tp ->
  RegValue sym tp ->
  IO (Either W4C.UniqueConcretizationFailure (ConcRegValue sym tp))
uniquelyConcRegValue bak fm iFns sFns tp v =
  uniquelyConcRegEntry bak fm iFns sFns (RM.RegEntry tp v)

-- | Generate a model and pick a feasible concrete value from it
uniquelyConcRegEntry ::
  forall tp sym bak solver scope st fm.
  ( CB.IsSymBackend sym bak
  , sym ~ ExprBuilder scope st (Flags fm)
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st (Flags fm)
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  FloatModeRepr fm ->
  MapF SymbolRepr (IntrinsicConcFn scope) ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  RM.RegEntry sym tp ->
  IO (Either W4C.UniqueConcretizationFailure (ConcRegValue sym tp))
uniquelyConcRegEntry bak fm iFns sFns re = do
  res <- uniquelyConcRegMap bak fm iFns sFns (RM.RegMap (Ctx.singleton re))
  case res of
    Left e -> pure (Left e)
    Right (Ctx.Empty Ctx.:> ConcRV' concV) -> pure (Right concV)

-- | Like 'concRegValue', but for a whole 'RegMap'
uniquelyConcRegMap ::
  forall tps sym bak solver scope st fm.
  ( CB.IsSymBackend sym bak
  , sym ~ ExprBuilder scope st (Flags fm)
  , SymExpr sym ~ Expr scope
  , bak ~ CBO.OnlineBackend solver scope st (Flags fm)
  , WPO.OnlineSolver solver
  ) =>
  bak ->
  FloatModeRepr fm ->
  MapF SymbolRepr (IntrinsicConcFn scope) ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  RegMap sym tps ->
  IO (Either W4C.UniqueConcretizationFailure (Ctx.Assignment (ConcRV' sym) tps))
uniquelyConcRegMap bak fm iFns sFns m = do
  case asConcRegMap m of
    Just concM -> pure (Right concM)
    Nothing -> do
      -- First, check to see if there are a models of the symbolic values.
      concM_ <- concRegMap bak iFns m
      case concM_ of
        Left e -> pure (Left (W4C.GroundingFailure e))
        Right concM -> do
          -- We found a model, so check to see if this is the only possible
          -- model for these symbolic values.  We do this by adding a blocking
          -- clause that assumes the `RegValue`s are /not/ equal to the
          -- model we found in the previous step. If this is unsatisfiable,
          -- the `RegValue`s can only be equal to the first model, so we can
          -- conclude they are concrete. If it is satisfiable, on the other
          -- hand, the `RegValue`s can be multiple values, so they are truly
          -- symbolic.
          let sym = CB.backendGetSym bak
          let notEq ::
                forall tp.
                ConcRV' sym tp ->
                RM.RegEntry sym tp ->
                IO (Const (W4I.Pred sym) tp)
              notEq (ConcRV' concV) (RM.RegEntry tp v) = do
                symV <- concToSym sym sFns fm tp concV
                p <- W4I.notPred sym =<< RV.eqRegValue sym tp symV v
                pure (Const p)
          let RM.RegMap mAssign = m
          preds <- Ctx.zipWithM notEq concM mAssign
          p <-
            foldlMFC
              (\p (Const p') -> W4I.andPred sym p p')
              (W4I.truePred sym)
              preds

          frm <- CB.pushAssumptionFrame bak
          loc <- W4I.getCurrentProgramLoc sym
          CB.addAssumption bak (CB.GenericAssumption loc "uniquelyConcRegMap" p)
          concM_' <- concRegMap bak iFns m
          res <-
            case concM_' of
              Left W4C.UnsatInitialAssumptions -> pure (Right concM)
              Left e -> pure (Left (W4C.GroundingFailure e))
              Right _ -> pure (Left W4C.MultipleModels)
          _ <- CB.popAssumptionFrame bak frm
          pure res

---------------------------------------------------------------------
-- * 'concToSym'

-- | Function for re-symbolizing an intrinsic type
type IntrinsicConcToSymFn :: Symbol -> Type
newtype IntrinsicConcToSymFn nm
  = IntrinsicConcToSymFn
    (forall sym ctx.
      W4I.IsExprBuilder sym =>
      sym ->
      Ctx.Assignment TypeRepr ctx ->
      ConcIntrinsic nm ctx ->
      IO (RegValue sym (IntrinsicType nm ctx)))

-- | Helper, not exported
concToSymAny ::
  (sym ~ ExprBuilder scope st (Flags fm)) =>
  sym ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  FloatModeRepr fm ->
  ConcRegValue sym AnyType ->
  IO (RegValue sym AnyType)
concToSymAny sym iFns fm (ConcAnyValue tp' (ConcRV' v')) =
  RV.AnyValue tp' <$> concToSym sym iFns fm tp' v'

-- | Helper, not exported
concToSymFn ::
  (sym ~ ExprBuilder scope st (Flags fm)) =>
  sym ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  FloatModeRepr fm ->
  Ctx.Assignment (TypeRepr) as ->
  TypeRepr r ->
  ConcRegValue sym (FunctionHandleType as r) ->
  IO (RegValue sym (FunctionHandleType as r))
concToSymFn sym iFns fm as r f =
  case f of
    ConcClosureFnVal clos vtp (ConcRV' v) -> do
      v' <- concToSym sym iFns fm vtp v
      clos' <- concToSymFn sym iFns fm (as Ctx.:> vtp) r clos
      pure (RV.ClosureFnVal clos' vtp v')

    ConcVarargsFnVal hdl extra ->
      pure (RV.VarargsFnVal hdl extra)

    ConcHandleFnVal hdl ->
      pure (RV.HandleFnVal hdl)

-- | Helper, not exported
concToSymIntrinsic ::
  W4I.IsExprBuilder sym =>
  sym ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  SymbolRepr nm ->
  CtxRepr ctx ->
  ConcRegValue sym (IntrinsicType nm ctx) ->
  IO (RegValue sym (IntrinsicType nm ctx))
concToSymIntrinsic sym iFns nm tyCtx v =
  case MapF.lookup nm iFns of
    Nothing ->
      let strNm = Text.unpack (symbolRepr nm) in
      fail ("Missing concretization function for intrinsic: " ++ strNm)
    Just (IntrinsicConcToSymFn f) -> f sym tyCtx v

-- | Helper, not exported
concToSymMaybe ::
  (sym ~ ExprBuilder scope st (Flags fm)) =>
  sym ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  FloatModeRepr fm ->
  TypeRepr tp ->
  ConcRegValue sym (MaybeType tp) ->
  IO (RegValue sym (MaybeType tp))
concToSymMaybe sym iFns fm tp =
  \case
    Nothing -> pure (W4P.Err ())
    Just v ->
      W4P.justPartExpr sym <$> concToSym sym iFns fm tp v

-- | Helper, not exported
concToSymRef ::
  W4I.IsExprBuilder sym =>
  sym ->
  ConcRegValue sym (ReferenceType tp) ->
  IO (RegValue sym (ReferenceType tp))
concToSymRef sym (v NE.:| _) = pure (MuxTree.toMuxTree sym v)

-- | Helper, not exported
concToSymVariant ::
  forall sym tps scope st fm.
  (sym ~ ExprBuilder scope st (Flags fm)) =>
  sym ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  FloatModeRepr fm ->
  CtxRepr tps ->
  ConcRegValue sym (VariantType tps) ->
  IO (RegValue sym (VariantType tps))
concToSymVariant sym iFns fm tps v = Ctx.zipWithM go tps v
  where
    go :: forall tp. TypeRepr tp -> ConcVariantBranch sym tp -> IO (RV.VariantBranch sym tp)
    go tp (ConcVariantBranch b) =
      case b of
        Nothing -> pure (RV.VB (W4P.Err ()))
        Just (ConcRV' v') ->
          RV.VB . W4P.justPartExpr sym <$> concToSym sym iFns fm tp v'

-- | Inject a 'ConcRegValue' back into a 'RegValue'.
concToSym ::
  (sym ~ ExprBuilder scope st (Flags fm)) =>
  sym ->
  MapF SymbolRepr IntrinsicConcToSymFn ->
  FloatModeRepr fm ->
  TypeRepr tp ->
  ConcRegValue sym tp ->
  IO (RegValue sym tp)
concToSym sym iFns fm tp v =
  case tp of
    -- Base types
    BoolRepr -> W4GE.groundToSym sym BaseBoolRepr v
    BVRepr width -> W4GE.groundToSym sym (BaseBVRepr width) v
    ComplexRealRepr -> W4GE.groundToSym sym BaseComplexRepr v
    FloatRepr fi ->
      case fm of
        FloatIEEERepr ->
          W4I.floatLit sym (floatInfoToPrecisionRepr fi) v
        FloatUninterpretedRepr -> do
          sv <- W4GE.groundToSym sym (floatInfoToBVTypeRepr fi) v
          iFloatFromBinary sym fi sv
        FloatRealRepr ->
          iFloatLitRational sym fi v
    IEEEFloatRepr fpp -> W4GE.groundToSym sym (BaseFloatRepr fpp) v
    IntegerRepr -> W4GE.groundToSym sym BaseIntegerRepr v
    NatRepr -> W4I.integerToNat sym =<< W4GE.groundToSym sym BaseIntegerRepr v
    RealValRepr -> W4GE.groundToSym sym BaseRealRepr v
    StringRepr si -> W4GE.groundToSym sym (BaseStringRepr si) v
    SymbolicArrayRepr idxs tp' -> W4GE.groundToSym sym (BaseArrayRepr idxs tp') v
    SymbolicStructRepr tys -> W4GE.groundToSym sym (BaseStructRepr tys) v

    -- Trivial cases
    UnitRepr -> pure ()
    CharRepr -> pure v

    -- Simple recursive cases
    RecursiveRepr symb tyCtx ->
      RV.RolledType <$> concToSym sym iFns fm (unrollType symb tyCtx) v
    SequenceRepr tp' -> do
      l <- traverse (concToSym sym iFns fm tp' . unConcRV') (F.toList v)
      SymSeq.fromListSymSequence sym l
    StringMapRepr tp' ->
      traverse (fmap (W4P.justPartExpr sym) . concToSym sym iFns fm tp' . unConcRV') v
    StructRepr tps ->
      Ctx.zipWithM (\tp' (ConcRV' v') -> RV.RV <$> concToSym sym iFns fm tp' v') tps v
    VectorRepr tp' ->
      traverse (concToSym sym iFns fm tp' . unConcRV') v

    -- Cases with helper functions
    AnyRepr -> concToSymAny sym iFns fm v
    MaybeRepr tp' -> concToSymMaybe sym iFns fm tp' v
    FunctionHandleRepr args ret -> concToSymFn sym iFns fm args ret v
    IntrinsicRepr nm tyCtx -> concToSymIntrinsic sym iFns nm tyCtx v
    ReferenceRepr _tp' -> concToSymRef sym v
    VariantRepr tps -> concToSymVariant sym iFns fm tps v

    -- Incomplete cases
    WordMapRepr _ _ -> fail "concToSym does not yet support WordMap"
