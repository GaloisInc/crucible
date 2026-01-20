-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Cast
-- Description      : Casting to and from the Crucible-LLVM ABI
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- In Crucible-LLVM, LLVM pointers and integers are translated to terms
-- of type 'Lang.Crucible.LLVM.MemModel.Pointer.LLVMPointerType'. When
-- writing overrides, it can be convenient to take arguments or return
-- values of 'Lang.Crucible.Types.BVType'. This is done frequently in
-- the built-in overrides in "Lang.Crucible.LLVM.Intrinsics.Libc" and
-- "Lang.Crucible.LLVM.Intrinsics.LLVM". This module contains helpers for
-- \"lowering\" signatures using Crucible bitvectors to ones that use LLVM
-- pointers.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Intrinsics.Cast
  ( -- * There
    CtxToLLVMType
  , ToLLVMType
  , ctxToLLVMType
  , toLLVMType
  , regValuesToLLVM
  , regValueToLLVM
    -- * Back again
  , regValuesFromLLVM
  , regValueFromLLVM
  , regEntriesFromLLVM
  , regMapFromLLVM
    -- * Lowering overrides
  , lowerLLVMOverride
  , lowerMakeOverride
  , lowerOverrideTemplate
  ) where

import           Control.Monad.IO.Class (liftIO)
import           Data.Coerce (coerce)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl), testEquality)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as TFC

import qualified What4.FunctionName as WFN

import qualified Lang.Crucible.Backend as CB
import           Lang.Crucible.Panic (panic)
import qualified Lang.Crucible.Simulator.OverrideSim as CSO
import qualified Lang.Crucible.Simulator.RegMap as CRM
import qualified Lang.Crucible.Simulator.RegValue as CRV
import qualified Lang.Crucible.Simulator.SimError as CSE
import qualified Lang.Crucible.Types as CT

import qualified Lang.Crucible.LLVM.Intrinsics.Common as IC
import           Lang.Crucible.LLVM.MemModel.Partial (HasLLVMAnn, ptrToBv)
import           Lang.Crucible.LLVM.MemModel.Pointer (LLVMPointerType)
import qualified Lang.Crucible.LLVM.MemModel.Pointer as Ptr

---------------------------------------------------------------------
-- * There

-- | Convert bitvectors to 'LLVMPointer's.
type CtxToLLVMType :: Ctx.Ctx CT.CrucibleType -> Ctx.Ctx CT.CrucibleType
type family CtxToLLVMType t where
  CtxToLLVMType Ctx.EmptyCtx = Ctx.EmptyCtx
  CtxToLLVMType (ctx Ctx.::> tp) = CtxToLLVMType ctx Ctx.::> ToLLVMType tp

-- | Convert bitvectors to 'LLVMPointer's.
type ToLLVMType :: CT.CrucibleType -> CT.CrucibleType
type family ToLLVMType t where
  ToLLVMType (CT.BVType w) = LLVMPointerType w

  -- recursive cases
  ToLLVMType (CT.VectorType tp) = CT.VectorType (ToLLVMType tp)
  ToLLVMType (CT.StructType ctx) = CT.StructType (CtxToLLVMType ctx)

  -- no-ops
  ToLLVMType CT.AnyType = CT.AnyType
  ToLLVMType CT.UnitType = CT.UnitType
  ToLLVMType CT.BoolType = CT.BoolType
  ToLLVMType CT.NatType = CT.NatType
  ToLLVMType CT.IntegerType = CT.IntegerType
  ToLLVMType CT.RealValType = CT.RealValType
  ToLLVMType (CT.FloatType flt) = CT.FloatType flt
  ToLLVMType (CT.IEEEFloatType ps) = CT.IEEEFloatType ps
  ToLLVMType CT.CharType = CT.CharType
  ToLLVMType (CT.StringType si) = CT.StringType si
  ToLLVMType (CT.ComplexRealType) = CT.ComplexRealType
  ToLLVMType (CT.IntrinsicType nm ctx) = CT.IntrinsicType nm ctx

  -- these shouldn't appear in override signaures, so don't worry about them
  ToLLVMType (CT.FunctionHandleType ctx ret) = CT.FunctionHandleType ctx ret
  ToLLVMType (CT.RecursiveType nm ctx) = CT.RecursiveType nm ctx
  ToLLVMType (CT.MaybeType tp) = CT.MaybeType tp
  ToLLVMType (CT.ReferenceType t) = CT.ReferenceType t
  ToLLVMType (CT.SequenceType tp) = CT.SequenceType tp
  ToLLVMType (CT.VariantType ctx) = CT.VariantType ctx
  ToLLVMType (CT.WordMapType n tp) = CT.WordMapType n tp
  ToLLVMType (CT.StringMapType tp) = CT.StringMapType tp
  ToLLVMType (CT.SymbolicArrayType idx t) = CT.SymbolicArrayType idx t
  ToLLVMType (CT.SymbolicStructType ctx) = CT.SymbolicStructType ctx

-- | Value-level analogue of 'CtxToLLVMType'
ctxToLLVMType ::
  Ctx.Assignment CT.TypeRepr ctx ->
  Ctx.Assignment CT.TypeRepr (CtxToLLVMType ctx)
ctxToLLVMType =
  \case
    Ctx.Empty -> Ctx.empty
    ctx Ctx.:> t -> ctxToLLVMType ctx Ctx.:> toLLVMType t

-- | Value-level analogue of 'ToLLVMType'
toLLVMType ::
  CT.TypeRepr t ->
  CT.TypeRepr (ToLLVMType t)
toLLVMType =
  \case
    CT.BVRepr w -> Ptr.LLVMPointerRepr w

    -- recursive cases
    CT.VectorRepr tp -> CT.VectorRepr (toLLVMType tp)
    CT.StructRepr ctx -> CT.StructRepr (ctxToLLVMType ctx)

    -- no-ops
    CT.AnyRepr -> CT.AnyRepr
    CT.UnitRepr -> CT.UnitRepr
    CT.BoolRepr -> CT.BoolRepr
    CT.NatRepr -> CT.NatRepr
    CT.IntegerRepr -> CT.IntegerRepr
    CT.RealValRepr -> CT.RealValRepr
    CT.FloatRepr flt -> CT.FloatRepr flt
    CT.IEEEFloatRepr ps -> CT.IEEEFloatRepr ps
    CT.CharRepr -> CT.CharRepr
    CT.StringRepr si -> CT.StringRepr si
    CT.ComplexRealRepr -> CT.ComplexRealRepr
    CT.IntrinsicRepr nm ctx -> CT.IntrinsicRepr nm ctx

    -- these shouldn't appear in override signaures, so don't worry about them
    t@CT.FunctionHandleRepr {} -> t
    t@CT.RecursiveRepr {} -> t
    t@CT.MaybeRepr {} -> t
    t@CT.SequenceRepr {} -> t
    t@CT.ReferenceRepr {} -> t
    t@CT.VariantRepr {} -> t
    t@CT.WordMapRepr {} -> t
    t@CT.StringMapRepr {} -> t
    t@CT.SymbolicArrayRepr {} -> t
    t@CT.SymbolicStructRepr {} -> t

-- | 'regValueToLLVM' over an 'Ctx.Assignment'
regValuesToLLVM ::
  CB.IsSymInterface sym =>
  sym ->
  Ctx.Assignment CT.TypeRepr tys ->
  Ctx.Assignment (CRV.RegValue' sym) tys ->
  IO (Ctx.Assignment  (CRV.RegValue' sym) (CtxToLLVMType tys))
regValuesToLLVM sym tys vals =
  case (tys, vals) of
    (Ctx.Empty, Ctx.Empty) -> pure Ctx.empty
    (restTys Ctx.:> ty, restVals Ctx.:> CRV.RV val) -> do
      rest <- regValuesToLLVM sym restTys restVals
      val' <- regValueToLLVM sym ty val
      pure (rest Ctx.:> CRV.RV val')

-- | Convert a 'CRV.RegValue' to its corresponding LLVM type (replacing
-- bitvectors with LLVM pointers).
regValueToLLVM ::
  CB.IsSymInterface sym =>
  sym ->
  CT.TypeRepr ty ->
  CRV.RegValue sym ty ->
  IO (CRV.RegValue sym (ToLLVMType ty))
regValueToLLVM sym ty val =
  case ty of
    CT.BVRepr {} -> Ptr.llvmPointer_bv sym val

    -- recursive cases
    CT.VectorRepr elemTy -> traverse (regValueToLLVM sym elemTy) val
    CT.StructRepr fieldTys -> regValuesToLLVM sym fieldTys val

    -- no-ops
    CT.AnyRepr -> pure val
    CT.UnitRepr -> pure val
    CT.BoolRepr -> pure val
    CT.NatRepr -> pure val
    CT.IntegerRepr -> pure val
    CT.RealValRepr -> pure val
    CT.FloatRepr {} -> pure val
    CT.IEEEFloatRepr {} -> pure val
    CT.CharRepr -> pure val
    CT.StringRepr {} -> pure val
    CT.ComplexRealRepr -> pure val
    CT.IntrinsicRepr {} -> pure val

    -- these shouldn't appear in override signaures, so don't worry about them
    CT.FunctionHandleRepr {} -> pure val
    CT.MaybeRepr {} -> pure val
    CT.SequenceRepr {} -> pure val
    CT.RecursiveRepr {} -> pure val
    CT.ReferenceRepr {} -> pure val
    CT.VariantRepr {} -> pure val
    CT.WordMapRepr {} -> pure val
    CT.StringMapRepr {} -> pure val
    CT.SymbolicArrayRepr {} -> pure val
    CT.SymbolicStructRepr {} -> pure val

---------------------------------------------------------------------
-- * Back again

-- | Map 'regValueFromLLVM' over an 'Ctx.Assignment'.
regValuesFromLLVM ::
  CB.IsSymBackend sym bak =>
  bak ->
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys ->
  Ctx.Assignment CT.TypeRepr (CtxToLLVMType tys) ->
  Ctx.Assignment (CRV.RegValue' sym) (CtxToLLVMType tys) ->
  IO (Ctx.Assignment (CRV.RegValue' sym) tys)
regValuesFromLLVM bak fNm wanteds tys vals =
  case (wanteds, tys) of
    (Ctx.Empty, Ctx.Empty) -> pure vals
    (restWanted Ctx.:> w, restTys Ctx.:> t) -> do
      case vals of
        rest Ctx.:> CRV.RV val -> do
          rest' <- regValuesFromLLVM bak fNm restWanted restTys rest
          val' <- regValueFromLLVM bak fNm w t val
          pure (rest' Ctx.:> CRV.RV val')

-- | Convert a 'CRV.RegValue' from its corresponding LLVM type (replacing LLVM
-- pointers with bitvectors where needed).
regValueFromLLVM ::
  forall sym bak ty.
  CB.IsSymBackend sym bak =>
  bak ->
  -- | Only used in error messages
  WFN.FunctionName ->
  CT.TypeRepr ty ->
  CT.TypeRepr (ToLLVMType ty) ->
  CRV.RegValue sym (ToLLVMType ty) ->
  IO (CRV.RegValue sym ty)
regValueFromLLVM bak fNm wanted ty val = do
  case (wanted, ty) of
    (CT.BVRepr w, Ptr.LLVMPointerRepr w')
      | Just Refl <- testEquality w w' -> do
        let err = 
              CSE.AssertFailureSimError
               "Found a pointer where a bitvector was expected"
               ("In the arguments of "
                ++ Text.unpack (WFN.functionName fNm))
        ptrToBv bak err val
    (CT.BVRepr {}, _) ->
      panic
        "regValueFromLLVM"
        [ "Pointer and bitvector of different sizes related by ToLLVMType!"
        , "This is impossible by the definition of ToLLVMType."
        ]

    -- recursive cases

    (CT.VectorRepr wantedElemTy, CT.VectorRepr elemTy) ->
      traverse (regValueFromLLVM bak fNm wantedElemTy elemTy) val

    (CT.StructRepr wantedFieldTys, CT.StructRepr fieldTys) ->
      regValuesFromLLVM bak fNm wantedFieldTys fieldTys val

    -- no-ops

    (CT.AnyRepr, _) -> pure val
    (CT.UnitRepr, _) ->  pure val
    (CT.BoolRepr, _) ->  pure val
    (CT.NatRepr, _) -> pure val
    (CT.IntegerRepr, _) -> pure val
    (CT.RealValRepr, _) -> pure val
    (CT.CharRepr, _) -> pure val
    (CT.ComplexRealRepr, _) -> pure val
    (CT.FloatRepr {}, _) -> pure val
    (CT.IEEEFloatRepr {}, _) -> pure val
    (CT.StringRepr {}, _) -> pure val
    (CT.IntrinsicRepr {}, _) -> pure val

    -- these shouldn't appear in override signaures, so don't worry about them

    (CT.FunctionHandleRepr {}, _) -> pure val
    (CT.MaybeRepr {}, _) -> pure val
    (CT.SequenceRepr {}, _) -> pure val
    (CT.RecursiveRepr {}, _) -> pure val
    (CT.ReferenceRepr {}, _) -> pure val
    (CT.VariantRepr {}, _) -> pure val
    (CT.WordMapRepr {}, _) -> pure val
    (CT.StringMapRepr {}, _) -> pure val
    (CT.SymbolicArrayRepr {}, _) -> pure val
    (CT.SymbolicStructRepr {}, _) -> pure val

-- | Map 'regValueFromLLVM' over an 'Ctx.Assignment' of 'CRM.RegEntry's.
regEntriesFromLLVM ::
  CB.IsSymBackend sym bak =>
  bak ->
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys ->
  Ctx.Assignment CT.TypeRepr (CtxToLLVMType tys) ->
  Ctx.Assignment (CRM.RegEntry sym) (CtxToLLVMType tys) ->
  IO (Ctx.Assignment (CRM.RegEntry sym) tys)
regEntriesFromLLVM bak fNm wanteds tys vals = do
  let cast = regValuesFromLLVM bak fNm wanteds tys
  Ctx.zipWith (\ty (CRV.RV v) -> CRM.RegEntry ty v) wanteds
    <$> cast (TFC.fmapFC (\(CRM.RegEntry _ty v) -> CRM.RV v) vals)

-- | Map 'regValueFromLLVM' over a 'CRM.RegMap'.
regMapFromLLVM ::
  forall sym bak tys.
  CB.IsSymBackend sym bak =>
  bak ->
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys ->
  Ctx.Assignment CT.TypeRepr (CtxToLLVMType tys) ->
  CRM.RegMap sym (CtxToLLVMType tys) ->
  IO (CRM.RegMap sym tys)
regMapFromLLVM bak fNm wanteds tys =
  coerce (regEntriesFromLLVM bak fNm wanteds tys)

---------------------------------------------------------------------
-- * Lowering overrides

-- | Lower an override to use the Crucible-LLVM ABI.
lowerLLVMOverride ::
  forall p sym ext args ret.
  HasLLVMAnn sym =>
  IC.LLVMOverride p sym ext args ret ->
  IC.LLVMOverride p sym ext (CtxToLLVMType args) (ToLLVMType ret)
lowerLLVMOverride ov =
  IC.LLVMOverride
  { IC.llvmOverride_name = IC.llvmOverride_name ov
  , IC.llvmOverride_args = argTys'
  , IC.llvmOverride_ret = retTy'
  , IC.llvmOverride_def =
    \mvar args ->
      CSO.ovrWithBackend $ \bak -> do
        args' <- liftIO (regEntriesFromLLVM bak fNm argTys argTys' args)
        ret <- IC.llvmOverride_def ov mvar args'
        liftIO (regValueToLLVM (CB.backendGetSym bak) retTy ret)
  }
  where
    argTys = IC.llvmOverride_args ov
    argTys' = ctxToLLVMType argTys
    retTy = IC.llvmOverride_ret ov
    retTy' = toLLVMType retTy

    L.Symbol nm = IC.llvmOverride_name ov
    fNm  = WFN.functionNameFromText (Text.pack nm)

-- | Postcompose 'lowerLLVMOverride' with a 'IC.MakeOverride'
lowerMakeOverride ::
  HasLLVMAnn sym =>
  IC.MakeOverride p sym ext arch ->
  IC.MakeOverride p sym ext arch
lowerMakeOverride (IC.MakeOverride f) =
  IC.MakeOverride $ \decl nm ctx -> do
    IC.SomeLLVMOverride ov <- f decl nm ctx
    Just (IC.SomeLLVMOverride (lowerLLVMOverride ov))

-- | Call 'lowerLLVMOverride' on the override in a 'OverrideTemplate'
lowerOverrideTemplate ::
  HasLLVMAnn sym =>
  IC.OverrideTemplate p sym ext arch ->
  IC.OverrideTemplate p sym ext arch
lowerOverrideTemplate t =
  IC.OverrideTemplate
  { IC.overrideTemplateMatcher = IC.overrideTemplateMatcher t
  , IC.overrideTemplateAction = lowerMakeOverride (IC.overrideTemplateAction t)
  }
