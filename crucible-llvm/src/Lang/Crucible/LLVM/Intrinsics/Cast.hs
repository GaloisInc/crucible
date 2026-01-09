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
  , ValCastError(..)
  , printValCastError
  , regValuesFromLLVM
  , regValueFromLLVM
  , regValuesFromLLVM'
  , regValueFromLLVM'
  , regEntriesFromLLVM
  , regMapFromLLVM
  ) where

import           Data.Coerce (coerce)
import qualified Data.Text as Text
import           Data.Type.Equality ((:~:)(Refl), testEquality)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TraversableFC as TFC

import qualified What4.FunctionName as WFN

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Simulator.RegMap as CRM
import qualified Lang.Crucible.Simulator.RegValue as CRV
import qualified Lang.Crucible.Simulator.SimError as CSE
import qualified Lang.Crucible.Types as CT

import           Lang.Crucible.LLVM.MemModel.Partial (ptrToBv)
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

  -- recursive cases
  ToLLVMType (CT.VectorType tp) = CT.VectorType (ToLLVMType tp)
  ToLLVMType (CT.StructType ctx) = CT.StructType (CtxToLLVMType ctx)

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

    -- recursive cases
    CT.VectorRepr tp -> CT.VectorRepr (toLLVMType tp)
    CT.StructRepr ctx -> CT.StructRepr (ctxToLLVMType ctx)

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

    -- recursive cases
    CT.VectorRepr elemTy -> traverse (regValueToLLVM sym elemTy) val
    CT.StructRepr fieldTys -> regValuesToLLVM sym fieldTys val

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

data ValCastError
  = -- | Mismatched number of arguments ('castLLVMArgs') or struct fields
    -- ('castLLVMRet').
    MismatchedShape
    -- | Can\'t cast between these types
  | ValCastError (Some CT.TypeRepr) (Some CT.TypeRepr)

-- | Turn a 'ValCastError' into a human-readable message (lines).
printValCastError :: ValCastError -> [String]
printValCastError =
  \case
    MismatchedShape -> ["argument shape mismatch"]
    ValCastError (Some ret) (Some ret') ->
      [ "Cannot cast types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Map 'regValueFromLLVM' over an 'Ctx.Assignment'.
regValuesFromLLVM ::
  CB.IsSymBackend sym bak =>
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys' ->
  Ctx.Assignment CT.TypeRepr tys ->
  Either
    ValCastError
    (bak ->
      Ctx.Assignment (CRV.RegValue' sym) tys ->
      IO (Ctx.Assignment (CRV.RegValue' sym) tys'))
regValuesFromLLVM fNm wanteds tys =
  case (wanteds, tys) of
    (Ctx.Empty, Ctx.Empty) -> Right (\_bak -> pure)
    (Ctx.Empty, _) -> Left MismatchedShape
    (_, Ctx.Empty) -> Left MismatchedShape
    (restWanted Ctx.:> w, restTys Ctx.:> t) -> do
      castRest <- regValuesFromLLVM fNm restWanted restTys
      cast <- regValueFromLLVM fNm w t
      Right $
        \bak ->
          \case
            rest Ctx.:> CRV.RV val -> do
              rest' <- castRest bak rest
              val' <- cast bak val
              pure (rest' Ctx.:> CRV.RV val')

-- | Convert a 'CRV.RegValue' from its corresponding LLVM type (LLVM pointers
-- with bitvectors where wanted).
--
-- If this function returns 'Right', then @ToLLVMType ty' ~ ty@ (though this
-- guarantee is not reflected in the type system).
regValueFromLLVM ::
  forall sym bak ty' ty.
  CB.IsSymBackend sym bak =>
  -- | Only used in error messages
  WFN.FunctionName ->
  CT.TypeRepr ty' ->
  CT.TypeRepr ty ->
  Either
    ValCastError
    (bak -> CRV.RegValue sym ty -> IO (CRV.RegValue sym ty'))
regValueFromLLVM fNm wanted ty = do
  let badCast w t = Left (ValCastError (Some w) (Some t))
  let noop ::
        Either
          ValCastError
          (bak -> CRV.RegValue sym ty -> IO (CRV.RegValue sym ty'))
      noop =
        case testEquality wanted ty of
          Just Refl -> Right (\_bak -> pure)
          Nothing -> badCast wanted ty
  case (wanted, ty) of
    (CT.BVRepr w, Ptr.LLVMPointerRepr w')
      | Just Refl <- testEquality w w' ->
      Right $ \bak val -> do
        let err = 
              CSE.AssertFailureSimError
               "Found a pointer where a bitvector was expected"
               ("In the arguments or return value of "
                ++ Text.unpack (WFN.functionName fNm))
        ptrToBv bak err val
    (CT.BVRepr {}, _) -> badCast wanted ty

    -- no-ops

    (CT.AnyRepr, _) -> noop
    (CT.UnitRepr, _) -> noop
    (CT.BoolRepr, _) -> noop
    (CT.NatRepr, _) -> noop
    (CT.IntegerRepr, _) -> noop
    (CT.RealValRepr, _) -> noop
    (CT.CharRepr, _) -> noop
    (CT.ComplexRealRepr, _) -> noop
    (CT.FloatRepr {}, _) -> noop
    (CT.IEEEFloatRepr {}, _) -> noop
    (CT.StringRepr {}, _) -> noop
    (CT.IntrinsicRepr {}, _) -> noop

    -- recursive cases

    (CT.VectorRepr wantedElemTy, CT.VectorRepr elemTy) -> do
      cast <- regValueFromLLVM fNm wantedElemTy elemTy
      Right (\bak -> (traverse (cast bak)))
    (CT.VectorRepr {}, _) -> badCast wanted ty

    (CT.StructRepr wantedFieldTys, CT.StructRepr fieldTys) ->
      regValuesFromLLVM fNm wantedFieldTys fieldTys
    (CT.StructRepr {}, _) -> badCast wanted ty

    -- these shouldn't appear in override signaures, so don't worry about them

    (CT.FunctionHandleRepr {}, _) -> noop
    (CT.MaybeRepr {}, _) -> noop
    (CT.SequenceRepr {}, _) -> noop
    (CT.RecursiveRepr {}, _) -> noop
    (CT.ReferenceRepr {}, _) -> noop
    (CT.VariantRepr {}, _) -> noop
    (CT.WordMapRepr {}, _) -> noop
    (CT.StringMapRepr {}, _) -> noop
    (CT.SymbolicArrayRepr {}, _) -> noop
    (CT.SymbolicStructRepr {}, _) -> noop

-- | Map 'regValueFromLLVM' over an 'Ctx.Assignment' of 'CRM.RegEntry's.
regEntriesFromLLVM ::
  CB.IsSymBackend sym bak =>
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys' ->
  Ctx.Assignment CT.TypeRepr tys ->
  Either
    ValCastError
    (bak ->
      Ctx.Assignment (CRM.RegEntry sym) tys ->
      IO (Ctx.Assignment (CRM.RegEntry sym) tys'))
regEntriesFromLLVM fNm wanteds tys = do
  cast <- regValuesFromLLVM fNm wanteds tys
  Right $ \bak vals ->
    Ctx.zipWith (\ty (CRV.RV v) -> CRM.RegEntry ty v) wanteds
      <$> cast bak (TFC.fmapFC (\(CRM.RegEntry _ty v) -> CRM.RV v) vals)

-- | Map 'regValueFromLLVM' over a 'CRM.RegMap'.
regMapFromLLVM ::
  forall sym bak tys' tys.
  CB.IsSymBackend sym bak =>
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys' ->
  Ctx.Assignment CT.TypeRepr tys ->
  Either
    ValCastError
    (bak -> CRM.RegMap sym tys -> IO (CRM.RegMap sym tys'))
regMapFromLLVM fNm wanteds tys = do
  cast <- regEntriesFromLLVM fNm wanteds tys
  Right $ \bak -> coerce (cast bak)


-- | Map 'regValueFromLLVM' over an 'Ctx.Assignment'.
regValuesFromLLVM' ::
  CB.IsSymBackend sym bak =>
  -- | Only used in error messages
  WFN.FunctionName ->
  Ctx.Assignment CT.TypeRepr tys ->
  Ctx.Assignment CT.TypeRepr (CtxToLLVMType tys) ->
  bak ->
  Ctx.Assignment (CRV.RegValue' sym) (CtxToLLVMType tys) ->
  IO (Ctx.Assignment (CRV.RegValue' sym) tys)
regValuesFromLLVM' fNm wanteds tys bak vals =
  case (wanteds, tys) of
    (Ctx.Empty, Ctx.Empty) -> pure vals
    (restWanted Ctx.:> w, restTys Ctx.:> t) -> do
      let castRest = regValuesFromLLVM' fNm restWanted restTys bak
      let cast = regValueFromLLVM' fNm w t bak
      case vals of
        rest Ctx.:> CRV.RV val -> do
          rest' <- castRest rest
          val' <- cast val
          pure (rest' Ctx.:> CRV.RV val')

-- | Convert a 'CRV.RegValue' from its corresponding LLVM type (LLVM pointers
-- with bitvectors where wanted).
--
-- If this function returns 'Right', then @ToLLVMType ty' ~ ty@ (though this
-- guarantee is not reflected in the type system).
regValueFromLLVM' ::
  forall sym bak ty.
  CB.IsSymBackend sym bak =>
  -- | Only used in error messages
  WFN.FunctionName ->
  CT.TypeRepr ty ->
  CT.TypeRepr (ToLLVMType ty) ->
  bak ->
  CRV.RegValue sym (ToLLVMType ty) ->
  IO (CRV.RegValue sym ty)
regValueFromLLVM' fNm wanted ty bak val = do
  let badCast w t = Left (ValCastError (Some w) (Some t))
  case (wanted, ty) of
    (CT.BVRepr w, Ptr.LLVMPointerRepr w')
      | Just Refl <- testEquality w w' -> do
        let err = 
              CSE.AssertFailureSimError
               "Found a pointer where a bitvector was expected"
               ("In the arguments or return value of "
                ++ Text.unpack (WFN.functionName fNm))
        ptrToBv bak err val
    (CT.BVRepr {}, _) -> error "TODO"

    -- no-ops

    (CT.AnyRepr, CT.AnyRepr) -> pure val
    (CT.UnitRepr, CT.UnitRepr) ->  pure val
    (CT.BoolRepr, CT.BoolRepr) ->  pure val
    (CT.NatRepr, CT.NatRepr) -> pure val
    (CT.IntegerRepr, CT.IntegerRepr) -> pure val
    (CT.RealValRepr, CT.RealValRepr) -> pure val
    (CT.CharRepr, CT.CharRepr) -> pure val
    (CT.ComplexRealRepr, CT.ComplexRealRepr) -> pure val
    (CT.FloatRepr {}, CT.FloatRepr {}) -> pure val
    (CT.IEEEFloatRepr {}, CT.IEEEFloatRepr {}) -> pure val
    (CT.StringRepr {}, CT.StringRepr {}) -> pure val
    (CT.IntrinsicRepr {}, CT.IntrinsicRepr {}) -> pure val

    -- recursive cases

    (CT.VectorRepr wantedElemTy, CT.VectorRepr elemTy) ->
      traverse (regValueFromLLVM' fNm wantedElemTy elemTy bak) val

    (CT.StructRepr wantedFieldTys, CT.StructRepr fieldTys) ->
      regValuesFromLLVM' fNm wantedFieldTys fieldTys bak val

    -- -- these shouldn't appear in override signaures, so don't worry about them

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
