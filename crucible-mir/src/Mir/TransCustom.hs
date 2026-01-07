{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}

module Mir.TransCustom(customOps) where

import Data.Bits (shift)
import qualified Data.BitVector.Sized as BV
import Data.Coerce (coerce)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import qualified Prettyprinter as PP

import Control.Monad
import Control.Lens ((^.), at, use)

import GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.Utils.Endian (Endian(..))
import qualified Data.Parameterized.Vector as PV


-- crucible
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.Syntax as S
import qualified Lang.Crucible.CFG.Reg as R
import Lang.Crucible.Panic


import qualified Mir.DefId as M
import           Mir.DefId (ExplodedDefId)
import           Mir.Mir

import           Mir.Generator hiding (customOps)
import           Mir.Intrinsics
import           Mir.TransTy
import           Mir.Trans


--------------------------------------------------------------------------------------------------------------------------
-- *  Primitives & other custom stuff



customOps :: CustomOpMap
customOps = CustomOpMap customOpDefs cloneShimDef cloneFromShimDef

customOpDefs :: Map ExplodedDefId CustomRHS
customOpDefs = Map.fromList $ [
                           slice_index_usize_get_unchecked
                         , slice_index_range_get_unchecked
                         , slice_index_usize_get_unchecked_mut
                         , slice_index_range_get_unchecked_mut
                         , slice_len
                         , const_slice_len
                         , mut_slice_len

                         -- core::intrinsics
                         , discriminant_value
                         , type_id
                         , needs_drop
                         , mem_swap
                         , add_with_overflow
                         , sub_with_overflow
                         , mul_with_overflow
                         , wrapping_add
                         , wrapping_sub
                         , wrapping_mul
                         , saturating_add
                         , saturating_sub
                         , unchecked_add
                         , unchecked_sub
                         , unchecked_mul
                         , unchecked_div
                         , unchecked_rem
                         , unchecked_shl
                         , unchecked_shr
                         , ctlz
                         , ctlz_nonzero
                         , rotate_left
                         , rotate_right
                         , size_of
                         , size_of_val
                         , min_align_of
                         , intrinsics_assume
                         , assert_inhabited
                         , unlikely
                         , bitreverse
                         , volatile_load
                         , volatile_write
                         , exact_div
                         , intrinsics_offset
                         , intrinsics_arith_offset
                         , intrinsics_ptr_offset_from

                         , mem_transmute
                         , mem_bswap
                         , mem_crucible_identity_transmute
                         , array_from_slice
                         , array_from_ref
                         , slice_from_ref
                         , slice_from_mut

                         , vector_new
                         , vector_replicate
                         , vector_len
                         , vector_push
                         , vector_push_front
                         , vector_pop
                         , vector_pop_front
                         , vector_as_slice
                         , vector_as_mut_slice
                         , vector_concat
                         , vector_split_at
                         , vector_copy_from_slice

                         , array_zeroed
                         , array_lookup
                         , array_update
                         , array_as_slice
                         , array_as_mut_slice

                         , any_new
                         , any_downcast

                         , ptr_offset
                         , ptr_offset_mut
                         , ptr_wrapping_offset
                         , ptr_wrapping_offset_mut
                         , ptr_offset_from
                         , ptr_offset_from_mut
                         , ptr_offset_from_unsigned
                         , sub_ptr
                         , sub_ptr_mut
                         , ptr_compare_usize
                         , is_aligned_and_not_null
                         , ptr_slice_from_raw_parts
                         , ptr_slice_from_raw_parts_mut

                         , ptr_read
                         , ptr_write
                         , ptr_swap
                         , ptr_null
                         , ptr_null_mut
                         , drop_in_place_dyn

                         , intrinsics_copy
                         , intrinsics_copy_nonoverlapping

                         , cell_swap_is_nonoverlapping

                         , exit
                         , abort
                         , panicking_begin_panic
                         , panicking_panic
                         , panicking_panic_fmt
                         , panicking_panicking

                         , allocate
                         , allocate_zeroed
                         , reallocate

                         , maybe_uninit_uninit

                         , non_zero_new

                         , ctpop

                         , integer_from_u8
                         , integer_from_i32
                         , integer_from_u64
                         , integer_as_u8
                         , integer_as_u64
                         , integer_shl
                         , integer_shr
                         , integer_bitand
                         , integer_bitor
                         , integer_add
                         , integer_sub
                         , integer_rem
                         , integer_eq
                         , integer_lt
                         ] ++ bv_funcs ++ atomic_funcs



-----------------------------------------------------------------------------------------------------
-- ** Custom: Exit

exit :: (ExplodedDefId, CustomRHS)
exit = (["std", "process", "exit"], \_ ->
           Just (CustomOpExit $ \_ -> return "process::exit"))

abort :: (ExplodedDefId, CustomRHS)
abort = (["core", "intrinsics", "abort"], \_ ->
            Just (CustomOpExit $ \_ -> return "intrinsics::abort"))

panicking_begin_panic :: (ExplodedDefId, CustomRHS)
panicking_begin_panic = (["std", "panicking", "begin_panic"], \_ -> Just $ CustomOpExit $ \_ -> do
    fn <- expectFnContext
    return $ "panicking::begin_panic, called from " <> M.idText (fn ^. fname)
    )

panicking_panic :: (ExplodedDefId, CustomRHS)
panicking_panic = (["core", "panicking", "panic"], \_ -> Just $ CustomOpExit $ \_ -> do
    fn <- expectFnContext
    return $ "panicking::panic, called from " <> M.idText (fn ^. fname)
    )

panicking_panic_fmt :: (ExplodedDefId, CustomRHS)
panicking_panic_fmt = (["core", "panicking", "panic_fmt"], \_ -> Just $ CustomOpExit $ \_ -> do
    fn <- expectFnContext
    return $ "panicking::panic_fmt, called from " <> M.idText (fn ^. fname)
    )

panicking_panicking :: (ExplodedDefId, CustomRHS)
panicking_panicking = (["std", "panicking", "panicking"], \_ -> Just $ CustomOp $ \_ _ -> do
    return $ MirExp C.BoolRepr $ R.App $ E.BoolLit False)


-----------------------------------------------------------------------------------------------------
-- ** Custom: Vector

-- Methods for crucible::vector::Vector<T> (which has custom representation)

vector_new :: (ExplodedDefId, CustomRHS)
vector_new = ( ["crucible","vector","{impl}", "new"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ -> do
        Some tpr <- tyToReprM t
        return $ MirExp (C.VectorRepr tpr) (R.App $ E.VectorLit tpr V.empty)
    _ -> Nothing

vector_replicate :: (ExplodedDefId, CustomRHS)
vector_replicate = ( ["crucible","vector","{impl}", "replicate"], ) $ \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp tpr eVal, MirExp UsizeRepr eLen] -> do
            let eLenNat = R.App $ usizeToNat eLen
            return $ MirExp (C.VectorRepr tpr) (R.App $ E.VectorReplicate tpr eLenNat eVal)
        _ -> mirFail $ "bad arguments for Vector::replicate: " ++ show ops
    _ -> Nothing

vector_len :: (ExplodedDefId, CustomRHS)
vector_len = ( ["crucible","vector","{impl}", "len"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr eRef] -> do
            Some tpr <- tyToReprM t
            e <- readMirRef (C.VectorRepr tpr) eRef
            return $ MirExp UsizeRepr (R.App $ vectorSizeUsize R.App e)
        _ -> mirFail $ "bad arguments for Vector::len: " ++ show ops
    _ -> Nothing

vector_push :: (ExplodedDefId, CustomRHS)
vector_push = ( ["crucible","vector","{impl}", "push"], ) $ \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec, MirExp tpr' eItem]
          | Just Refl <- testEquality tpr tpr' -> do
            eSnoc <- vectorSnoc tpr eVec eItem
            return $ MirExp (C.VectorRepr tpr) eSnoc
        _ -> mirFail $ "bad arguments for Vector::push: " ++ show ops
    _ -> Nothing

vector_push_front :: (ExplodedDefId, CustomRHS)
vector_push_front = ( ["crucible","vector","{impl}", "push_front"], ) $ \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec, MirExp tpr' eItem]
          | Just Refl <- testEquality tpr tpr' -> do
            let eSnoc = R.App $ E.VectorCons tpr eItem eVec
            return $ MirExp (C.VectorRepr tpr) eSnoc
        _ -> mirFail $ "bad arguments for Vector::push_front: " ++ show ops
    _ -> Nothing

vector_pop :: (ExplodedDefId, CustomRHS)
vector_pop = ( ["crucible","vector","{impl}", "pop"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec] -> do
            meInit <- MirExp (C.VectorRepr tpr) <$> vectorInit tpr eVec
            -- `Option<T>` must exist because it appears in the return type.
            meLast <- vectorLast tpr eVec >>= maybeToOption t tpr
            vectorTy <- findExplodedAdtTy vectorExplodedDefId (Substs [t])
            optionTy <- findExplodedAdtTy optionExplodedDefId (Substs [t])
            buildTupleMaybeM [vectorTy, optionTy] [Just meInit, Just meLast]
        _ -> mirFail $ "bad arguments for Vector::pop: " ++ show ops
    _ -> Nothing

vector_pop_front :: (ExplodedDefId, CustomRHS)
vector_pop_front = ( ["crucible","vector","{impl}", "pop_front"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec] -> do
            -- `Option<T>` must exist because it appears in the return type.
            meHead <- vectorHead tpr eVec >>= maybeToOption t tpr
            meTail <- MirExp (C.VectorRepr tpr) <$> vectorTail tpr eVec
            optionTy <- findExplodedAdtTy optionExplodedDefId (Substs [t])
            vectorTy <- findExplodedAdtTy vectorExplodedDefId (Substs [t])
            buildTupleMaybeM [optionTy, vectorTy] [Just meHead, Just meTail]
        _ -> mirFail $ "bad arguments for Vector::pop_front: " ++ show ops
    _ -> Nothing

vector_as_slice_impl :: CustomRHS
vector_as_slice_impl (Substs [t]) =
    Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr e] -> do
            Some tpr <- tyToReprM t
            -- This is similar to `&mut [T; n] -> &mut [T]` unsizing.
            v <- readMirRef (C.VectorRepr tpr) e
            let end = R.App $ vectorSizeUsize R.App v
            e' <- subindexRef tpr e (R.App $ usizeLit 0)
            let tup = S.mkStruct
                    (Ctx.Empty Ctx.:> MirReferenceRepr Ctx.:> knownRepr)
                    (Ctx.Empty Ctx.:> e' Ctx.:> end)
            return $ MirExp MirSliceRepr tup
        _ -> mirFail $ "bad arguments for Vector::as_slice: " ++ show ops
vector_as_slice_impl _ = Nothing

-- `&Vector<T>` and `&[T]` use the same representations as `&mut Vector<T>` and
-- `&mut [T]`, so we can use the same implementation.
vector_as_slice :: (ExplodedDefId, CustomRHS)
vector_as_slice = ( ["crucible","vector","{impl}", "as_slice"], vector_as_slice_impl )

vector_as_mut_slice :: (ExplodedDefId, CustomRHS)
vector_as_mut_slice = ( ["crucible","vector","{impl}", "as_mut_slice"], vector_as_slice_impl )

vector_concat :: (ExplodedDefId, CustomRHS)
vector_concat = ( ["crucible","vector","{impl}", "concat"], ) $ \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr1) e1, MirExp (C.VectorRepr tpr2) e2]
          | Just Refl <- testEquality tpr1 tpr2 -> do
            MirExp (C.VectorRepr tpr1) <$> vectorConcat tpr1 e1 e2
        _ -> mirFail $ "bad arguments for Vector::concat: " ++ show ops
    _ -> Nothing

vector_split_at :: (ExplodedDefId, CustomRHS)
vector_split_at = ( ["crucible","vector","{impl}", "split_at"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec, MirExp UsizeRepr eIdx] -> do
            let eIdxNat = R.App $ usizeToNat eIdx
            mePre <- MirExp (C.VectorRepr tpr) <$> vectorTake tpr eVec eIdxNat
            meSuf <- MirExp (C.VectorRepr tpr) <$> vectorDrop tpr eVec eIdxNat
            vectorTy <- findExplodedAdtTy vectorExplodedDefId (Substs [t])
            buildTupleMaybeM [vectorTy, vectorTy] [Just mePre, Just meSuf]
        _ -> mirFail $ "bad arguments for Vector::split_at: " ++ show ops
    _ -> Nothing

vector_copy_from_slice :: (ExplodedDefId, CustomRHS)
vector_copy_from_slice = ( ["crucible","vector","{impl}", "copy_from_slice"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirSliceRepr e] -> do
            Some tpr <- tyToReprM t
            let ptr = getSlicePtr e
            let len = getSliceLen e
            v <- vectorCopy tpr ptr len
            return $ MirExp (C.VectorRepr tpr) v
        _ -> mirFail $ "bad arguments for Vector::copy_from_slice: " ++ show ops
    _ -> Nothing


-----------------------------------------------------------------------------------------------------
-- ** Custom: Array

-- Methods for crucible::array::Array<T> (which has custom representation)

array_zeroed :: (ExplodedDefId, CustomRHS)
array_zeroed = ( ["crucible","array","{impl}", "zeroed"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ -> tyToReprM t >>= \(Some tpr) -> case tpr of
        C.BVRepr w -> do
            let idxs = Ctx.Empty Ctx.:> BaseUsizeRepr
            v <- arrayZeroed idxs w
            return $ MirExp (C.SymbolicArrayRepr idxs (C.BaseBVRepr w)) v
        _ -> mirFail $ "bad substs for Array::zeroed: " ++ show t
    _ -> Nothing

array_lookup :: (ExplodedDefId, CustomRHS)
array_lookup = ( ["crucible","array","{impl}", "lookup"], ) $ \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [ MirExp (UsizeArrayRepr btr) eArr,
          MirExp UsizeRepr eIdx ] -> do
            let idx = E.BaseTerm BaseUsizeRepr eIdx
            let idxs = Ctx.Empty Ctx.:> idx
            return $ MirExp (C.baseToType btr) (R.App $ E.SymArrayLookup btr eArr idxs)
        _ -> mirFail $ "bad arguments for Array::lookup: " ++ show ops
    _ -> Nothing

array_update :: (ExplodedDefId, CustomRHS)
array_update = ( ["crucible","array","{impl}", "update"], ) $ \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [ MirExp arrTpr@(UsizeArrayRepr btr) eArr,
          MirExp UsizeRepr eIdx,
          MirExp (C.asBaseType -> C.AsBaseType btr') eVal ]
          | Just Refl <- testEquality btr btr' -> do
            let idx = E.BaseTerm BaseUsizeRepr eIdx
            let idxs = Ctx.Empty Ctx.:> idx
            return $ MirExp arrTpr (R.App $ E.SymArrayUpdate btr eArr idxs eVal)
        _ -> mirFail $ "bad arguments for Array::lookup: " ++ show ops
    _ -> Nothing

array_as_slice_impl :: CustomRHS
array_as_slice_impl (Substs [t]) =
    Just $ CustomOp $ \_ ops -> case ops of
        [ MirExp MirReferenceRepr e,
          MirExp UsizeRepr start,
          MirExp UsizeRepr len ] -> do
            Some tpr <- tyToReprM t
            ptr <- subindexRef tpr e start
            return $ MirExp MirSliceRepr $ mkSlice ptr len
        _ -> mirFail $ "bad arguments for Array::as_slice: " ++ show ops
array_as_slice_impl _ = Nothing

array_as_slice :: (ExplodedDefId, CustomRHS)
array_as_slice = ( ["crucible","array","{impl}", "as_slice"], array_as_slice_impl )

array_as_mut_slice :: (ExplodedDefId, CustomRHS)
array_as_mut_slice = ( ["crucible","array","{impl}", "as_mut_slice"], array_as_slice_impl )



-----------------------------------------------------------------------------------------------------
-- ** Custom: Any

-- Methods for crucible::any::Any (which has custom representation)

any_new :: (ExplodedDefId, CustomRHS)
any_new = ( ["core", "crucible", "any", "{impl}", "new"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp tpr e] -> do
            return $ MirExp C.AnyRepr $ R.App $ E.PackAny tpr e
        _ -> mirFail $ "bad arguments for Any::new: " ++ show ops
    _ -> Nothing
    )

any_downcast :: (ExplodedDefId, CustomRHS)
any_downcast = ( ["core", "crucible", "any", "{impl}", "downcast"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp C.AnyRepr e] -> do
            Some tpr <- tyToReprM t
            let maybeVal = R.App $ E.UnpackAny tpr e
            let errMsg = R.App $ E.StringLit $ fromString $
                    "failed to downcast Any as " ++ show tpr
            let val = R.App $ E.FromJustValue tpr maybeVal errMsg
            return $ MirExp tpr val
        _ -> mirFail $ "bad arguments for Any::downcast: " ++ show ops
    _ -> Nothing
    )


-----------------------------------------------------------------------------------------------------
-- ** Custom: ptr

ptr_offset_impl :: CustomRHS
ptr_offset_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ref, MirExp IsizeRepr offset] ->
            MirExp MirReferenceRepr <$> mirRef_offset ref offset
        _ -> mirFail $ "bad arguments for ptr::offset: " ++ show ops
    _ -> Nothing

ptr_offset :: (ExplodedDefId, CustomRHS)
ptr_offset = (["core", "ptr", "const_ptr", "{impl}", "offset"], ptr_offset_impl)
ptr_offset_mut :: (ExplodedDefId, CustomRHS)
ptr_offset_mut = (["core", "ptr", "mut_ptr", "{impl}", "offset"], ptr_offset_impl)

ptr_wrapping_offset_impl :: CustomRHS
ptr_wrapping_offset_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ref, MirExp IsizeRepr offset] ->
            MirExp MirReferenceRepr <$> mirRef_offsetWrap ref offset
        _ -> mirFail $ "bad arguments for ptr::wrapping_offset: " ++ show ops
    _ -> Nothing

ptr_wrapping_offset :: (ExplodedDefId, CustomRHS)
ptr_wrapping_offset =
    (["core", "ptr", "const_ptr", "{impl}", "wrapping_offset"], ptr_wrapping_offset_impl)
ptr_wrapping_offset_mut :: (ExplodedDefId, CustomRHS)
ptr_wrapping_offset_mut =
    (["core", "ptr", "mut_ptr", "{impl}", "wrapping_offset"], ptr_wrapping_offset_impl)

ptr_offset_from_impl :: CustomRHS
ptr_offset_from_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ref1, MirExp MirReferenceRepr ref2] -> do
            maybeOffset <- mirRef_tryOffsetFrom ref1 ref2
            let errMsg = R.App $ E.StringLit $ fromString $
                    "tried to subtract pointers into different arrays"
            let val = R.App $ E.FromJustValue IsizeRepr maybeOffset errMsg
            return $ MirExp IsizeRepr val
        _ -> mirFail $ "bad arguments for ptr::offset_from: " ++ show ops
    _ -> Nothing

ptr_offset_from :: (ExplodedDefId, CustomRHS)
ptr_offset_from = (["core", "ptr", "const_ptr", "{impl}", "offset_from"], ptr_offset_from_impl)
ptr_offset_from_mut :: (ExplodedDefId, CustomRHS)
ptr_offset_from_mut = (["core", "ptr", "mut_ptr", "{impl}", "offset_from"], ptr_offset_from_impl)

ptr_offset_from_unsigned_impl :: CustomRHS
ptr_offset_from_unsigned_impl = \substs -> case substs of
  Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp MirReferenceRepr ref1, MirExp MirReferenceRepr ref2] -> do
      maybeOffset <- mirRef_tryOffsetFrom ref1 ref2
      let errMsg = R.App $ E.StringLit $ fromString $
            "ptr_offset_from_unsigned: pointers not in same allocation"
      let signedOffset = R.App $ E.FromJustValue IsizeRepr maybeOffset errMsg
      let zeroIsize = R.App $ E.BVLit (knownNat @SizeBits) (BV.mkBV (knownNat @SizeBits) 0)
      let isNeg = R.App $ E.BVSlt (knownNat @SizeBits) signedOffset zeroIsize
      G.assertExpr (R.App $ E.Not isNeg) $
        S.litExpr "ptr_offset_from_unsigned: negative offset"
      -- just reinterpret as unsigned:
      let unsignedOffset = signedOffset
      return $ MirExp UsizeRepr unsignedOffset
    _ -> mirFail $ "bad arguments for ptr_offset_from_unsigned: " ++ show ops
  _ -> Nothing

ptr_offset_from_unsigned :: (ExplodedDefId, CustomRHS)
ptr_offset_from_unsigned =
  ( ["core", "intrinsics", "ptr_offset_from_unsigned"]
  , ptr_offset_from_unsigned_impl
  )

sub_ptr :: (ExplodedDefId, CustomRHS)
sub_ptr = (["core", "ptr", "const_ptr", "{impl}", "sub_ptr"], ptr_offset_from_impl)
sub_ptr_mut :: (ExplodedDefId, CustomRHS)
sub_ptr_mut = (["core", "ptr", "mut_ptr", "{impl}", "sub_ptr"], ptr_offset_from_impl)

ptr_compare_usize :: (ExplodedDefId, CustomRHS)
ptr_compare_usize = (["core", "crucible", "ptr", "compare_usize"],
    \substs -> case substs of
        Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
            [MirExp MirReferenceRepr ptr, MirExp UsizeRepr val] -> do
                valAsPtr <- integerToMirRef val
                MirExp C.BoolRepr <$> mirRef_eq ptr valAsPtr
            [MirExp MirSliceRepr slice, MirExp UsizeRepr val] -> do
                let ptr = getSlicePtr slice
                valAsPtr <- integerToMirRef val
                MirExp C.BoolRepr <$> mirRef_eq ptr valAsPtr
            [MirExp DynRefRepr dynRef, MirExp UsizeRepr val] -> do
                let ptr = S.getStruct dynRefDataIndex dynRef
                valAsPtr <- integerToMirRef val
                MirExp C.BoolRepr <$> mirRef_eq ptr valAsPtr
            _ -> mirFail $ "bad arguments for ptr::compare_usize: " ++ show ops
        _ -> Nothing)

is_aligned_and_not_null :: (ExplodedDefId, CustomRHS)
is_aligned_and_not_null = (["core", "intrinsics", "is_aligned_and_not_null"],
    -- TODO (layout): correct behavior is to return `True` for all valid
    -- references, and check `i != 0 && i % align_of::<T>() == 0` for
    -- `MirReference_Integer i`.  However, `align_of` is not implementable
    -- until we start gathering layout information from mir-json.
    \_substs -> Just $ CustomOp $ \_ _ -> return $ MirExp C.BoolRepr $ R.App $ E.BoolLit True)

ptr_slice_from_raw_parts_impl :: CustomRHS
ptr_slice_from_raw_parts_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ptr, MirExp UsizeRepr len] ->
            return $ MirExp MirSliceRepr (mkSlice ptr len)
        _ -> mirFail $ "bad arguments for ptr::slice_from_raw_parts: " ++ show ops
    _ -> Nothing

ptr_slice_from_raw_parts :: (ExplodedDefId, CustomRHS)
ptr_slice_from_raw_parts =
    ( ["core", "ptr", "slice_from_raw_parts", "crucible_slice_from_raw_parts_hook"]
    , ptr_slice_from_raw_parts_impl)
ptr_slice_from_raw_parts_mut :: (ExplodedDefId, CustomRHS)
ptr_slice_from_raw_parts_mut =
    ( ["core", "ptr", "slice_from_raw_parts_mut", "crucible_slice_from_raw_parts_hook"]
    , ptr_slice_from_raw_parts_impl)

-- | [@@std::ptr::read](https://doc.rust-lang.org/std/ptr/fn.read.html)
ptr_read :: (ExplodedDefId, CustomRHS)
ptr_read = (["core", "ptr", "read"], ptr_read_impl "ptr::write")

-- | [@@std::ptr::write](https://doc.rust-lang.org/std/ptr/fn.write.html)
ptr_write :: (ExplodedDefId, CustomRHS)
ptr_write = (["core", "ptr", "write"], ptr_write_impl "ptr::write")

-- | [@std::ptr::read_volatile@](https://doc.rust-lang.org/std/ptr/fn.read_volatile.html)
volatile_load :: (ExplodedDefId, CustomRHS)
volatile_load = (["core", "intrinsics", "volatile_load"], ptr_read_impl "intrinsics::volatile_load")

-- | [@std::ptr::write_volatile@](https://doc.rust-lang.org/std/ptr/fn.write_volatile.html)
volatile_write :: (ExplodedDefId, CustomRHS)
volatile_write = (["core", "intrinsics", "volatile_store"], ptr_write_impl "intrinsics::volatile_write")

ptr_read_impl :: String -> CustomRHS
ptr_read_impl what substs =
  case substs of
    Substs [ty] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ptr] -> do
            Some tpr <- tyToReprM ty
            MirExp tpr <$> readMirRef tpr ptr
        _ -> mirFail $ "bad arguments for " ++ what ++ ": " ++ show ops
    _ -> Nothing

ptr_write_impl :: String -> CustomRHS
ptr_write_impl what substs =
  case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ptr, MirExp tpr val] -> do
            writeMirRef tpr ptr val
            MirExp MirAggregateRepr <$> mirAggregate_zst
        _ -> mirFail $ "bad arguments for " ++ what ++ ": " ++ show ops
    _ -> Nothing

ptr_swap :: (ExplodedDefId, CustomRHS)
ptr_swap = ( ["core", "ptr", "swap"], \substs -> case substs of
    Substs [ty] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr ptr1, MirExp MirReferenceRepr ptr2] -> do
            Some tpr <- tyToReprM ty
            x1 <- readMirRef tpr ptr1
            x2 <- readMirRef tpr ptr2
            writeMirRef tpr ptr1 x2
            writeMirRef tpr ptr2 x1
            MirExp MirAggregateRepr <$> mirAggregate_zst
        _ -> mirFail $ "bad arguments for ptr::swap: " ++ show ops
    _ -> Nothing)

ptr_null :: (ExplodedDefId, CustomRHS)
ptr_null = ( ["core", "ptr", "null", "crucible_null_hook"]
           , null_ptr_impl "ptr::null" )

ptr_null_mut :: (ExplodedDefId, CustomRHS)
ptr_null_mut = ( ["core", "ptr", "null_mut", "crucible_null_hook"]
               , null_ptr_impl "ptr::null_mut" )

null_ptr_impl :: String -> CustomRHS
null_ptr_impl what substs = case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [] -> do
            ref <- integerToMirRef $ R.App $ eBVLit knownNat 0
            return $ MirExp MirReferenceRepr ref
        _  -> mirFail $ "expected no arguments for " ++ what ++ ", received: " ++ show ops
    _ -> Nothing

-- | Experimentally, we've observed that rustc seems not to generate proper drop
-- glue for @&dyn Trait@ drops. We get around this by overriding
-- @core::ptr::drop_in_place@ (when instantiated at @dyn@ types) to fetch the
-- appropriate drop method from the trait object's vtable. @mir-json@ will have
-- included this method.
--
-- For versions of @drop_in_place@ instantiated at other types, this override
-- will not apply, and we will defer to the rustc-provided implementation.
drop_in_place_dyn :: (ExplodedDefId, CustomRHS)
drop_in_place_dyn =
    ( ["core", "ptr", "drop_in_place"],
      \case
        Substs [TyDynamic traitName'] ->
            Just $ CustomOp $ \_argTys args -> case args of
              [MirExp selfTy selfExpr] -> do
                col <- use $ cs . collection
                let argTys = Ctx.empty
                let argExprs = Ctx.empty
                let retTy = MirAggregateRepr

                -- We expect `mir-json` to have placed this trait object's drop
                -- method at index 0, unless the trait object lacks a principal
                -- trait (e.g. `dyn Send`). (This caveat for traits like `Send`
                -- is a bug/limitation of `mir-json` - it _should_ emit a vtable
                -- with a drop method for their trait objects, but that requires
                -- some implementation effort we haven't yet spent, so it
                -- currently does not.) Check here whether the trait has any
                -- methods, to emit a more relevant error message than
                -- `doVirtCall` would emit on its own.
                let dropMethodIndex = 0
                () <- case col ^. traits . at traitName' of
                    Nothing -> mirFail $ "undefined trait: " <> show traitName'
                    Just trait ->
                        case trait ^. traitItems of
                            [] -> mirFail $ "no drop method available in trait " <> show traitName'
                            (_:_) -> pure ()

                callExpr <-
                    doVirtCall
                        col
                        traitName'
                        dropMethodIndex
                        selfTy
                        selfExpr
                        argTys
                        argExprs
                        retTy
                pure (MirExp retTy callExpr)
              _ -> mirFail $ "bad arguments for core::ptr::drop_in_place: " ++ show args
        Substs [_] ->
            -- We weren't provided a `dyn`/`TyDynamic`, so we don't provide an
            -- override, we just defer to the rustc-provided implementation.
            Nothing
        Substs ss ->
            Just $ CustomOp $ \_ _ -> mirFail $ unwords
                [ "expected one subst for `core::ptr::drop_in_place`, saw"
                , show (length ss) <> ":"
                , show ss ]
    )

intrinsics_copy :: (ExplodedDefId, CustomRHS)
intrinsics_copy = ( ["core", "intrinsics", "copy"], \substs -> case substs of
    Substs [ty] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp MirReferenceRepr src,
         MirExp MirReferenceRepr dest,
         MirExp UsizeRepr count] -> do
            Some tpr <- tyToReprM ty
            -- `copy` (as opposed to `copy_nonoverlapping`) must work
            -- atomically even when the source and dest overlap.  We do this by
            -- taking a snapshot of the source, then copying the snapshot into
            -- dest.
            --
            -- TODO: check for overlap and copy in reverse order if needed.
            -- This will let us avoid the temporary `constMirRef`.
            (srcAg, srcIdx) <- mirRef_peelIndex src
            srcSnapAg <- readMirRef MirAggregateRepr srcAg
            srcSnapRoot <- constMirRef MirAggregateRepr srcSnapAg
            srcSnap <- subindexRef tpr srcSnapRoot srcIdx

            ptrCopy tpr srcSnap dest count
            MirExp MirAggregateRepr <$> mirAggregate_zst

        _ -> mirFail $ "bad arguments for intrinsics::copy: " ++ show ops
    _ -> Nothing)

intrinsics_copy_nonoverlapping :: (ExplodedDefId, CustomRHS)
intrinsics_copy_nonoverlapping = ( ["core", "intrinsics", "copy_nonoverlapping"],
    \substs -> case substs of
        Substs [ty] -> Just $ CustomOp $ \_ ops -> case ops of
            [MirExp MirReferenceRepr src,
             MirExp MirReferenceRepr dest,
             MirExp UsizeRepr count] -> do
                Some tpr <- tyToReprM ty
                copyNonOverlapping tpr src dest count

            _ -> mirFail $ "bad arguments for intrinsics::copy_nonoverlapping: " ++ show ops
        _ -> Nothing)

cell_swap_is_nonoverlapping :: (ExplodedDefId, CustomRHS)
cell_swap_is_nonoverlapping =
    ( ["core", "cell", "{impl}", "swap", "crucible_cell_swap_is_nonoverlapping_hook"]
    , \case
        Substs [ty] -> Just $ CustomOp $ \_ ops -> case ops of
            [MirExp MirReferenceRepr src,
             MirExp MirReferenceRepr dest] -> do
                size <- getLayoutFieldAsExpr "crucible_cell_swap_is_nonoverlapping_hook" laySize ty
                MirExp C.BoolRepr <$> isNonOverlapping src dest size
            _ -> mirFail $
                "bad arguments for Cell::swap::crucible_cell_swap_is_nonoverlapping_hook: "
                ++ show ops
        _ -> Nothing
    )

-----------------------------------------------------------------------------------------------------
-- ** Custom: wrapping_mul


-- Note the naming: `overflowing` means `T -> T -> T`, with the output wrapped
-- mod 2^N.  `with_overflow` means `T -> T -> (T, Bool)`, returning both the
-- wrapped output and an overflow flag.

makeOverflowingArith :: String -> BinOp -> CustomRHS
makeOverflowingArith name bop =
    \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
        ([TyUint _, TyUint _], [e1, e2]) ->
            fst <$> evalBinOp bop (Just Unsigned) e1 e2
        ([TyInt _, TyInt _], [e1, e2]) ->
            fst <$> evalBinOp bop (Just Signed) e1 e2
        _ -> mirFail $ "bad arguments to " ++ name ++ ": " ++ show (opTys, ops)

wrapping_add ::  (ExplodedDefId, CustomRHS)
wrapping_add =
    ( ["core","intrinsics", "wrapping_add"]
    , makeOverflowingArith "wrapping_add" Add
    )

wrapping_sub ::  (ExplodedDefId, CustomRHS)
wrapping_sub =
    ( ["core","intrinsics", "wrapping_sub"]
    , makeOverflowingArith "wrapping_sub" Sub
    )

wrapping_mul ::  (ExplodedDefId, CustomRHS)
wrapping_mul =
    ( ["core","intrinsics", "wrapping_mul"]
    , makeOverflowingArith "wrapping_mul" Mul
    )


overflowResult ::
    Ty ->
    C.TypeRepr tp ->
    R.Expr MIR s tp ->
    R.Expr MIR s C.BoolType ->
    MirGenerator h s ret (MirExp s)
overflowResult valTy tpr value over =
  buildTupleM [valTy, TyBool] [MirExp tpr value, MirExp C.BoolRepr over]

makeArithWithOverflow :: String -> Maybe Bool -> BinOp -> CustomRHS
makeArithWithOverflow name isSignedOverride bop = \substs ->
  case substs of
    Substs [t] -> Just $ CustomOp $ \_opTys ops -> case ops of
        [e1, e2] -> do
            let arithType' = fmap (\s -> if s then Signed else Unsigned) $ isSigned t
            (result, overflow) <- evalBinOp bop arithType' e1 e2
            case result of
                MirExp (C.BVRepr w) result' ->
                    overflowResult t (C.BVRepr w) result' overflow
                MirExp tpr _ -> mirFail $
                    "bad return values from evalBinOp " ++ show bop ++ ": " ++ show tpr
        _ -> mirFail $ "bad arguments to " ++ name ++ ": " ++ show (t, ops)
    _ -> Nothing
  where
    isSigned _ | Just s <- isSignedOverride = Just s
    isSigned (TyInt _) = Just True
    isSigned (TyUint _) = Just False
    -- Includes `Bv<_>` support so that `makeArithWithOverflow` can also be
    -- used to implement `Bv::overflowing_add` etc.
    isSigned (CTyBv _) = Just False
    isSigned _ = Nothing

add_with_overflow ::  (ExplodedDefId, CustomRHS)
add_with_overflow =
    ( ["core","intrinsics", "add_with_overflow"]
    , makeArithWithOverflow "add_with_overflow" Nothing Add
    )

sub_with_overflow ::  (ExplodedDefId, CustomRHS)
sub_with_overflow =
    ( ["core","intrinsics", "sub_with_overflow"]
    , makeArithWithOverflow "sub_with_overflow" Nothing Sub
    )

mul_with_overflow ::  (ExplodedDefId, CustomRHS)
mul_with_overflow =
    ( ["core","intrinsics", "mul_with_overflow"]
    , makeArithWithOverflow "mul_with_overflow" Nothing Mul
    )


saturatingResultBV :: (1 <= w) => NatRepr w ->
    R.Expr MIR s (C.BVType w) ->
    R.Expr MIR s (C.BVType w) ->
    R.Expr MIR s C.BoolType ->
    MirGenerator h s ret (MirExp s)
saturatingResultBV w satValue value over = return $ MirExp (C.BVRepr w) $
    R.App $ E.BVIte over w satValue value

saturateValueUnsigned :: (1 <= w) => NatRepr w -> BinOp -> Maybe (R.Expr MIR s (C.BVType w))
saturateValueUnsigned w Add = Just $ R.App $ eBVLit w (shift 1 (fromInteger $ C.intValue w) - 1)
saturateValueUnsigned w Sub = Just $ R.App $ eBVLit w 0
saturateValueUnsigned w Mul = Just $ R.App $ eBVLit w (shift 1 (fromInteger $ C.intValue w) - 1)
saturateValueUnsigned _ _ = Nothing

saturateValueSigned :: (1 <= w) => NatRepr w -> BinOp -> R.Expr MIR s C.BoolType -> Maybe (R.Expr MIR s (C.BVType w))
saturateValueSigned w op pos = case op of
    Add -> Just $ R.App $ E.BVIte pos w maxVal minVal
    Sub -> Just $ R.App $ E.BVIte pos w minVal maxVal
    _ -> Nothing
  where
    bits = fromIntegral $ C.intValue w
    maxVal = R.App $ eBVLit w ((1 `shift` (bits - 1)) - 1)
    minVal = R.App $ eBVLit w (negate $ 1 `shift` (bits - 1))

makeSaturatingArith :: String -> BinOp -> CustomRHS
makeSaturatingArith name bop =
    \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
        ([TyUint _, TyUint _], [e1, e2]) -> do
            (result, overflow) <- evalBinOp bop (Just Unsigned) e1 e2
            case result of
                MirExp (C.BVRepr w) result' -> do
                    satValue <- case saturateValueUnsigned w bop of
                        Just x -> return x
                        Nothing -> mirFail $ "not yet implemented: unsigned saturating " ++ show bop
                    saturatingResultBV w satValue result' overflow
                MirExp tpr _ -> mirFail $
                    "bad return values from evalBinOp " ++ show bop ++ ": " ++ show tpr
        ([TyInt _, TyInt _], [e1, e2]) -> do
            (result, overflow) <- evalBinOp bop (Just Signed) e1 e2
            pos <- isPos e2
            case result of
                MirExp (C.BVRepr w) result' -> do
                    satValue <- case saturateValueSigned w bop pos of
                        Just x -> return x
                        Nothing -> mirFail $ "not yet implemented: signed saturating " ++ show bop
                    saturatingResultBV w satValue result' overflow
                MirExp tpr _ -> mirFail $
                    "bad return values from evalBinOp " ++ show bop ++ ": " ++ show tpr
        _ -> mirFail $ "bad arguments to " ++ name ++ ": " ++ show (opTys, ops)
  where
    isPos :: MirExp s -> MirGenerator h s ret (R.Expr MIR s C.BoolType)
    isPos (MirExp (C.BVRepr w) e) = return $ R.App $ E.BVSle w (R.App $ eBVLit w 0) e
    isPos (MirExp tpr _) = mirFail $ name ++ ": expected BVRepr, but got " ++ show tpr


saturating_add ::  (ExplodedDefId, CustomRHS)
saturating_add =
    ( ["core","intrinsics", "saturating_add"]
    , makeSaturatingArith "saturating_add" Add
    )

saturating_sub ::  (ExplodedDefId, CustomRHS)
saturating_sub =
    ( ["core","intrinsics", "saturating_sub"]
    , makeSaturatingArith "saturating_sub" Sub
    )


-- | Common implementation for `unchecked_add` and related intrinsics.  These
-- all perform the normal arithmetic operation, but overflow is undefined
-- behavior.
makeUncheckedArith :: String -> BinOp -> CustomRHS
makeUncheckedArith name bop =
    \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
        ([TyUint _, TyUint _], [e1, e2]) -> do
            (result, overflow) <- evalBinOp bop (Just Unsigned) e1 e2
            G.assertExpr (R.App $ E.Not overflow) $
                S.litExpr $ Text.pack $ "undefined behavior: " ++ name ++ " overflowed"
            return result
        ([TyInt _, TyInt _], [e1, e2]) -> do
            (result, overflow) <- evalBinOp bop (Just Signed) e1 e2
            G.assertExpr (R.App $ E.Not overflow) $
                S.litExpr $ Text.pack $ "undefined behavior: " ++ name ++ " overflowed"
            return result
        _ -> mirFail $ "bad arguments to " ++ name ++ ": " ++ show (opTys, ops)

unchecked_add ::  (ExplodedDefId, CustomRHS)
unchecked_add =
    ( ["core","intrinsics", "unchecked_add"]
    , makeUncheckedArith "unchecked_add" Add
    )

unchecked_sub ::  (ExplodedDefId, CustomRHS)
unchecked_sub =
    ( ["core","intrinsics", "unchecked_sub"]
    , makeUncheckedArith "unchecked_sub" Sub
    )

unchecked_mul ::  (ExplodedDefId, CustomRHS)
unchecked_mul =
    ( ["core","intrinsics", "unchecked_mul"]
    , makeUncheckedArith "unchecked_mul" Mul
    )

unchecked_div ::  (ExplodedDefId, CustomRHS)
unchecked_div =
    ( ["core","intrinsics", "unchecked_div"]
    , makeUncheckedArith "unchecked_div" Div
    )

unchecked_rem ::  (ExplodedDefId, CustomRHS)
unchecked_rem =
    ( ["core","intrinsics", "unchecked_rem"]
    , makeUncheckedArith "unchecked_rem" Rem
    )

unchecked_shl ::  (ExplodedDefId, CustomRHS)
unchecked_shl =
    ( ["core","intrinsics", "unchecked_shl"]
    , makeUncheckedArith "unchecked_shl" Shl
    )

unchecked_shr ::  (ExplodedDefId, CustomRHS)
unchecked_shr =
    ( ["core","intrinsics", "unchecked_shr"]
    , makeUncheckedArith "unchecked_shr" Shr
    )

-- Implement the [`core::intrinsics::exact_div`] intrinsic.
-- This operation performs integer division that triggers undefined behavior
-- if the division has a nonzero remainder or overflows.
-- Supports both signed and unsigned integer types.
makeExactDiv :: CustomRHS
makeExactDiv =
  \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
    ([TyInt _ , TyInt _ ], [e1, e2]) ->
      evalExactDiv Signed e1 e2
    ([TyUint _, TyUint _], [e1, e2]) ->
      evalExactDiv Unsigned e1 e2
    _ ->
      mirFail $ "BUG: invalid arguments to exact_div: " ++ show (opTys, ops)

-- Evaluate the `exact_div` intrinsic for signed or unsigned integers.
-- Raises UB if the division overflows or is not exact.
evalExactDiv ::
  ArithType ->
  MirExp s -> MirExp s ->
  MirGenerator h s ret (MirExp s)
evalExactDiv arithType' e1 e2 = do
  (q, overflow) <- evalBinOp Div (Just arithType') e1 e2
  (r, _)        <- evalBinOp Rem (Just arithType') e1 e2
  case (q, r) of
    (MirExp (C.BVRepr wq) q', MirExp (C.BVRepr wr) r')
      | Just Refl <- testEquality wq wr -> do
          let zero = R.App $ E.BVLit wq (BV.mkBV wq 0)
          let remZero = R.App $ E.BVEq wq r' zero
          G.assertExpr (R.App $ E.Not overflow)
            (S.litExpr "undefined behavior: exact_div overflowed")
          G.assertExpr remZero
            (S.litExpr "undefined behavior: exact_div not exact")
          pure (MirExp (C.BVRepr wq) q')
    _ -> mirFail $ "BUG: invalid arguments to exact_div: " ++ show (q, r)

exact_div :: (ExplodedDefId, CustomRHS)
exact_div =
  ( ["core", "intrinsics", "exact_div"]
  , makeExactDiv
  )

-- Build a \"count leading zeros\" implementation. The function will be
-- polymorphic, accepting bitvectors of any width. The function will return
-- a width-32 bitvector, as everything that makes use of this functionality
-- hardcodes this width.
ctlz_impl :: Text -> CustomRHS
ctlz_impl name _substs = Just $ CustomOp $ \_optys ops -> case ops of
    [MirExp (C.BVRepr w) v] -> do
        let leadingZeros = S.app $ E.BVCountLeadingZeros w v
        let w32 = knownNat @32
        -- Because BVCountLeadingZeros returns a bitvector with the same width
        -- as the input, we may need to extend or truncate it to make it have a
        -- width of 32. There is no risk of information loss here due to
        -- truncation, as 32 bits is more than enough to represent the number
        -- of digits for all supported primitive integer and Bv types.
        return $ MirExp (C.BVRepr w32) $ bv_convert_impl w leadingZeros w32
    _ -> mirFail $ "BUG: invalid arguments to " ++ Text.unpack name ++ ": " ++ show ops

ctlz :: (ExplodedDefId, CustomRHS)
ctlz =
    (["core", "intrinsics", "ctlz"], ctlz_impl "ctlz")

ctlz_nonzero :: (ExplodedDefId, CustomRHS)
ctlz_nonzero =
    (["core", "intrinsics", "ctlz_nonzero"], ctlz_impl "ctlz_nonzero")

rotate_left :: (ExplodedDefId, CustomRHS)
rotate_left = ( ["core","intrinsics", "rotate_left"],
  \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp (C.BVRepr w) eVal, MirExp (C.BVRepr w') eAmt] ->
      reduceRotate E.BVRol w eVal w' eAmt
    _ -> mirFail $ "invalid arguments for rotate_left")

rotate_right :: (ExplodedDefId, CustomRHS)
rotate_right = ( ["core","intrinsics", "rotate_right"],
  \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp (C.BVRepr w) eVal, MirExp (C.BVRepr w') eAmt] ->
      reduceRotate E.BVRor w eVal w' eAmt
    _ -> mirFail $ "invalid arguments for rotate_right")

-- | Perform a left or right rotation operation. If @wVal@ (the width of the
-- first bitvector argument) is not the same as @wAmt@ (the width of the second
-- bitvector argument), then zero-extend or truncate the second bitvector
-- argument as needed before performing the rotation.
--
-- The implementation of this function is heavily inspired by @bvRol@ and
-- @bvRor@ from @what4@, which also do similar zero-extension and truncation.
reduceRotate ::
  (1 <= wVal, 1 <= wAmt) =>
  (NatRepr wVal ->
    R.Expr MIR s (C.BVType wVal) ->
    R.Expr MIR s (C.BVType wVal) ->
    E.App MIR (R.Expr MIR s) (C.BVType wVal)) ->
  NatRepr wVal ->
  R.Expr MIR s (C.BVType wVal) ->
  NatRepr wAmt ->
  R.Expr MIR s (C.BVType wAmt) ->
  MirGenerator h s ret (MirExp s)
reduceRotate rotateOp wVal eVal wAmt eAmt =
  case compareNat wVal wAmt of
    -- already the same size, apply the operation
    NatEQ ->
      pure $ MirExp (C.BVRepr wVal) $ R.App
           $ rotateOp wVal eVal eAmt

    -- wAmt is shorter: zero extend.
    NatGT _diff ->
      pure $ MirExp (C.BVRepr wVal) $ R.App
           $ rotateOp wVal eVal $ R.App
           $ E.BVZext wVal wAmt eAmt

    -- wAmt is longer: reduce modulo the width of wVal, then truncate.
    -- Truncation is OK because the value will always fit after modulo
    -- reduction.
    NatLT _diff ->
      pure $ MirExp (C.BVRepr wVal) $ R.App
           $ rotateOp wVal eVal $ R.App
           $ E.BVTrunc wVal wAmt $ R.App
           $ E.BVUrem wAmt eAmt $ R.App
           $ E.BVLit wAmt
           $ BV.mkBV wAmt $ intValue wVal

---------------------------------------------------------------------------------------
-- ** Custom ::intrinsics::discriminant_value

discriminant_value ::  (ExplodedDefId, CustomRHS)
discriminant_value = (["core","intrinsics", "discriminant_value"],
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
      case (opTys,ops) of
        ([TyRef ty@(TyAdt nm _ _) Immut], [eRef]) -> do
            adt <- findAdt nm
            e <- derefExp ty eRef >>= readPlace
            MirExp tp' e' <- enumDiscriminant adt e
            case testEquality tp' IsizeRepr of
              Just Refl ->
                return $ MirExp (C.BVRepr (knownRepr :: NatRepr 64)) $
                    isizeToBv knownRepr R.App e'
              Nothing ->
                mirFail "unexpected non-isize discriminant"
        _ -> mirFail $ "BUG: invalid arguments for discriminant_value")

type_id ::  (ExplodedDefId, CustomRHS)
type_id = (["core","intrinsics", "type_id"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \ _opTys _ops -> do
        -- Rust `TypeId`s are represented with 128-bits since
        -- https://github.com/rust-lang/rust/commit/9e5573a0d275c71dce59b715d981c6880d30703a
        tyId <- getTypeId t
        return (MirExp knownRepr (R.App (eBVLit (knownRepr :: NatRepr 128) (toInteger tyId))))
    _ -> Nothing
    )

needs_drop :: (ExplodedDefId, CustomRHS)
needs_drop = (["core","intrinsics","needs_drop"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \ _opTys _ops -> do
        needsDrop <- getNeedsDrop t
        pure (MirExp C.BoolRepr (R.App (E.BoolLit needsDrop)))
    _ -> Nothing
    )

size_of :: (ExplodedDefId, CustomRHS)
size_of = (["core", "intrinsics", "size_of"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ ->
        getLayoutFieldAsMirExp "size_of" laySize t
    _ -> Nothing
    )

size_of_val :: (ExplodedDefId, CustomRHS)
size_of_val = (["core", "intrinsics", "size_of_val"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
        -- We first check whether the underlying type is sized or not.
        ([TyRawPtr ty _], [MirExp tpr e]) -> case tpr of
            -- Slices (e.g., `&[u8]`, `&str`, and custom DSTs whose last field
            -- contains a slice) are unsized. We currently support computing
            -- the size of slice values that aren't embedded in a custom DST.
            -- TODO(#1614): Lift this restriction.
            MirSliceRepr -> case ty of
                TySlice elemTy -> sizeOfSlice elemTy e
                TyStr {} -> sizeOfSlice (TyUint B8) e
                TyAdt {} -> unsupportedCustomDst ty
                _ -> panic "size_of_val"
                       ["Unexpected MirSliceRepr type", show (PP.pretty ty)]

            -- Trait objects (e.g., `&dyn Debug` and custom DSTs whose last
            -- field contains a trait object) are unsized. This override
            -- currently does not support any kind of trait object, so all we
            -- do here is make an effort to give a descriptive error message.
            -- TODO(#1614): Support trait objects and custom DSTs here.
            DynRefRepr -> case ty of
                TyDynamic {} -> unsupportedTraitObject ty
                TyAdt {} -> unsupportedCustomDst ty
                _ -> panic "size_of_val"
                       ["Unexpected DynRefRepr type", show (PP.pretty ty)]

            -- All other cases should correspond to sized types. For these
            -- cases, computing the value's size is equivalent to computing the
            -- type's size.
            MirReferenceRepr ->
                getLayoutFieldAsMirExp "size_of_val" laySize ty
            _ -> panic "size_of_val"
                   ["Unexpected TypeRepr for *const", show tpr]
        _ -> mirFail $ "bad arguments to size_of_val: " ++ show ops
    _ -> Nothing
    )
  where
    -- The size of a slice value is equal to the to the slice length multiplied
    -- by the size of the element type. Note that slice element types are
    -- always sized, so we do not need to call size_of_val recursively here.
    sizeOfSlice ::
      Ty -> R.Expr MIR s MirSlice -> MirGenerator h s ret (MirExp s)
    sizeOfSlice ty e = do
        let len = getSliceLen e
        sz <- getLayoutFieldAsExpr "size_of_val" laySize ty
        pure $ MirExp UsizeRepr $ R.App $ usizeMul len sz

    unsupportedTraitObject :: Ty -> MirGenerator h s ret a
    unsupportedTraitObject ty =
        mirFail $ unlines
            [ "size_of_val does not currently support trait objects"
            , "In the type " ++ show (PP.pretty ty)
            ]

    unsupportedCustomDst :: Ty -> MirGenerator h s ret a
    unsupportedCustomDst ty =
        mirFail $ unlines
            [ "size_of_val does not currently support custom DSTs"
            , "In the type " ++ show (PP.pretty ty)
            ]

min_align_of :: (ExplodedDefId, CustomRHS)
min_align_of = (["core", "intrinsics", "min_align_of"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ ->
        getLayoutFieldAsMirExp "min_align_of" layAlign t
    _ -> Nothing
    )

-- mem::swap is used pervasively (both directly and via mem::replace), but it
-- has a nasty unsafe implementation, with lots of raw pointers and
-- reintepreting casts.  Fortunately, it requires `T: Sized`, so it's almost
-- trivial to implement as a custom op.
mem_swap ::  (ExplodedDefId, CustomRHS)
mem_swap = (["core","mem", "swap"], \substs ->
  case substs of
    Substs [ty] -> Just $ CustomOp $ \ opTys ops -> case ops of
        [MirExp MirReferenceRepr e1, MirExp MirReferenceRepr e2] -> do
            Some tpr <- tyToReprM ty
            val1 <- readMirRef tpr e1
            val2 <- readMirRef tpr e2
            writeMirRef tpr e1 val2
            writeMirRef tpr e2 val1
            MirExp MirAggregateRepr <$> mirAggregate_zst
        _ -> mirFail $ "bad arguments to mem_swap: " ++ show (opTys, ops)
    _ -> Nothing)

-- This is like normal mem::transmute, but requires source and target types to
-- have identical Crucible `TypeRepr`s.
mem_crucible_identity_transmute ::  (ExplodedDefId, CustomRHS)
mem_crucible_identity_transmute = (["core","mem", "crucible_identity_transmute"],
    \ substs -> case substs of
      Substs [tyT, tyU] -> Just $ CustomOp $ \ _ ops -> case ops of
        [e@(MirExp argTy _)] -> do
            Some retTy <- tyToReprM tyU
            case testEquality argTy retTy of
                Just _ -> return e
                Nothing -> mirFail $ "crucible_identity_transmute: types are not compatible: " ++
                    show (tyT, argTy) ++ " != " ++ show (tyU, retTy)
        _ -> mirFail $ "bad arguments to mem_crucible_identity_transmute: "
          ++ show (tyT, tyU, ops)
      _ -> Nothing
    )

mem_bswap ::  (ExplodedDefId, CustomRHS)
mem_bswap = (["core", "intrinsics", "bswap"],
    \ substs -> case substs of
      Substs [tyT] -> Just $ CustomOp $ \ _ ops -> case ops of
        [MirExp argTy@C.BVRepr{} argExpr] -> return . MirExp argTy $ bswap argTy argExpr
        _ -> mirFail $ "bswap expected `BVRepr w` but got: " ++ show (tyT, ops)
      _ -> Nothing)
  where
    zero = knownNat @0
    byte = knownNat @8
    bswap :: C.TypeRepr (C.BVType w) -> R.Expr MIR s (C.BVType w) -> R.Expr MIR s (C.BVType w)
    bswap (C.BVRepr w) bv
        | Just Refl <- testEquality byte w = bv -- 8 ≡ w
        | 0 <- natValue w `mod` natValue byte   -- 0 ≡ w%8
        , Just (LeqProof, Refl, LeqProof) <- lemma w =
            let x = R.App $ E.BVSelect zero byte w bv   -- least significant byte
                xsw = subNat w byte                     -- size of int sans one byte
                xs = R.App $ E.BVSelect byte xsw w bv   -- int sans least significant byte
            in R.App $ E.BVConcat byte xsw x (bswap (C.BVRepr xsw) xs)
        | otherwise = panic "bswap" ["`BVRepr w` must satisfy `8 ≤ w ∧ w%8 ≡ 0`"]
    lemma :: NatRepr w -> Maybe (LeqProof 8 w, 8 + (w - 8) :~: w, LeqProof 1 (w - 8))
    lemma w
        | Just LeqProof <- testLeq byte w               -- 8 ≤ w
        , Left (lt@LeqProof) <- testStrictLeq byte w    -- 8+1 ≤ w
        , Refl <- plusComm (subNat w byte) byte         -- 8+(w-8) ≡ (w-8)+8
        , Refl <- minusPlusCancel w byte                -- (w-8)+8 ≡ w
        , LeqProof <- leqSub2 lt (leqRefl byte)         -- 1 ≤ w-8
        = Just (LeqProof, Refl, LeqProof)
        | otherwise = Nothing

mem_transmute ::  (ExplodedDefId, CustomRHS)
mem_transmute = (["core", "intrinsics", "transmute"],
    \ substs -> case substs of
      Substs [tyT, tyU] -> Just $ CustomOp $ \ _ ops -> case ops of
        [e] -> transmuteExp e tyT tyU
        _ -> mirFail $ "bad arguments to transmute: "
          ++ show (tyT, tyU, ops)
      _ -> Nothing)

intrinsics_assume :: (ExplodedDefId, CustomRHS)
intrinsics_assume = (["core", "intrinsics", "assume"], \_substs ->
    Just $ CustomOp $ \_ ops -> case ops of
        [MirExp C.BoolRepr cond] -> do
            G.assertExpr cond $
                S.litExpr "undefined behavior: core::intrinsics::assume(false)"
            MirExp MirAggregateRepr <$> mirAggregate_zst
        _ -> mirFail $ "BUG: invalid arguments to core::intrinsics::assume: " ++ show ops
    )

-- TODO: needs layout info from mir-json
assert_inhabited :: (ExplodedDefId, CustomRHS)
assert_inhabited = (["core", "intrinsics", "assert_inhabited"], \_substs ->
    Just $ CustomOp $ \_ _ -> MirExp MirAggregateRepr <$> mirAggregate_zst)

array_from_slice ::  (ExplodedDefId, CustomRHS)
array_from_slice = (["core","slice", "{impl}", "as_array", "crucible_array_from_slice_hook"],
    \_substs -> Just $ CustomOpNamed $ \fnName ops -> do
        fn <- findFn fnName
        case (fn ^. fsig . fsreturn_ty, ops) of
            ( TyAdt optionMonoName _ (Substs [TyRef (TyArray ty tyLen) Immut]),
              [MirExp MirSliceRepr e] ) -> do
                -- TODO: This should be implemented as a type cast, so the
                -- input and output are aliases.  However, the input slice's
                -- data pointer may point into a `Vector`/`Array` rather than a
                -- `MirAggregate`, whereas the output must always point to a
                -- `MirAggregate`.  So for now, we use `aggregateCopy` to build
                -- the output.  Once `MirAggregate` flattening is enabled, we
                -- may be able to turn this into a proper cast.
                let ptr = getSlicePtr e
                let len = getSliceLen e
                let lenOk = R.App $ usizeEq len (R.App $ usizeLit $ fromIntegral tyLen)
                -- Get the Adt info for the return type, which should be
                -- Option<&[T; N]>.
                adt <- findAdt optionMonoName
                SomeRustEnumRepr discrTpr variantsCtx <- enumVariantsM adt
                let expectedEnumTpr = RustEnumRepr discrTpr variantsCtx

                Some tpr <- tyToReprM ty
                MirExp expectedEnumTpr <$> G.ifte' expectedEnumTpr lenOk
                    (do ag <- aggregateCopy_constLen tpr ptr tyLen 1  -- TODO: hardcoded size=1
                        ref <- constMirRef MirAggregateRepr ag
                        let refMir = MirExp MirReferenceRepr ref
                        MirExp enumTpr enum <- buildEnum adt optionDiscrSome [refMir]
                        Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
                        pure enum)
                    (do MirExp enumTpr enum <- buildEnum adt optionDiscrNone []
                        Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
                        pure enum)

            _ -> mirFail $ "bad monomorphization of crucible_array_from_slice_hook: " ++
                show (fnName, fn ^. fsig, ops)
    )

array_from_ref ::  (ExplodedDefId, CustomRHS)
array_from_ref = (["core", "array", "from_ref", "crucible_array_from_ref_hook"],
    \_substs -> Just $ CustomOpNamed $ \fnName ops -> do
        fn <- findFn fnName
        case (fn ^. fsig . fsreturn_ty, ops) of
            (TyRef (TyArray elemTy 1) Immut, [MirExp MirReferenceRepr elemRef]) -> do
                -- TODO: Like `array_from_slice`, above, this would be more
                -- correctly implemented as a type cast, so that the input and
                -- output are aliases.
                Some elemRepr <- tyToReprM elemTy
                elemVal <- readMirRef elemRepr elemRef
                ag <- mirAggregate_uninit_constSize 1
                -- TODO: hardcoded size=1
                ag' <- mirAggregate_set 0 1 elemRepr elemVal ag
                agRef <- constMirRef MirAggregateRepr ag'
                pure (MirExp MirReferenceRepr agRef)
            _ -> mirFail $ "bad monomorphization of crucible_array_from_ref_hook: " ++
                show (fnName, fn ^. fsig, ops)
    )

slice_from :: Mutability -> (ExplodedDefId, CustomRHS)
slice_from mut = (["core", "slice", "raw", Text.pack hookLoc, Text.pack hookName],
    \_substs -> Just $ CustomOpNamed $ \fnName ops -> do
        fn <- findFn fnName
        case (fn ^. fsig . fsreturn_ty, ops) of
            (TyRef (TySlice _elemTy) m, [MirExp MirReferenceRepr elemRef])
                | m == mut -> do
                -- Unlike `array_from_ref` and `array_from_slice`, this _does_
                -- alias the input and output. This is possible because while a
                -- `&[T; N]` must point to a `MirAggregateRepr`, which we must
                -- create, a `&[T]` can point to any `T` - so we can reuse the
                -- function's `&T` parameter.
                let sliceRef = mkSlice elemRef (R.App $ usizeLit 1)
                pure (MirExp MirSliceRepr sliceRef)
            _ -> mirFail $ "bad monomorphization of " ++ hookName ++ ": " ++
                show (fnName, fn ^. fsig, ops)
    )
    where
        (hookLoc, hookName) = case mut of
            Immut -> ("from_ref", "crucible_slice_from_ref_hook")
            Mut   -> ("from_mut", "crucible_slice_from_mut_hook")

slice_from_ref ::  (ExplodedDefId, CustomRHS)
slice_from_ref = slice_from Immut

slice_from_mut ::  (ExplodedDefId, CustomRHS)
slice_from_mut = slice_from Mut

intrinsics_offset :: (ExplodedDefId, CustomRHS)
intrinsics_offset = (["core", "intrinsics", "offset"], ptr_offset_impl)

intrinsics_arith_offset :: (ExplodedDefId, CustomRHS)
intrinsics_arith_offset = (["core", "intrinsics", "arith_offset"], ptr_wrapping_offset_impl)

intrinsics_ptr_offset_from :: (ExplodedDefId, CustomRHS)
intrinsics_ptr_offset_from = (["core", "intrinsics", "ptr_offset_from"], ptr_offset_from_impl)


-------------------------------------------------------------------------------------------------------
-- ** Custom: slice impl functions
--

slice_len :: (ExplodedDefId, CustomRHS)
slice_len =
  ( ["core","slice","{impl}","len", "crucible_slice_len_hook"]
  , slice_len_impl )

const_slice_len :: (ExplodedDefId, CustomRHS)
const_slice_len =
  ( ["core","ptr","const_ptr","{impl}","len", "crucible_slice_len_hook"]
  , slice_len_impl )

mut_slice_len :: (ExplodedDefId, CustomRHS)
mut_slice_len =
  ( ["core","ptr","mut_ptr","{impl}","len", "crucible_slice_len_hook"]
  , slice_len_impl )

slice_len_impl :: CustomRHS
slice_len_impl (Substs [_]) =
    Just $ CustomOp $ \ _optys ops ->
        case ops of
            [MirExp MirSliceRepr e] -> do
                return $ MirExp UsizeRepr $ getSliceLen e
            _ -> mirFail $ "BUG: invalid arguments to " ++ "slice_len"
slice_len_impl _ = Nothing

-- These four custom ops implement mutable and immutable unchecked indexing by
-- usize and by Range.  All other indexing dispatches to one of these.  Note
-- the use of inner `crucible_hook` functions - otherwise we can't distinguish
-- the `fn get_unchecked` in the impl for usize from the `fn get_unchecked` in
-- the impl for Range.

slice_index_usize_get_unchecked_impl :: CustomRHS
slice_index_usize_get_unchecked_impl (Substs [_elTy]) =
    Just $ CustomOp $ \ _ ops -> case ops of
        [MirExp UsizeRepr ind, MirExp MirSliceRepr slice] -> do
            let ptr = getSlicePtr slice
            ptr' <- mirRef_offset ptr ind
            return $ (MirExp MirReferenceRepr ptr')
        _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
slice_index_usize_get_unchecked_impl _ = Nothing

slice_index_usize_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked =
    ( ["core","slice","{impl}","get_unchecked", "crucible_hook_usize"]
    , slice_index_usize_get_unchecked_impl )

slice_index_usize_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked_mut =
    ( ["core","slice","{impl}","get_unchecked_mut", "crucible_hook_usize"]
    , slice_index_usize_get_unchecked_impl )

slice_index_range_get_unchecked_impl :: CustomRHS
slice_index_range_get_unchecked_impl (Substs [_elTy]) =
    Just $ CustomOp $ \ _ ops -> case ops of
        [ MirExp tr1 start, MirExp tr2 end, MirExp MirSliceRepr slice]
          | Just Refl <- testEquality tr1 UsizeRepr
          , Just Refl <- testEquality tr2 UsizeRepr
          -> do
            let ptr = getSlicePtr slice
            ptr' <- mirRef_offset ptr start
            let len' = S.app $ usizeSub end start
            return $ MirExp MirSliceRepr $ mkSlice ptr' len'

        _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
slice_index_range_get_unchecked_impl _ = Nothing

slice_index_range_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked =
    ( ["core","slice","{impl}","get_unchecked", "crucible_hook_range"]
    , slice_index_range_get_unchecked_impl )

slice_index_range_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked_mut =
    ( ["core","slice","{impl}","get_unchecked_mut", "crucible_hook_range"]
    , slice_index_range_get_unchecked_impl )

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: Integer

integerWidth :: NatRepr 512
integerWidth = knownNat

integer_from_u8 :: (ExplodedDefId, CustomRHS)
integer_from_u8 = (["int512", "u8", "from_prim"], integerFromUnsigned)

integer_from_i32 :: (ExplodedDefId, CustomRHS)
integer_from_i32 = (["int512", "i32", "from_prim"], integerFromSigned)

integer_from_u64 :: (ExplodedDefId, CustomRHS)
integer_from_u64 = (["int512", "u64", "from_prim"], integerFromUnsigned)

integerFromSigned :: CustomRHS
integerFromSigned (Substs []) =
    let w' = integerWidth in
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w) int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w') (S.app $ E.BVSext w' w int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerFromSigned: " ++ show ops
integerFromSigned _ = Nothing

integerFromUnsigned :: CustomRHS
integerFromUnsigned (Substs []) =
    let w' = integerWidth in
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w) int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w') (S.app $ E.BVZext w' w int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerFromUnsigned: " ++ show ops
integerFromUnsigned _ = Nothing


integer_as_u8 :: (ExplodedDefId, CustomRHS)
integer_as_u8 = (["int512", "u8", "as_prim"],
    integerAsUnsigned (knownNat :: NatRepr 8))

integer_as_u64 :: (ExplodedDefId, CustomRHS)
integer_as_u64 = (["int512", "u64", "as_prim"],
    integerAsUnsigned (knownNat :: NatRepr 64))

integerAsUnsigned :: 1 <= w => NatRepr w -> CustomRHS
integerAsUnsigned w (Substs []) =
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w) (S.app $ E.BVTrunc w w' int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerAsUnsigned: " ++ show ops
integerAsUnsigned _ _ = Nothing


integer_shl :: (ExplodedDefId, CustomRHS)
integer_shl = (["int512", "shl"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') val_e, MirExp (C.BVRepr w) amt_e]
          | Just LeqProof <- testLeq (incNat w) w' ->
            let amt_e' = S.app $ E.BVZext w' w amt_e in
            return $ MirExp (C.BVRepr w') (S.app $ E.BVShl w' val_e amt_e')
        _ -> mirFail $ "BUG: invalid arguments to integer_shl: " ++ show ops
  _ ->
    Nothing)

integer_shr :: (ExplodedDefId, CustomRHS)
integer_shr = (["int512", "shr"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') val_e, MirExp (C.BVRepr w) amt_e]
          | Just LeqProof <- testLeq (incNat w) w' ->
            let amt_e' = S.app $ E.BVZext w' w amt_e in
            return $ MirExp (C.BVRepr w') (S.app $ E.BVLshr w' val_e amt_e')
        _ -> mirFail $ "BUG: invalid arguments to integer_shr: " ++ show ops
  _ ->
    Nothing)

integer_bitand :: (ExplodedDefId, CustomRHS)
integer_bitand = (["int512", "bitand"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVAnd w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_bitand: " ++ show ops
  _ ->
    Nothing)

integer_bitor :: (ExplodedDefId, CustomRHS)
integer_bitor = (["int512", "bitor"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVOr w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_bitor: " ++ show ops
  _ ->
    Nothing)

integer_eq :: (ExplodedDefId, CustomRHS)
integer_eq = (["int512", "eq"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp C.BoolRepr (S.app $ E.BVEq w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_eq: " ++ show ops
  _ ->
    Nothing)

integer_lt :: (ExplodedDefId, CustomRHS)
integer_lt = (["int512", "lt"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp C.BoolRepr (S.app $ E.BVSlt w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_lt: " ++ show ops
  _ ->
    Nothing)

integer_add :: (ExplodedDefId, CustomRHS)
integer_add = (["int512", "add"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVAdd w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_add: " ++ show ops
  _ ->
    Nothing)

integer_sub :: (ExplodedDefId, CustomRHS)
integer_sub = (["int512", "sub"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVSub w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_sub: " ++ show ops
  _ ->
    Nothing)

integer_rem :: (ExplodedDefId, CustomRHS)
integer_rem = (["int512", "rem"], \substs -> case substs of
  Substs [] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVSrem w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_rem: " ++ show ops
  _ ->
    Nothing)


--------------------------------------------------------------------------------------------------------------------------
-- crucible::bitvector::Bv implementation

bv_convert :: (ExplodedDefId, CustomRHS)
bv_convert = (["crucible", "bitvector", "convert"], \substs -> case substs of
  Substs [_, u] ->
    Just $ CustomOp $ \_optys ops -> impl u ops
  _ ->
    Nothing)
  where
    impl :: HasCallStack => Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s)
    impl u ops
      | [MirExp (C.BVRepr w1) v] <- ops = do

        Some r <- tyToReprM u
        case r of
            C.BVRepr w2 ->
                return $ MirExp (C.BVRepr w2) $ bv_convert_impl w1 v w2
            _ -> mirFail ("BUG: invalid arguments to bv_convert: " ++ show ops)
      | otherwise = mirFail ("BUG: invalid arguments to bv_convert: " ++ show ops)

-- | Convert a bitvector to a different bit width. This may zero-extend or
-- truncate the bitvector if the input width differs from the output width.
-- Because this function may truncate the bitvector, be aware that calling this
-- function may result in a loss of bit information.
bv_convert_impl ::
  (1 <= inputW, 1 <= outputW) =>
  NatRepr inputW ->
  R.Expr MIR s (C.BVType inputW) ->
  NatRepr outputW ->
  R.Expr MIR s (C.BVType outputW)
bv_convert_impl w1 v w2 =
  case compareNat w1 w2 of
      NatLT _ -> S.app $ E.BVZext w2 w1 v
      NatGT _ -> S.app $ E.BVTrunc w2 w1 v
      NatEQ -> v

bv_funcs :: [(ExplodedDefId, CustomRHS)]
bv_funcs =
    [ bv_convert
    , bv_unop "neg" E.BVNeg
    , bv_unop "not" E.BVNot
    , bv_binop "add" E.BVAdd
    , bv_binop "sub" E.BVSub
    , bv_binop "mul" E.BVMul
    , bv_binop "div" E.BVUdiv
    , bv_binop "rem" E.BVUrem
    , bv_binop "bitand" E.BVAnd
    , bv_binop "bitor" E.BVOr
    , bv_binop "bitxor" E.BVXor
    , bv_shift_op "shl" E.BVShl
    , bv_shift_op "shr" E.BVLshr
    , bv_overflowing_binop "add" Add
    , bv_overflowing_binop "sub" Sub
    , bv_eq
    , bv_lt
    , bv_literal "ZERO" (\w -> eBVLit w 0)
    , bv_literal "ONE" (\w -> eBVLit w 1)
    , bv_literal "MAX" (\w -> eBVLit w $ (1 `shift` fromIntegral (intValue w)) - 1)
    , bv_leading_zeros
    ]

type BVUnOp = forall ext f w. (1 <= w)
        => (NatRepr w)
        -> (f (C.BVType w))
        -> E.App ext f (C.BVType w)

bv_unop :: Text -> BVUnOp -> (ExplodedDefId, CustomRHS)
bv_unop name op = (["crucible", "bitvector", "{impl}", name], \substs -> case substs of
  Substs [_sz] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) v1] ->
            return $ MirExp (C.BVRepr w1) (S.app $ op w1 v1)
        _ -> mirFail $ "BUG: invalid arguments to bv_" ++ Text.unpack name ++ ": " ++ show ops
  _ ->
    Nothing)

type BVBinOp = forall ext f w. (1 <= w)
        => (NatRepr w)
        -> (f (C.BVType w))
        -> (f (C.BVType w))
        -> E.App ext f (C.BVType w)

bv_binop :: Text -> BVBinOp -> (ExplodedDefId, CustomRHS)
bv_binop name op = (["crucible", "bitvector", "{impl}", name], bv_binop_impl name op)

bv_binop_impl :: Text -> BVBinOp -> CustomRHS
bv_binop_impl name op (Substs [_sz]) = Just $ CustomOp $ \_optys ops -> case ops of
    [MirExp (C.BVRepr w1) v1, MirExp (C.BVRepr w2) v2]
      | Just Refl <- testEquality w1 w2 ->
        return $ MirExp (C.BVRepr w1) (S.app $ op w1 v1 v2)
    _ -> mirFail $ "BUG: invalid arguments to bv_" ++ Text.unpack name ++ ": " ++ show ops
bv_binop_impl _ _ _ = Nothing

bv_shift_op :: Text -> BVBinOp -> (ExplodedDefId, CustomRHS)
bv_shift_op name op = (["crucible", "bitvector", name], bv_binop_impl name op)

bv_overflowing_binop :: Text -> BinOp -> (ExplodedDefId, CustomRHS)
bv_overflowing_binop name bop =
    ( ["crucible", "bitvector", "{impl}", "overflowing_" <> name]
    , makeArithWithOverflow ("bv_overflowing_" ++ Text.unpack name) (Just False) bop
    )

bv_eq :: (ExplodedDefId, CustomRHS)
bv_eq = (["crucible", "bitvector", "{impl}", "eq"], \substs -> case substs of
  Substs [sz] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp MirReferenceRepr r1, MirExp MirReferenceRepr r2]
          | Just (BVSize w) <- tyBvSize sz -> do
            v1 <- readMirRef (C.BVRepr w) r1
            v2 <- readMirRef (C.BVRepr w) r2
            return $ MirExp C.BoolRepr $ S.app $ E.BVEq w v1 v2
        _ -> mirFail $ "BUG: invalid arguments to bv_eq: " ++ show ops
  _ -> Nothing)

bv_lt :: (ExplodedDefId, CustomRHS)
bv_lt = (["crucible", "bitvector", "{impl}", "lt"], \substs -> case substs of
  Substs [sz] ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp MirReferenceRepr r1, MirExp MirReferenceRepr r2]
          | Just (BVSize w) <- tyBvSize sz -> do
            v1 <- readMirRef (C.BVRepr w) r1
            v2 <- readMirRef (C.BVRepr w) r2
            return $ MirExp C.BoolRepr $ S.app $ E.BVUlt w v1 v2
        _ -> mirFail $ "BUG: invalid arguments to bv_lt: " ++ show ops
  _ -> Nothing)

type BVMakeLiteral = forall ext f w.
    (1 <= w) => NatRepr w -> E.App ext f (C.BVType w)

bv_literal :: Text -> BVMakeLiteral -> (ExplodedDefId, CustomRHS)
bv_literal name op = (["crucible", "bitvector", "{impl}", name], \substs -> case substs of
  Substs [sz] ->
    Just $ CustomOp $ \_optys _ops -> do
        bvTy <- findExplodedAdtTy bvExplodedDefId (Substs [sz])
        tyToReprM bvTy >>= \(Some tpr) -> case tpr of
            C.BVRepr w ->
                return $ MirExp (C.BVRepr w) $ S.app $ op w
            _ -> mirFail $
                "BUG: invalid type param for bv_" ++ Text.unpack name ++ ": " ++ show sz
  _ -> Nothing)

bv_leading_zeros :: (ExplodedDefId, CustomRHS)
bv_leading_zeros =
    ( ["crucible", "bitvector", "{impl}", "leading_zeros"]
    , ctlz_impl "bv_leading_zeros" )



--------------------------------------------------------------------------------------------------------------------------
-- crucible::alloc implementation

-- fn allocate<T>(len: usize) -> *mut T
allocate :: (ExplodedDefId, CustomRHS)
allocate = (["crucible", "alloc", "allocate"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp UsizeRepr sz] -> do
            -- Create an uninitialized `MirAggregate` of length `len`, and
            -- return a pointer to its first element.
            Some tpr <- tyToReprM t
            ag <- mirAggregate_uninit sz
            ref <- newMirRef MirAggregateRepr
            writeMirRef MirAggregateRepr ref ag
            -- `subindexRef` doesn't do a bounds check (those happen on deref
            -- instead), so this works even when len is 0.
            ptr <- subindexRef tpr ref (R.App $ usizeLit 0)
            return $ MirExp MirReferenceRepr ptr
        _ -> mirFail $ "BUG: invalid arguments to allocate: " ++ show ops
    _ -> Nothing)

allocate_zeroed :: (ExplodedDefId, CustomRHS)
allocate_zeroed = (["crucible", "alloc", "allocate_zeroed"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp UsizeRepr len] -> do
            Some tpr <- tyToReprM t
            zero <- mkZero tpr
            let sz = 1  -- TODO: hardcoded size=1
            ag <- mirAggregate_replicate sz tpr zero len

            ref <- newMirRef MirAggregateRepr
            writeMirRef MirAggregateRepr ref ag
            ptr <- subindexRef tpr ref (R.App $ usizeLit 0)
            return $ MirExp MirReferenceRepr ptr
        _ -> mirFail $ "BUG: invalid arguments to allocate: " ++ show ops
    _ -> Nothing)

mkZero :: C.TypeRepr tp -> MirGenerator h s ret (R.Expr MIR s tp)
mkZero (C.BVRepr w) = return $ R.App $ eBVLit w 0
mkZero tpr = mirFail $ "don't know how to zero-initialize " ++ show tpr

-- fn reallocate<T>(ptr: *mut T, new_len: usize)
reallocate :: (ExplodedDefId, CustomRHS)
reallocate = (["crucible", "alloc", "reallocate"], \substs -> case substs of
    Substs [_t] -> Just $ CustomOp $ \_ ops -> case ops of
        [ MirExp MirReferenceRepr ptr, MirExp UsizeRepr newSz ] -> do
            (agPtr, idx) <- mirRef_peelIndex ptr

            let isZero = R.App $ usizeEq idx $ R.App $ usizeLit 0
            G.assertExpr isZero $
                S.litExpr "bad pointer in reallocate: not the start of an allocation"

            oldAg <- readMirRef MirAggregateRepr agPtr
            newAg <- mirAggregate_resize oldAg newSz
            writeMirRef MirAggregateRepr agPtr newAg
            MirExp MirAggregateRepr <$> mirAggregate_zst
        _ -> mirFail $ "BUG: invalid arguments to reallocate: " ++ show ops
    _ -> Nothing)

-- No `deallocate` for now - we'd need some extra MirRef ops to implement that
-- (since we need to get from the first-element pointer to the underlying
-- RefCell that we want to drop).


--------------------------------------------------------------------------------------------------------------------------
-- Atomic operations
--
-- These intrinsics come in many varieties that differ only in memory ordering.
-- We don't support multithreading, so there are no visible differences between
-- orderings, and we can use a single implementation for each group.

-- Make a group of atomic intrinsics.  If `name` is "foo", this generates
-- overrides for `atomic_foo`, `atomic_foo_variant1`, `atomic_foo_variant2`,
-- etc., all with the same `rhs`.
makeAtomicIntrinsics :: Text -> [Text] -> CustomRHS -> [(ExplodedDefId, CustomRHS)]
makeAtomicIntrinsics name variants rhs =
    [(["core", "intrinsics", "atomic_" <> name <> suffix], rhs)
        | suffix <- "" : map ("_" <>) variants]

atomic_store_impl :: CustomRHS
atomic_store_impl = \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp MirReferenceRepr ref, MirExp tpr val] -> do
        writeMirRef tpr ref val
        MirExp MirAggregateRepr <$> mirAggregate_zst
    _ -> mirFail $ "BUG: invalid arguments to atomic_store: " ++ show ops

atomic_load_impl :: CustomRHS
atomic_load_impl = \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
    ([TyRawPtr ty _], [MirExp MirReferenceRepr ref]) -> do
        Some tpr <- tyToReprM ty
        MirExp tpr <$> readMirRef tpr ref
    _ -> mirFail $ "BUG: invalid arguments to atomic_load: " ++ show ops

atomic_cxchg_impl :: CustomRHS
atomic_cxchg_impl = \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
    ([_, ty, _], [MirExp MirReferenceRepr ref, MirExp tpr expect, MirExp tpr' val])
      | Just Refl <- testEquality tpr tpr'
      , C.BVRepr w <- tpr -> do
        old <- readMirRef tpr ref
        let eq = R.App $ E.BVEq w old expect
        let new = R.App $ E.BVIte eq w val old
        writeMirRef tpr ref new
        buildTupleMaybeM [ty, TyBool] $
            [Just $ MirExp tpr old, Just $ MirExp C.BoolRepr eq]
    _ -> mirFail $ "BUG: invalid arguments to atomic_cxchg: " ++ show ops

atomic_fence_impl :: CustomRHS
atomic_fence_impl = \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [] -> MirExp MirAggregateRepr <$> mirAggregate_zst
    _ -> mirFail $ "BUG: invalid arguments to atomic_fence: " ++ show ops

-- Common implementation for all atomic read-modify-write operations.  These
-- all read the value, apply some operation, write the result back, and return
-- the old value.
atomic_rmw_impl ::
    String ->
    (forall w h s ret. (1 <= w) =>
        C.NatRepr w ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s (C.BVType w) ->
        MirGenerator h s ret (R.Expr MIR s (C.BVType w))) ->
    CustomRHS
atomic_rmw_impl name rmw = \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp MirReferenceRepr ref, MirExp tpr val]
      | C.BVRepr w <- tpr -> do
        old <- readMirRef tpr ref
        new <- rmw w old val
        writeMirRef tpr ref new
        return $ MirExp tpr old
    _ -> mirFail $ "BUG: invalid arguments to atomic_" ++ name ++ ": " ++ show ops

makeAtomicRMW ::
    String ->
    (forall w h s ret. (1 <= w) =>
        C.NatRepr w ->
        R.Expr MIR s (C.BVType w) ->
        R.Expr MIR s (C.BVType w) ->
        MirGenerator h s ret (R.Expr MIR s (C.BVType w))) ->
    [(ExplodedDefId, CustomRHS)]
makeAtomicRMW name rmw =
    makeAtomicIntrinsics (Text.pack name) allAtomicOrderings $
        atomic_rmw_impl name rmw

-- These names are taken from
-- https://github.com/rust-lang/rust/blob/22b4c688956de0925f7a10a79cb0e1ca35f55425/library/core/src/sync/atomic.rs#L3039-L3043
allAtomicOrderings :: [Text]
allAtomicOrderings = ["acquire", "release", "acqrel", "relaxed", "seqcst"]

atomic_funcs :: [(ExplodedDefId, CustomRHS)]
atomic_funcs =
    makeAtomicIntrinsics "store" storeVariants atomic_store_impl ++
    makeAtomicIntrinsics "load" loadVariants atomic_load_impl ++
    makeAtomicIntrinsics "cxchg" compareExchangeVariants atomic_cxchg_impl ++
    makeAtomicIntrinsics "cxchgweak" compareExchangeVariants atomic_cxchg_impl ++
    makeAtomicIntrinsics "fence" fenceVariants atomic_fence_impl ++
    makeAtomicIntrinsics "singlethreadfence" fenceVariants atomic_fence_impl ++
    concat [
        makeAtomicRMW "xchg" $ \_w _old val -> return val,
        makeAtomicRMW "xadd" $ \w old val -> return $ R.App $ E.BVAdd w old val,
        makeAtomicRMW "xsub" $ \w old val -> return $ R.App $ E.BVSub w old val,
        makeAtomicRMW "and" $ \w old val -> return $ R.App $ E.BVAnd w old val,
        makeAtomicRMW "or" $ \w old val -> return $ R.App $ E.BVOr w old val,
        makeAtomicRMW "xor" $ \w old val -> return $ R.App $ E.BVXor w old val,
        makeAtomicRMW "nand" $ \w old val ->
            return $ R.App $ E.BVNot w $ R.App $ E.BVAnd w old val,
        makeAtomicRMW "max" $ \w old val -> return $ R.App $ E.BVSMax w old val,
        makeAtomicRMW "min" $ \w old val -> return $ R.App $ E.BVSMin w old val,
        makeAtomicRMW "umax" $ \w old val -> return $ R.App $ E.BVUMax w old val,
        makeAtomicRMW "umin" $ \w old val -> return $ R.App $ E.BVUMin w old val
    ]
  where
    -- See https://github.com/rust-lang/rust/blob/22b4c688956de0925f7a10a79cb0e1ca35f55425/library/core/src/sync/atomic.rs#L3008-L3012
    storeVariants = ["release", "relaxed", "seqcst"]
    -- See https://github.com/rust-lang/rust/blob/22b4c688956de0925f7a10a79cb0e1ca35f55425/library/core/src/sync/atomic.rs#L3023-L3027
    loadVariants = ["acquire", "relaxed", "seqcst"]
    -- See https://github.com/rust-lang/rust/blob/22b4c688956de0925f7a10a79cb0e1ca35f55425/library/core/src/sync/atomic.rs#L3095-L3111
    compareExchangeVariants = [ success <> "_" <> failure
                              | success <- allAtomicOrderings
                              , failure <- allAtomicOrderings
                              , failure `notElem` ["acqrel", "release"]
                              ]
    -- See https://github.com/rust-lang/rust/blob/22b4c688956de0925f7a10a79cb0e1ca35f55425/library/core/src/sync/atomic.rs#L3366-L3370
    fenceVariants = ["acquire", "release", "acqrel", "seqcst"]

--------------------------------------------------------------------------------------------------------------------------

unlikely :: (ExplodedDefId, CustomRHS)
unlikely = (name, rhs)
    where
        name = ["core", "intrinsics", "unlikely"]
        rhs _substs = Just $ CustomOp $ \_ ops -> case ops of
          [op] -> pure op
          _ -> mirFail $ "bad arguments to intrinsics::unlikely: " ++ show ops



--------------------------------------------------------------------------------------------------------------------------

-- | @fn bitreverse<T>(_x: T) -> T@.
--
-- Reverse the bits in an integer type @T@.
bitreverse :: (ExplodedDefId, CustomRHS)
bitreverse = (["core", "intrinsics", "bitreverse"],
  \(Substs substs) ->
    case substs of
      [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp tpr@(C.BVRepr w) val] ->
          return $ MirExp tpr $ bvBitreverse w val
        _ -> mirFail $ "bad arguments to intrinsics::bitreverse: " ++ show ops
      _ -> Nothing)
  where
    -- The code below is cargo-culted from the implementation of what4's
    -- bvBitreverse function
    -- (https://hackage.haskell.org/package/what4-1.6.3/docs/src/What4.Interface.html#bvBitreverse),
    -- but modified to work over Crucible `Expr`s.

    -- Swap the order of bits in a bitvector.
    bvBitreverse ::
      forall s w.
      (1 <= w) =>
      NatRepr w ->
      R.Expr MIR s (C.BVType w) ->
      R.Expr MIR s (C.BVType w)
    bvBitreverse w v =
      bvJoinVector (knownNat @1) $
      PV.reverse $
      bvSplitVector w (knownNat @1) v

    -- Join a @PV.Vector@ of smaller bitvectors. The vector is interpreted in
    -- big endian order; that is, with the most significant bitvector first.
    bvJoinVector ::
      forall s n w.
      (1 <= w) =>
      NatRepr w ->
      PV.Vector n (R.Expr MIR s (C.BVType w)) ->
      R.Expr MIR s (C.BVType (n * w))
    bvJoinVector w =
        coerce $ PV.joinWith @(BVExpr s) @n bvConcat' w
      where
        bvConcat' ::
          forall l.
          (1 <= l) =>
          NatRepr l ->
          BVExpr s w ->
          BVExpr s l ->
          BVExpr s (w + l)
        bvConcat' l (BVExpr x) (BVExpr y)
          | LeqProof <- leqAdd (LeqProof @1 @w) l
          = BVExpr $ R.App $ E.BVConcat w l x y

    -- Split a bitvector to a @PV.Vector@ of smaller bitvectors. The returned
    -- vector is in big endian order; that is, with the most significant bitvector first.
    bvSplitVector ::
      forall s n w.
      (1 <= w, 1 <= n) =>
      NatRepr n ->
      NatRepr w ->
      R.Expr MIR s (C.BVType (n * w)) ->
      PV.Vector n (R.Expr MIR s (C.BVType w))
    bvSplitVector n w x =
        coerce $ PV.splitWith BigEndian bvSelect' n w (BVExpr x)
      where
        bvSelect' ::
          forall i.
          (i + w <= n * w) =>
          NatRepr (n * w) ->
          NatRepr i ->
          BVExpr s (n * w) ->
          BVExpr s w
        bvSelect' nw i (BVExpr y)
          | LeqProof <- leqMulPos n w
          = BVExpr $ R.App $ E.BVSelect i w nw y

-- | This newtype is necessary for @bvJoinVector@ and @bvSplitVector@ (used in
-- the implementation of 'bitreverse' above). These both use functions from
-- "Data.Parameterized.Vector" that that expect a wrapper of kind @Nat -> Type@,
-- defining this newtype with (w :: Nat) as the last type parameter allows us to
-- partially apply @BVExpr s@ to obtain something of kind @Nat -> Type@.
newtype BVExpr s w = BVExpr (R.Expr MIR s (C.BVType w))

--------------------------------------------------------------------------------------------------------------------------
-- MaybeUninit

maybe_uninit_uninit :: (ExplodedDefId, CustomRHS)
maybe_uninit_uninit = (["core", "mem", "maybe_uninit", "{impl}", "uninit"],
    \substs -> case substs of
        Substs [t] -> Just $ CustomOp $ \_ _ -> do
            maybeUninitTy <- findExplodedAdtTy maybeUninitExplodedDefId (Substs [t])
            initialValue maybeUninitTy >>= \mv -> case mv of
                Just v -> return v
                Nothing -> mirFail $ "MaybeUninit::uninit unsupported for " ++ show t
        _ -> Nothing)

--------------------------------------------------------------------------------------------------------------------------
-- NonZero

non_zero_new ::  (ExplodedDefId, CustomRHS)
non_zero_new = (["core", "num", "nonzero", "{impl}", "new", "crucible_non_zero_new_hook"],
    \_substs -> Just $ CustomOpNamed $ \fnName ops -> do
        fn <- findFn fnName
        case (fn ^. fsig . fsreturn_ty, ops) of
            (TyAdt optionMonoName _ _, [MirExp tpr@(C.BVRepr w) val]) -> do
                let isZero = R.App $ E.BVEq w val $ R.App $ E.BVLit w $ BV.mkBV w 0
                -- Get the Adt info for the return type, which should be
                -- Option<NonZero<T>>.
                adt <- findAdt optionMonoName
                SomeRustEnumRepr discrTpr variantsCtx <- enumVariantsM adt
                let expectedEnumTpr = RustEnumRepr discrTpr variantsCtx
                MirExp expectedEnumTpr <$> G.ifte' expectedEnumTpr isZero
                    (do MirExp enumTpr enum <- buildEnum adt optionDiscrNone []
                        Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
                        pure enum)
                    (do MirExp enumTpr enum <- buildEnum adt optionDiscrSome [MirExp tpr val]
                        Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
                        pure enum)
            _ -> mirFail $ "bad arguments to NonZero::new: " ++ show ops
    )

--------------------------------------------------------------------------------------------------------------------------

ctpop :: (ExplodedDefId, CustomRHS)
ctpop = (["core", "intrinsics", "ctpop"],
    \(Substs substs) -> case substs of
        [_] -> Just $ CustomOp $ \_ ops -> case ops of
            [MirExp tpr@(C.BVRepr w) val] ->
                Mir.Trans.extendUnsignedBV
                    (MirExp tpr $ R.App $ E.BVPopcount w val)
                    (knownNat @32)
            _ -> mirFail $ "bad arguments to intrinsics::ctpop: " ++ show ops
        _ -> Nothing)

--------------------------------------------------------------------------------------------------------------------------
-- Implementations for `IkCloneShim`.  Clone shims are auto-generated `clone`
-- and `clone_from` implementations for tuples, closures, coroutine closures,
-- function pointers, and function definitions. They dispatch to the
-- `clone`/`clone_from` methods of the individual fields or array elements.

cloneShimDef :: Ty -> [M.DefId] -> CustomOp
cloneShimDef (TyTuple tys) parts = cloneShimTuple tys parts
cloneShimDef (TyClosure upvar_tys) parts = cloneShimTuple upvar_tys parts
cloneShimDef (TyCoroutineClosure upvar_tys) parts = cloneShimTuple upvar_tys parts
cloneShimDef (TyFnPtr _) parts = cloneShimNoFields "function pointer" parts
cloneShimDef (TyFnDef _) parts = cloneShimNoFields "function definition" parts
cloneShimDef ty _parts = CustomOp $ \_ _ -> mirFail $ "cloneShimDef not implemented for " ++ show ty

-- | Create an 'IkCloneShim' implementation for a tuple or closure type.
cloneShimTuple :: [Ty] -> [M.DefId] -> CustomOp
cloneShimTuple tys parts = CustomMirOp $ \ops -> do
    when (length tys /= length parts) $ mirFail "cloneShimTuple: expected tys and parts to match"
    -- The clone shim expects exactly one operand, with a reference type that
    -- looks something `&(A, B, C)`. First, we dereference the argument to
    -- obtain an lvalue `lv: (A, B, C)`.
    lv <- case ops of
        [Move lv] -> return (LProj lv Deref)
        [Copy lv] -> return (LProj lv Deref)
        -- Temp operands can be introduced when evaluating nested tuple clone
        -- shims (e.g., ((1, 2), 3).clone()), as seen in the invocation of
        -- `callExp` below. We manually dereference these by removing the inner
        -- Ref rvalue.
        [Temp (Ref _ lv _)] -> return lv
        [op] -> mirFail $ "cloneShimTuple: expected lvalue operand, but got " ++ show op
        _ -> mirFail $ "cloneShimTuple: expected exactly one argument, but got " ++ show (length ops)
    -- Project out the tuple fields to pass to the individual clone methods.
    -- These clone methods require `&A`, `&B`, `&C`, computed as `&lv.0`.
    let fieldRefRvs = zipWith (\ty i ->
            Ref Shared (LProj lv (PField i ty)) "_") tys [0..]
    -- Call the individual clone methods. Use Temp operands as a shortcut for
    -- constructing operands to pass to the methods. (It's awkward to use Move
    -- or Copy operand instead, as they require lvalues, but using Ref above
    -- forces them to be rvalues.)
    clonedExps <- zipWithM (\part rv -> callExp part [Temp rv]) parts fieldRefRvs
    -- Finally, construct the result tuple using the cloned fields.
    buildTupleMaybeM tys (map Just clonedExps)

-- | Create an 'IkCloneShim' implementation for a value that is expected not to
-- have any fields. Implementing clone shims for such values is as simple as
-- dereferencing them.
cloneShimNoFields ::
  -- | What type of value this is. This is only used for error messages.
  String ->
  -- | The value's fields, which is checked to be empty.
  [M.DefId] ->
  CustomOp
cloneShimNoFields what parts
  | [] <- parts = CustomOp $ \opTys ops ->
    case (opTys, ops) of
      ([TyRef ty _], [eRef]) -> do
        e <- derefExp ty eRef
        readPlace e
      _ -> mirFail $ "cloneShimNoFields: expected exactly one argument, but got " ++ show (opTys, ops)
  | otherwise = CustomOp $ \_ _ -> mirFail $
    "expected no clone functions in " ++ what ++ " clone shim, but got " ++ show parts

cloneFromShimDef :: Ty -> [M.DefId] -> CustomOp
cloneFromShimDef ty _parts = CustomOp $ \_ _ -> mirFail $ "cloneFromShimDef not implemented for " ++ show ty



--------------------------------------------------------------------------------------------------------------------------

-- Convert a Crucible `MaybeType` into a Rust `Option`.
--
-- The caller is responsible for ensuring that `Option<T>` exists in the crate.
maybeToOption :: Ty -> C.TypeRepr tp -> R.Expr MIR s (C.MaybeType tp) ->
    MirGenerator h s ret (MirExp s)
maybeToOption ty tpr e = do
    adt <- findExplodedAdtInst optionExplodedDefId (Substs [ty])
    SomeRustEnumRepr discrTpr variantsCtx <- enumVariantsM adt
    let expectedEnumTpr = RustEnumRepr discrTpr variantsCtx
    e' <- G.caseMaybe e expectedEnumTpr $ G.MatchMaybe
        (\val -> do
          MirExp enumTpr enum <- buildEnum adt optionDiscrSome [MirExp tpr val]
          Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
          pure enum)
        (do MirExp enumTpr enum <- buildEnum adt optionDiscrNone []
            Refl <- expectEnumOrFail discrTpr variantsCtx enumTpr
            pure enum)
    return $ MirExp expectedEnumTpr e'
