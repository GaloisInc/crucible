{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
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

module Mir.TransCustom(customOps) where

import Data.Bits (shift)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.String as String
import           Data.String (fromString)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V

import Control.Monad
import Control.Lens

import GHC.Stack

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Type.Equality (gcastWith) -- counterpart to NatRepr.withLeqProof but for Refl
import Data.Parameterized.Peano
import Data.Parameterized.Some
import Data.Parameterized.WithRepr


-- crucible
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.Syntax as S
import qualified Lang.Crucible.CFG.Reg as R
import Lang.Crucible.Panic

import qualified What4.ProgramLoc as PL



import qualified Mir.DefId as M
import           Mir.DefId (ExplodedDefId)
import           Mir.Mir

import           Mir.PP (fmt)
import           Mir.Generator hiding (customOps)
import           Mir.Intrinsics
import           Mir.TransTy
import           Mir.Trans

import Debug.Trace


--------------------------------------------------------------------------------------------------------------------------
-- *  Primitives & other custom stuff



customOps = CustomOpMap customOpDefs fnPtrShimDef cloneShimDef cloneFromShimDef

customOpDefs :: Map ExplodedDefId CustomRHS
customOpDefs = Map.fromList $ [
                           slice_index_usize_get_unchecked
                         , slice_index_range_get_unchecked
                         , slice_index_usize_get_unchecked_mut
                         , slice_index_range_get_unchecked_mut
                         , slice_len

                         -- core::intrinsics
                         , discriminant_value
                         , type_id
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
                         , min_align_of
                         , intrinsics_assume
                         , assert_inhabited

                         , mem_transmute
                         , mem_bswap
                         , mem_crucible_identity_transmute
                         , array_from_slice

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
                         , ptr_compare_usize
                         , is_aligned_and_not_null
                         , ptr_slice_from_raw_parts
                         , ptr_slice_from_raw_parts_mut

                         , ptr_read
                         , ptr_write
                         , ptr_swap
                         , intrinsics_copy
                         , intrinsics_copy_nonoverlapping

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
exit = (["std", "process", "exit"], \s ->
           Just (CustomOpExit $ \ops -> return "process::exit"))

abort :: (ExplodedDefId, CustomRHS)
abort = (["core", "intrinsics", "", "abort"], \s ->
            Just (CustomOpExit $ \ops -> return "intrinsics::abort"))

panicking_begin_panic :: (ExplodedDefId, CustomRHS)
panicking_begin_panic = (["std", "panicking", "begin_panic"], \s -> Just $ CustomOpExit $ \ops -> do
    name <- use $ currentFn . fname
    return $ "panicking::begin_panic, called from " <> M.idText name
    )

panicking_panic :: (ExplodedDefId, CustomRHS)
panicking_panic = (["core", "panicking", "panic"], \s -> Just $ CustomOpExit $ \ops -> do
    name <- use $ currentFn . fname
    return $ "panicking::panic, called from " <> M.idText name
    )

panicking_panic_fmt :: (ExplodedDefId, CustomRHS)
panicking_panic_fmt = (["core", "panicking", "panic_fmt"], \s -> Just $ CustomOpExit $ \ops -> do
    name <- use $ currentFn . fname
    return $ "panicking::panic_fmt, called from " <> M.idText name
    )

panicking_panicking :: (ExplodedDefId, CustomRHS)
panicking_panicking = (["std", "panicking", "panicking"], \_ -> Just $ CustomOp $ \_ _ -> do
    return $ MirExp C.BoolRepr $ R.App $ E.BoolLit False)


-----------------------------------------------------------------------------------------------------
-- ** Custom: Vector

-- Methods for crucible::vector::Vector<T> (which has custom representation)

vector_new :: (ExplodedDefId, CustomRHS)
vector_new = ( ["crucible","vector","{{impl}}", "new"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ -> do
        Some tpr <- tyToReprM t
        return $ MirExp (C.VectorRepr tpr) (R.App $ E.VectorLit tpr V.empty)
    _ -> Nothing

vector_replicate :: (ExplodedDefId, CustomRHS)
vector_replicate = ( ["crucible","vector","{{impl}}", "replicate"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp tpr eVal, MirExp UsizeRepr eLen] -> do
            let eLenNat = R.App $ usizeToNat eLen
            return $ MirExp (C.VectorRepr tpr) (R.App $ E.VectorReplicate tpr eLenNat eVal)
        _ -> mirFail $ "bad arguments for Vector::replicate: " ++ show ops
    _ -> Nothing

vector_len :: (ExplodedDefId, CustomRHS)
vector_len = ( ["crucible","vector","{{impl}}", "len"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr (C.VectorRepr tpr)) eRef] -> do
            e <- readMirRef (C.VectorRepr tpr) eRef
            return $ MirExp UsizeRepr (R.App $ vectorSizeUsize R.App e)
        _ -> mirFail $ "bad arguments for Vector::len: " ++ show ops
    _ -> Nothing

vector_push :: (ExplodedDefId, CustomRHS)
vector_push = ( ["crucible","vector","{{impl}}", "push"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec, MirExp tpr' eItem]
          | Just Refl <- testEquality tpr tpr' -> do
            eSnoc <- vectorSnoc tpr eVec eItem
            return $ MirExp (C.VectorRepr tpr) eSnoc
        _ -> mirFail $ "bad arguments for Vector::push: " ++ show ops
    _ -> Nothing

vector_push_front :: (ExplodedDefId, CustomRHS)
vector_push_front = ( ["crucible","vector","{{impl}}", "push_front"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec, MirExp tpr' eItem]
          | Just Refl <- testEquality tpr tpr' -> do
            let eSnoc = R.App $ E.VectorCons tpr eItem eVec
            return $ MirExp (C.VectorRepr tpr) eSnoc
        _ -> mirFail $ "bad arguments for Vector::push_front: " ++ show ops
    _ -> Nothing

vector_pop :: (ExplodedDefId, CustomRHS)
vector_pop = ( ["crucible","vector","{{impl}}", "pop"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec] -> do
            meInit <- MirExp (C.VectorRepr tpr) <$> vectorInit tpr eVec
            -- `Option<T>` must exist because it appears in the return type.
            meLast <- vectorLast tpr eVec >>= maybeToOption t tpr
            buildTupleMaybeM [CTyVector t, CTyOption t] [Just meInit, Just meLast]
        _ -> mirFail $ "bad arguments for Vector::pop: " ++ show ops
    _ -> Nothing

vector_pop_front :: (ExplodedDefId, CustomRHS)
vector_pop_front = ( ["crucible","vector","{{impl}}", "pop_front"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec] -> do
            -- `Option<T>` must exist because it appears in the return type.
            meHead <- vectorHead tpr eVec >>= maybeToOption t tpr
            meTail <- MirExp (C.VectorRepr tpr) <$> vectorTail tpr eVec
            buildTupleMaybeM [CTyOption t, CTyVector t] [Just meHead, Just meTail]
        _ -> mirFail $ "bad arguments for Vector::pop_front: " ++ show ops
    _ -> Nothing

vector_as_slice_impl :: CustomRHS
vector_as_slice_impl (Substs [t]) =
    Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr (C.VectorRepr tpr)) e] -> do
            -- This is similar to `&mut [T; n] -> &mut [T]` unsizing.
            v <- readMirRef (C.VectorRepr tpr) e
            let end = R.App $ vectorSizeUsize R.App v
            e' <- mirRef_vectorAsMirVector tpr e
            e'' <- subindexRef tpr e' (R.App $ usizeLit 0)
            let tup = S.mkStruct
                    (Ctx.Empty Ctx.:> MirReferenceRepr tpr Ctx.:> knownRepr)
                    (Ctx.Empty Ctx.:> e'' Ctx.:> end)
            return $ MirExp (MirSliceRepr tpr) tup
        _ -> mirFail $ "bad arguments for Vector::as_slice: " ++ show ops
vector_as_slice_impl _ = Nothing

-- `&Vector<T>` and `&[T]` use the same representations as `&mut Vector<T>` and
-- `&mut [T]`, so we can use the same implementation.
vector_as_slice :: (ExplodedDefId, CustomRHS)
vector_as_slice = ( ["crucible","vector","{{impl}}", "as_slice"], vector_as_slice_impl )

vector_as_mut_slice :: (ExplodedDefId, CustomRHS)
vector_as_mut_slice = ( ["crucible","vector","{{impl}}", "as_mut_slice"], vector_as_slice_impl )

vector_concat :: (ExplodedDefId, CustomRHS)
vector_concat = ( ["crucible","vector","{{impl}}", "concat"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr1) e1, MirExp (C.VectorRepr tpr2) e2]
          | Just Refl <- testEquality tpr1 tpr2 -> do
            MirExp (C.VectorRepr tpr1) <$> vectorConcat tpr1 e1 e2
        _ -> mirFail $ "bad arguments for Vector::concat: " ++ show ops
    _ -> Nothing

vector_split_at :: (ExplodedDefId, CustomRHS)
vector_split_at = ( ["crucible","vector","{{impl}}", "split_at"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (C.VectorRepr tpr) eVec, MirExp UsizeRepr eIdx] -> do
            let eIdxNat = R.App $ usizeToNat eIdx
            mePre <- MirExp (C.VectorRepr tpr) <$> vectorTake tpr eVec eIdxNat
            meSuf <- MirExp (C.VectorRepr tpr) <$> vectorDrop tpr eVec eIdxNat
            buildTupleMaybeM [CTyVector t, CTyVector t] [Just mePre, Just meSuf]
        _ -> mirFail $ "bad arguments for Vector::split_at: " ++ show ops
    _ -> Nothing

vector_copy_from_slice :: (ExplodedDefId, CustomRHS)
vector_copy_from_slice = ( ["crucible","vector","{{impl}}", "copy_from_slice"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirSliceRepr tpr) e] -> do
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
array_zeroed = ( ["crucible","array","{{impl}}", "zeroed"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ -> tyToReprM t >>= \(Some tpr) -> case tpr of
        C.BVRepr w -> do
            let idxs = Ctx.Empty Ctx.:> BaseUsizeRepr
            v <- arrayZeroed idxs w
            return $ MirExp (C.SymbolicArrayRepr idxs (C.BaseBVRepr w)) v
        _ -> mirFail $ "bad substs for Array::zeroed: " ++ show t
    _ -> Nothing

array_lookup :: (ExplodedDefId, CustomRHS)
array_lookup = ( ["crucible","array","{{impl}}", "lookup"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [ MirExp (UsizeArrayRepr btr) eArr,
          MirExp UsizeRepr eIdx ] -> do
            let idx = E.BaseTerm BaseUsizeRepr eIdx
            let idxs = Ctx.Empty Ctx.:> idx
            return $ MirExp (C.baseToType btr) (R.App $ E.SymArrayLookup btr eArr idxs)
        _ -> mirFail $ "bad arguments for Array::lookup: " ++ show ops
    _ -> Nothing

array_update :: (ExplodedDefId, CustomRHS)
array_update = ( ["crucible","array","{{impl}}", "update"], ) $ \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
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
        [ MirExp (MirReferenceRepr (UsizeArrayRepr btpr)) e,
          MirExp UsizeRepr start,
          MirExp UsizeRepr len ] -> do
            e' <- mirRef_arrayAsMirVector btpr e
            let tpr = C.baseToType btpr
            ptr <- subindexRef tpr e' start
            return $ MirExp (MirSliceRepr tpr) $ mkSlice tpr ptr len
        _ -> mirFail $ "bad arguments for Array::as_slice: " ++ show ops
array_as_slice_impl _ = Nothing

array_as_slice :: (ExplodedDefId, CustomRHS)
array_as_slice = ( ["crucible","array","{{impl}}", "as_slice"], array_as_slice_impl )

array_as_mut_slice :: (ExplodedDefId, CustomRHS)
array_as_mut_slice = ( ["crucible","array","{{impl}}", "as_mut_slice"], array_as_slice_impl )



-----------------------------------------------------------------------------------------------------
-- ** Custom: Any

-- Methods for crucible::any::Any (which has custom representation)

any_new :: (ExplodedDefId, CustomRHS)
any_new = ( ["core", "crucible", "any", "{{impl}}", "new"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp tpr e] -> do
            return $ MirExp C.AnyRepr $ R.App $ E.PackAny tpr e
        _ -> mirFail $ "bad arguments for Any::new: " ++ show ops
    _ -> Nothing
    )

any_downcast :: (ExplodedDefId, CustomRHS)
any_downcast = ( ["core", "crucible", "any", "{{impl}}", "downcast"], \substs -> case substs of
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
        [MirExp (MirReferenceRepr tpr) ref, MirExp IsizeRepr offset] ->
            MirExp (MirReferenceRepr tpr) <$> mirRef_offset tpr ref offset
        _ -> mirFail $ "bad arguments for ptr::offset: " ++ show ops
    _ -> Nothing

ptr_offset :: (ExplodedDefId, CustomRHS)
ptr_offset = (["core", "ptr", "const_ptr", "{{impl}}", "offset"], ptr_offset_impl)
ptr_offset_mut :: (ExplodedDefId, CustomRHS)
ptr_offset_mut = (["core", "ptr", "mut_ptr", "{{impl}}", "offset"], ptr_offset_impl)

ptr_wrapping_offset_impl :: CustomRHS
ptr_wrapping_offset_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr) ref, MirExp IsizeRepr offset] ->
            MirExp (MirReferenceRepr tpr) <$> mirRef_offsetWrap tpr ref offset
        _ -> mirFail $ "bad arguments for ptr::wrapping_offset: " ++ show ops
    _ -> Nothing

ptr_wrapping_offset :: (ExplodedDefId, CustomRHS)
ptr_wrapping_offset =
    (["core", "ptr", "const_ptr", "{{impl}}", "wrapping_offset"], ptr_wrapping_offset_impl)
ptr_wrapping_offset_mut :: (ExplodedDefId, CustomRHS)
ptr_wrapping_offset_mut =
    (["core", "ptr", "mut_ptr", "{{impl}}", "wrapping_offset"], ptr_wrapping_offset_impl)

ptr_offset_from_impl :: CustomRHS
ptr_offset_from_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr1) ref1, MirExp (MirReferenceRepr tpr2) ref2]
          | Just Refl <- testEquality tpr1 tpr2 -> do
            maybeOffset <- mirRef_tryOffsetFrom ref1 ref2
            let errMsg = R.App $ E.StringLit $ fromString $
                    "tried to subtract pointers into different arrays"
            let val = R.App $ E.FromJustValue IsizeRepr maybeOffset errMsg
            return $ MirExp IsizeRepr val
        _ -> mirFail $ "bad arguments for ptr::offset_from: " ++ show ops
    _ -> Nothing

ptr_offset_from :: (ExplodedDefId, CustomRHS)
ptr_offset_from = (["core", "ptr", "const_ptr", "{{impl}}", "offset_from"], ptr_offset_from_impl)
ptr_offset_from_mut :: (ExplodedDefId, CustomRHS)
ptr_offset_from_mut = (["core", "ptr", "mut_ptr", "{{impl}}", "offset_from"], ptr_offset_from_impl)

ptr_compare_usize :: (ExplodedDefId, CustomRHS)
ptr_compare_usize = (["core", "crucible", "ptr", "compare_usize"],
    \substs -> case substs of
        Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
            [MirExp (MirReferenceRepr tpr) ptr, MirExp UsizeRepr val] -> do
                valAsPtr <- integerToMirRef tpr val
                MirExp C.BoolRepr <$> mirRef_eq ptr valAsPtr
            [MirExp (MirSliceRepr tpr) slice, MirExp UsizeRepr val] -> do
                let ptr = getSlicePtr slice
                valAsPtr <- integerToMirRef tpr val
                MirExp C.BoolRepr <$> mirRef_eq ptr valAsPtr
            -- TODO: `&dyn Tr` case (after defining MirDynRepr)
            _ -> mirFail $ "bad arguments for ptr::compare_usize: " ++ show ops
        _ -> Nothing)

is_aligned_and_not_null :: (ExplodedDefId, CustomRHS)
-- Not an actual intrinsic, so it's not in an `extern` block, so it doesn't
-- have the "" element in its path.
is_aligned_and_not_null = (["core", "intrinsics", "is_aligned_and_not_null"],
    -- TODO (layout): correct behavior is to return `True` for all valid
    -- references, and check `i != 0 && i % align_of::<T>() == 0` for
    -- `MirReference_Integer i`.  However, `align_of` is not implementable
    -- until we start gathering layout information from mir-json.
    \_substs -> Just $ CustomOp $ \_ _ -> return $ MirExp C.BoolRepr $ R.App $ E.BoolLit True)

ptr_slice_from_raw_parts_impl :: CustomRHS
ptr_slice_from_raw_parts_impl = \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr) ptr, MirExp UsizeRepr len] ->
            return $ MirExp (MirSliceRepr tpr) (mkSlice tpr ptr len)
        _ -> mirFail $ "bad arguments for ptr::slice_from_raw_parts: " ++ show ops
    _ -> Nothing

ptr_slice_from_raw_parts :: (ExplodedDefId, CustomRHS)
ptr_slice_from_raw_parts =
    ( ["core", "ptr", "slice_from_raw_parts"]
    , ptr_slice_from_raw_parts_impl)
ptr_slice_from_raw_parts_mut :: (ExplodedDefId, CustomRHS)
ptr_slice_from_raw_parts_mut =
    ( ["core", "ptr", "slice_from_raw_parts_mut"]
    , ptr_slice_from_raw_parts_impl)


ptr_read :: (ExplodedDefId, CustomRHS)
ptr_read = ( ["core", "ptr", "read"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr) ptr] ->
            MirExp tpr <$> readMirRef tpr ptr
        _ -> mirFail $ "bad arguments for ptr::read: " ++ show ops
    _ -> Nothing)

ptr_write :: (ExplodedDefId, CustomRHS)
ptr_write = ( ["core", "ptr", "write"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr) ptr, MirExp tpr' val]
          | Just Refl <- testEquality tpr tpr' -> do
            writeMirRef ptr val
            return $ MirExp C.UnitRepr $ R.App E.EmptyApp
        _ -> mirFail $ "bad arguments for ptr::write: " ++ show ops
    _ -> Nothing)

ptr_swap :: (ExplodedDefId, CustomRHS)
ptr_swap = ( ["core", "ptr", "swap"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr) ptr1, MirExp (MirReferenceRepr tpr') ptr2]
          | Just Refl <- testEquality tpr tpr' -> do
            x1 <- readMirRef tpr ptr1
            x2 <- readMirRef tpr ptr2
            writeMirRef ptr1 x2
            writeMirRef ptr2 x1
            return $ MirExp C.UnitRepr $ R.App E.EmptyApp
        _ -> mirFail $ "bad arguments for ptr::swap: " ++ show ops
    _ -> Nothing)


intrinsics_copy :: (ExplodedDefId, CustomRHS)
intrinsics_copy = ( ["core", "intrinsics", "copy"], \substs -> case substs of
    Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp (MirReferenceRepr tpr) src,
         MirExp (MirReferenceRepr tpr') dest,
         MirExp UsizeRepr count]
          | Just Refl <- testEquality tpr tpr' -> do
            -- `copy` (as opposed to `copy_nonoverlapping`) must work
            -- atomically even when the source and dest overlap.  We do this by
            -- taking a snapshot of the source, then copying the snapshot into
            -- dest.
            (srcVec, srcIdx) <- mirRef_peelIndex tpr src
            srcSnapVec <- readMirRef (MirVectorRepr tpr) srcVec
            srcSnapRoot <- constMirRef (MirVectorRepr tpr) srcSnapVec
            srcSnap <- subindexRef tpr srcSnapRoot srcIdx

            ptrCopy tpr srcSnap dest count
            return $ MirExp C.UnitRepr $ R.App E.EmptyApp

        _ -> mirFail $ "bad arguments for intrinsics::copy: " ++ show ops
    _ -> Nothing)

intrinsics_copy_nonoverlapping :: (ExplodedDefId, CustomRHS)
intrinsics_copy_nonoverlapping = ( ["core", "intrinsics", "copy_nonoverlapping"],
    \substs -> case substs of
        Substs [_] -> Just $ CustomOp $ \_ ops -> case ops of
            [MirExp (MirReferenceRepr tpr) src,
             MirExp (MirReferenceRepr tpr') dest,
             MirExp UsizeRepr count]
              | Just Refl <- testEquality tpr tpr' -> do
                -- Assert that the two regions really are nonoverlapping.
                maybeOffset <- mirRef_tryOffsetFrom dest src

                -- `count` must not exceed isize::MAX, else the overlap check
                -- will misbehave.
                let sizeBits = fromIntegral $ C.intValue (C.knownNat @SizeBits)
                let maxCount = R.App $ usizeLit (1 `shift` (sizeBits - 1))
                let countOk = R.App $ usizeLt count maxCount
                G.assertExpr countOk $ S.litExpr "count overflow in copy_nonoverlapping"

                -- If `maybeOffset` is Nothing, then src and dest definitely
                -- don't overlap, since they come from different allocations.
                -- If it's Just, the value must be >= count or <= -count to put
                -- the two regions far enough apart.
                let count' = usizeToIsize R.App count
                let destAbove = \offset -> R.App $ isizeLe count' offset
                let destBelow = \offset -> R.App $ isizeLe offset (R.App $ isizeNeg count')
                offsetOk <- G.caseMaybe maybeOffset C.BoolRepr $ G.MatchMaybe
                    (\offset -> return $ R.App $ E.Or (destAbove offset) (destBelow offset))
                    (return $ R.App $ E.BoolLit True)
                G.assertExpr offsetOk $ S.litExpr "src and dest overlap in copy_nonoverlapping"

                ptrCopy tpr src dest count
                return $ MirExp C.UnitRepr $ R.App E.EmptyApp

            _ -> mirFail $ "bad arguments for intrinsics::copy_nonoverlapping: " ++ show ops
        _ -> Nothing)

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
    ( ["core","intrinsics", "", "wrapping_add"]
    , makeOverflowingArith "wrapping_add" Add
    )

wrapping_sub ::  (ExplodedDefId, CustomRHS)
wrapping_sub =
    ( ["core","intrinsics", "", "wrapping_sub"]
    , makeOverflowingArith "wrapping_sub" Sub
    )

wrapping_mul ::  (ExplodedDefId, CustomRHS)
wrapping_mul =
    ( ["core","intrinsics", "", "wrapping_mul"]
    , makeOverflowingArith "wrapping_mul" Mul
    )


overflowResult :: C.TypeRepr tp ->
    R.Expr MIR s tp ->
    R.Expr MIR s C.BoolType ->
    MirGenerator h s ret (MirExp s)
overflowResult tpr value over = return $ buildTuple
    [ MirExp (C.MaybeRepr tpr) $ R.App $ E.JustValue tpr value
    , MirExp (C.MaybeRepr C.BoolRepr) $ R.App $ E.JustValue C.BoolRepr over
    ]

makeArithWithOverflow :: String -> Maybe Bool -> BinOp -> CustomRHS
makeArithWithOverflow name isSignedOverride bop =
    \(Substs [t]) -> Just $ CustomOp $ \_opTys ops -> case ops of
        [e1, e2] -> do
            let arithType = fmap (\s -> if s then Signed else Unsigned) $ isSigned t
            (result, overflow) <- evalBinOp bop arithType e1 e2
            case result of
                MirExp (C.BVRepr w) result' ->
                    overflowResult (C.BVRepr w) result' overflow
                MirExp tpr _ -> mirFail $
                    "bad return values from evalBinOp " ++ show bop ++ ": " ++ show tpr
        _ -> mirFail $ "bad arguments to " ++ name ++ ": " ++ show (t, ops)
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
    ( ["core","intrinsics", "", "add_with_overflow"]
    , makeArithWithOverflow "add_with_overflow" Nothing Add
    )

sub_with_overflow ::  (ExplodedDefId, CustomRHS)
sub_with_overflow =
    ( ["core","intrinsics", "", "sub_with_overflow"]
    , makeArithWithOverflow "sub_with_overflow" Nothing Sub
    )

mul_with_overflow ::  (ExplodedDefId, CustomRHS)
mul_with_overflow =
    ( ["core","intrinsics", "", "mul_with_overflow"]
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
saturateValueUnsigned w _ = Nothing

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
    ( ["core","intrinsics", "", "saturating_add"]
    , makeSaturatingArith "saturating_add" Add
    )

saturating_sub ::  (ExplodedDefId, CustomRHS)
saturating_sub =
    ( ["core","intrinsics", "", "saturating_sub"]
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
    ( ["core","intrinsics", "", "unchecked_add"]
    , makeUncheckedArith "unchecked_add" Add
    )

unchecked_sub ::  (ExplodedDefId, CustomRHS)
unchecked_sub =
    ( ["core","intrinsics", "", "unchecked_sub"]
    , makeUncheckedArith "unchecked_sub" Sub
    )

unchecked_mul ::  (ExplodedDefId, CustomRHS)
unchecked_mul =
    ( ["core","intrinsics", "", "unchecked_mul"]
    , makeUncheckedArith "unchecked_mul" Mul
    )

unchecked_div ::  (ExplodedDefId, CustomRHS)
unchecked_div =
    ( ["core","intrinsics", "", "unchecked_div"]
    , makeUncheckedArith "unchecked_div" Div
    )

unchecked_rem ::  (ExplodedDefId, CustomRHS)
unchecked_rem =
    ( ["core","intrinsics", "", "unchecked_rem"]
    , makeUncheckedArith "unchecked_rem" Rem
    )

unchecked_shl ::  (ExplodedDefId, CustomRHS)
unchecked_shl =
    ( ["core","intrinsics", "", "unchecked_shl"]
    , makeUncheckedArith "unchecked_shl" Shl
    )

unchecked_shr ::  (ExplodedDefId, CustomRHS)
unchecked_shr =
    ( ["core","intrinsics", "", "unchecked_shr"]
    , makeUncheckedArith "unchecked_shr" Shr
    )

-- Build a "count leading zeros" implementation.  The function will be
-- polymorphic, accepting bitvectors of any width.  The `NatRepr` is the width
-- of the output, or `Nothing` to return a bitvector of the same width as the
-- input.
ctlz_impl :: Text -> Maybe (Some NatRepr) -> CustomRHS
ctlz_impl name optFixedWidth _substs = Just $ CustomOp $ \_optys ops -> case ops of
    [MirExp (C.BVRepr w) v] -> case optFixedWidth of
        Nothing ->
            return $ MirExp (C.BVRepr w) $ S.app $ buildMux w w w v
        Just (Some w')
          | Just LeqProof <- isPosNat w' ->
            return $ MirExp (C.BVRepr w') $ S.app $ buildMux w w w' v
          | otherwise -> error $ "bad output width "++ show w' ++ " for ctlz_impl"
    _ -> mirFail $ "BUG: invalid arguments to " ++ Text.unpack name ++ ": " ++ show ops
  where
    getBit :: (1 <= w, i + 1 <= w) =>
        NatRepr w -> NatRepr i ->
        R.Expr MIR s (C.BVType w) ->
        E.App MIR (R.Expr MIR s) C.BoolType
    getBit w i bv =
        E.BVNonzero knownRepr $ R.App $
        E.BVSelect i (knownNat @1) w $ bv

    -- Build a mux tree that computes the number of leading zeros in `bv`,
    -- assuming that all bits at positions >= i are already known to be zero.
    -- The result is returned as a bitvector of width `w'`.
    buildMux :: (1 <= w, i <= w, 1 <= w') =>
        NatRepr w -> NatRepr i -> NatRepr w' ->
        R.Expr MIR s (C.BVType w) ->
        E.App MIR (R.Expr MIR s) (C.BVType w')
    buildMux w i w' bv = case isZeroNat i of
        ZeroNat ->
            -- Bits 0..w are all known to be zero.  There are `w` leading
            -- zeros.
            eBVLit w' $ intValue w
        NonZeroNat
          | i' <- predNat i
          , LeqProof <- addIsLeq i' (knownNat @1)
          , LeqProof <- leqTrans (leqProof i' i) (leqProof i w)
          -- Bits i..w are known to be zero, so inspect bit `i-1` next.
          -> E.BVIte (R.App $ getBit w i' bv) w'
                (R.App $ eBVLit w' $ intValue w - intValue i)
                (R.App $ buildMux w i' w' bv)

ctlz :: (ExplodedDefId, CustomRHS)
ctlz =
    ( ["core","intrinsics", "", "ctlz"]
    , ctlz_impl "ctlz" Nothing )

ctlz_nonzero :: (ExplodedDefId, CustomRHS)
ctlz_nonzero =
    ( ["core","intrinsics", "", "ctlz_nonzero"]
    , ctlz_impl "ctlz_nonzero" Nothing )

rotate_left :: (ExplodedDefId, CustomRHS)
rotate_left = ( ["core","intrinsics", "", "rotate_left"],
  \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp (C.BVRepr w) eVal, MirExp (C.BVRepr w') eAmt]
      | Just Refl <- testEquality w w' -> do
        return $ MirExp (C.BVRepr w) $ R.App $ E.BVRol w eVal eAmt
    _ -> mirFail $ "invalid arguments for rotate_left")

rotate_right :: (ExplodedDefId, CustomRHS)
rotate_right = ( ["core","intrinsics", "", "rotate_right"],
  \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp (C.BVRepr w) eVal, MirExp (C.BVRepr w') eAmt]
      | Just Refl <- testEquality w w' -> do
        return $ MirExp (C.BVRepr w) $ R.App $ E.BVRor w eVal eAmt
    _ -> mirFail $ "invalid arguments for rotate_right")


---------------------------------------------------------------------------------------
-- ** Custom ::intrinsics::discriminant_value

discriminant_value ::  (ExplodedDefId, CustomRHS)
discriminant_value = (["core","intrinsics", "", "discriminant_value"],
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
      case (opTys,ops) of
        ([TyRef (TyAdt nm _ _) Immut], [eRef]) -> do
            adt <- findAdt nm
            e <- derefExp eRef >>= readPlace
            MirExp IsizeRepr e' <- enumDiscriminant adt e
            return $ MirExp (C.BVRepr (knownRepr :: NatRepr 64)) $
                isizeToBv knownRepr R.App e'
        _ -> mirFail $ "BUG: invalid arguments for discriminant_value")

type_id ::  (ExplodedDefId, CustomRHS)
type_id = (["core","intrinsics", "", "type_id"],
  \ _substs -> Just $ CustomOp $ \ opTys ops ->
    -- TODO: keep a map from Ty to Word64, assigning IDs on first use of each type
    return $ MirExp knownRepr $ R.App (eBVLit (knownRepr :: NatRepr 64) 0))

size_of :: (ExplodedDefId, CustomRHS)
size_of = (["core", "intrinsics", "", "size_of"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ ->
        -- TODO: return the actual size, once mir-json exports size/layout info
        return $ MirExp UsizeRepr $ R.App $ usizeLit 1
    )

min_align_of :: (ExplodedDefId, CustomRHS)
min_align_of = (["core", "intrinsics", "", "min_align_of"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ _ ->
        -- TODO: return the actual alignment, once mir-json exports size/layout info
        return $ MirExp UsizeRepr $ R.App $ usizeLit 1
    )

-- mem::swap is used pervasively (both directly and via mem::replace), but it
-- has a nasty unsafe implementation, with lots of raw pointers and
-- reintepreting casts.  Fortunately, it requires `T: Sized`, so it's almost
-- trivial to implement as a custom op.
mem_swap ::  (ExplodedDefId, CustomRHS)
mem_swap = (["core","mem", "swap"],
    \ _substs -> Just $ CustomOp $ \ opTys ops -> case ops of
        [MirExp (MirReferenceRepr ty1) e1, MirExp (MirReferenceRepr ty2) e2]
          | Just Refl <- testEquality ty1 ty2 -> do
            val1 <- readMirRef ty1 e1
            val2 <- readMirRef ty2 e2
            writeMirRef e1 val2
            writeMirRef e2 val1
            return $ MirExp knownRepr $ R.App E.EmptyApp
        _ -> mirFail $ "bad arguments to mem_swap: " ++ show (opTys, ops)
    )


-- This is like normal mem::transmute, but requires source and target types to
-- have identical Crucible `TypeRepr`s.
mem_crucible_identity_transmute ::  (ExplodedDefId, CustomRHS)
mem_crucible_identity_transmute = (["core","mem", "crucible_identity_transmute"],
    \ substs -> case substs of
      Substs [tyT, tyU] -> Just $ CustomOp $ \ _ ops -> case ops of
        [e@(MirExp argTy _)] -> do
            Some retTy <- tyToReprM tyU
            case testEquality argTy retTy of
                Just refl -> return e
                Nothing -> mirFail $ "crucible_identity_transmute: types are not compatible: " ++
                    show (tyT, argTy) ++ " != " ++ show (tyU, retTy)
        _ -> mirFail $ "bad arguments to mem_crucible_identity_transmute: "
          ++ show (tyT, tyU, ops)
      _ -> Nothing
    )

mem_bswap ::  (ExplodedDefId, CustomRHS)
mem_bswap = (["core", "intrinsics", "", "bswap"],
    \ substs -> case substs of
      Substs [tyT] -> Just $ CustomOp $ \ _ ops -> case ops of
        [e@(MirExp argTy@C.BVRepr{} argExpr)] -> return . MirExp argTy $ bswap argTy argExpr
        _ -> mirFail $ "bswap expected `BVRepr w` but got: " ++ show (tyT, ops)
      _ -> Nothing)
  where
    zero = knownNat @0
    byte = knownNat @8
    bswap :: C.TypeRepr (C.BVType w) -> R.Expr MIR s (C.BVType w) -> R.Expr MIR s (C.BVType w)
    bswap (C.BVRepr w) bv
        | Just Refl <- testEquality byte w = bv -- 8 ≡ w
        | 0 <- natValue w `mod` natValue byte               -- 0 ≡ w%8
        , Just (byteLEw@LeqProof) <- testLeq byte w         -- 8 ≤ w
        , Left (byteLTw@LeqProof) <- testStrictLeq byte w = -- 8+1 ≤ w
            let xsw = subNat w byte in -- size of int sans one byte
            withLeqProof (leqSub (leqRefl w) byteLEw) $     -- w-8 ≤ w
            withLeqProof (leqSub2 byteLTw (leqRefl byte)) $ -- 1 ≤ w-8
            let xs = R.App $ E.BVSelect zero xsw w bv in -- int sans least significant byte
            gcastWith (minusPlusCancel w byte) $            -- (w-8)+8 ≡ w
            let x = R.App $ E.BVSelect xsw byte w bv in -- least significant byte
            gcastWith (plusComm xsw byte) $                 -- 8+(w-8) ≡ w
            R.App $ E.BVConcat byte xsw x (bswap (C.BVRepr xsw) xs)
        | otherwise = panic "bswap" ["`BVRepr w` must satisfy `8 ≤ w ∧ w%8 ≡ 0`"]

mem_transmute ::  (ExplodedDefId, CustomRHS)
mem_transmute = (["core", "intrinsics", "", "transmute"],
    \ substs -> case substs of
      Substs [tyT, tyU] -> Just $ CustomOp $ \ _ ops -> case ops of
        [e@(MirExp argTy argExpr)] -> do
          Some retTy <- tyToReprM tyU
          case (argTy, retTy) of
            -- Splitting an integer into pieces (usually bytes)
            (C.BVRepr w1, MirVectorRepr (C.BVRepr w2))
              | natValue w1 `mod` natValue w2 == 0 -> do
                let n = natValue w1 `div` natValue w2
                pieces <- forM [0 .. n - 1] $ \i -> do
                  Some i' <- return $ mkNatRepr i
                  let offset = natMultiply i' w2
                  LeqProof <- case testLeq (addNat offset w2) w1 of
                    Just x -> return x
                    Nothing -> panic "transmute" ["impossible: (w1 / w2 - 1) * w2 + w2 > w1?"]
                  return $ R.App $ E.BVSelect (natMultiply i' w2) w2 w1 argExpr
                let v = R.App $ E.VectorLit (C.BVRepr w2) (V.fromList pieces)
                mv <- mirVector_fromVector (C.BVRepr w2) v
                return $ MirExp retTy mv

            -- Reconstructing an integer from pieces (usually bytes)
            (MirVectorRepr (C.BVRepr w1), C.BVRepr w2)
              | natValue w2 `mod` natValue w1 == 0 -> do
                let n = natValue w2 `div` natValue w1
                vecRef <- constMirRef (MirVectorRepr (C.BVRepr w1)) argExpr
                pieces <- forM [0 .. n - 1] $ \i -> do
                  let idx = R.App $ usizeLit (fromIntegral i)
                  elemRef <- subindexRef (C.BVRepr w1) vecRef idx
                  readMirRef (C.BVRepr w1) elemRef
                let go :: (1 <= wp) =>
                      NatRepr wp ->
                      [R.Expr MIR s (C.BVType wp)] ->
                      (forall wr. (1 <= wr) => NatRepr wr -> R.Expr MIR s (C.BVType wr) -> a) ->
                      a
                    go _ [] _ = panic "transmute" ["impossible: w2/w1 == 0?"]
                    go wp [x] k = k wp x
                    go wp (x:xs) k = go wp xs (\wr rest ->
                      case leqAdd (leqProof (knownNat @1) wr) wp of
                        LeqProof -> k (addNat wr wp) (R.App $ E.BVConcat wr wp rest x))
                concatExpr <- go w1 pieces $ \wr result -> do
                  Refl <- case testEquality wr w2 of
                    Just x -> return x
                    Nothing -> panic "transmute" ["impossible: w1 * (w2/w1) != w2?"]
                  return result
                return $ MirExp retTy concatExpr

            -- Transmuting between values of the same Crucible repr
            _ | Just Refl <- testEquality argTy retTy -> return e

            _ -> mirFail $
              "can't transmute " ++ show argTy ++ " to " ++ show retTy
        _ -> mirFail $ "bad arguments to transmute: "
          ++ show (tyT, tyU, ops)
      _ -> Nothing)
  where
    sizeBytes sz = case sz of
      USize -> intValue (knownNat @SizeBits) `div` 8
      B8 -> 1
      B16 -> 2
      B32 -> 4
      B64 -> 8
      B128 -> 16

intrinsics_assume :: (ExplodedDefId, CustomRHS)
intrinsics_assume = (["core", "intrinsics", "", "assume"], \_substs ->
    Just $ CustomOp $ \_ ops -> case ops of
        [MirExp C.BoolRepr cond] -> do
            G.assertExpr cond $
                S.litExpr "undefined behavior: core::intrinsics::assume(false)"
            return $ MirExp C.UnitRepr $ R.App E.EmptyApp
    )

-- TODO: needs layout info from mir-json
assert_inhabited :: (ExplodedDefId, CustomRHS)
assert_inhabited = (["core", "intrinsics", "", "assert_inhabited"], \_substs ->
    Just $ CustomOp $ \_ _ -> return $ MirExp C.UnitRepr $ R.App E.EmptyApp)

array_from_slice ::  (ExplodedDefId, CustomRHS)
array_from_slice = (["core","array", "{{impl}}", "try_from", "crucible_array_from_slice_hook"],
    \substs -> Just $ CustomOpNamed $ \fnName ops -> do
        fn <- findFn fnName
        case (fn ^. fsig . fsreturn_ty, ops) of
            ( TyAdt optionMonoName _ (Substs [TyRef (TyArray ty _) Immut]),
              [MirExp (MirSliceRepr tpr) e, MirExp UsizeRepr eLen] ) -> do
                -- TODO: This should be implemented as a type cast, so the
                -- input and output are aliases.  However, the input slice is a
                -- MirVector, while the output must be a plain crucible Vector.
                -- We don't currently have a way to do that downcast, so we use
                -- `vectorCopy` instead.
                let ptr = getSlicePtr e
                let len = getSliceLen e
                let lenOk = R.App $ usizeEq len eLen
                -- Get the Adt info for the return type, which should be
                -- Option<&[T; N]>.
                adt <- findAdt optionMonoName

                MirExp C.AnyRepr <$> G.ifte lenOk
                    (do v <- vectorCopy tpr ptr len
                        v' <- mirVector_fromVector tpr v
                        ref <- constMirRef (MirVectorRepr tpr) v'
                        let vMir = MirExp (MirReferenceRepr (MirVectorRepr tpr)) ref
                        enum <- buildEnum adt optionDiscrSome [vMir]
                        unwrapMirExp C.AnyRepr enum)
                    (do enum <- buildEnum adt optionDiscrNone []
                        unwrapMirExp C.AnyRepr enum)

            _ -> mirFail $ "bad monomorphization of crucible_array_from_slice_hook: " ++
                show (fnName, fn ^. fsig, ops)
    )



-------------------------------------------------------------------------------------------------------
-- ** Custom: slice impl functions
--

slice_len :: (ExplodedDefId, CustomRHS)
slice_len =
  (["core","slice","{{impl}}","len", "crucible_slice_len_hook"]
  , \(Substs [_]) -> Just $ CustomOp $ \ _optys ops -> 
     case ops of 
       [MirExp (MirSliceRepr _) e] -> do
            return $ MirExp UsizeRepr $ getSliceLen e
       _ -> mirFail $ "BUG: invalid arguments to " ++ "slice_len")

-- These four custom ops implement mutable and immutable unchecked indexing by
-- usize and by Range.  All other indexing dispatches to one of these.  Note
-- the use of inner `crucible_hook` functions - otherwise we can't distinguish
-- the `fn get_unchecked` in the impl for usize from the `fn get_unchecked` in
-- the impl for Range.

slice_index_usize_get_unchecked_impl :: CustomRHS
slice_index_usize_get_unchecked_impl (Substs [_elTy]) =
    Just $ CustomOp $ \ optys ops -> case ops of
        [MirExp UsizeRepr ind, MirExp (MirSliceRepr el_tp) slice] -> do
            let ptr = getSlicePtr slice
            let len = getSliceLen slice
            ptr' <- mirRef_offset el_tp ptr ind
            return $ (MirExp (MirReferenceRepr el_tp) ptr')
        _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
slice_index_usize_get_unchecked_impl _ = Nothing

slice_index_usize_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked =
    ( ["core","slice","{{impl}}","get_unchecked", "crucible_hook_usize"]
    , slice_index_usize_get_unchecked_impl )

slice_index_usize_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_index_usize_get_unchecked_mut =
    ( ["core","slice","{{impl}}","get_unchecked_mut", "crucible_hook_usize"]
    , slice_index_usize_get_unchecked_impl )

slice_index_range_get_unchecked_impl :: CustomRHS
slice_index_range_get_unchecked_impl (Substs [_elTy]) =
    Just $ CustomOp $ \ optys ops -> case ops of
        [ MirExp tr1 start, MirExp tr2 end, MirExp (MirSliceRepr tpr) slice]
          | Just Refl <- testEquality tr1 UsizeRepr
          , Just Refl <- testEquality tr2 UsizeRepr
          -> do
            let ptr = getSlicePtr slice
            let len = getSliceLen slice
            ptr' <- mirRef_offset tpr ptr start
            let len' = S.app $ usizeSub end start
            return $ MirExp (MirSliceRepr tpr) $ mkSlice tpr ptr' len'

        _ -> mirFail $ "BUG: invalid arguments to slice_get_unchecked_mut: " ++ show ops
slice_index_range_get_unchecked_impl _ = Nothing

slice_index_range_get_unchecked :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked =
    ( ["core","slice","{{impl}}","get_unchecked", "crucible_hook_range"]
    , slice_index_range_get_unchecked_impl )

slice_index_range_get_unchecked_mut :: (ExplodedDefId, CustomRHS)
slice_index_range_get_unchecked_mut =
    ( ["core","slice","{{impl}}","get_unchecked_mut", "crucible_hook_range"]
    , slice_index_range_get_unchecked_impl )

--------------------------------------------------------------------------------------------------------------------------
-- ** Custom: Integer

integerWidth = knownNat :: NatRepr 512

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

integerFromUnsigned :: CustomRHS
integerFromUnsigned (Substs []) =
    let w' = integerWidth in
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w) int_e] | Just LeqProof <- testLeq (incNat w) w' ->
            return $ MirExp (C.BVRepr w') (S.app $ E.BVZext w' w int_e)
        _ -> mirFail $ "BUG: invalid arguments to integerFromUnsigned: " ++ show ops


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


integer_shl :: (ExplodedDefId, CustomRHS)
integer_shl = (["int512", "shl"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') val_e, MirExp (C.BVRepr w) amt_e]
          | Just LeqProof <- testLeq (incNat w) w' ->
            let amt_e' = S.app $ E.BVZext w' w amt_e in
            return $ MirExp (C.BVRepr w') (S.app $ E.BVShl w' val_e amt_e')
        _ -> mirFail $ "BUG: invalid arguments to integer_shl: " ++ show ops
    )

integer_shr :: (ExplodedDefId, CustomRHS)
integer_shr = (["int512", "shr"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w') val_e, MirExp (C.BVRepr w) amt_e]
          | Just LeqProof <- testLeq (incNat w) w' ->
            let amt_e' = S.app $ E.BVZext w' w amt_e in
            return $ MirExp (C.BVRepr w') (S.app $ E.BVLshr w' val_e amt_e')
        _ -> mirFail $ "BUG: invalid arguments to integer_shr: " ++ show ops
    )

integer_bitand :: (ExplodedDefId, CustomRHS)
integer_bitand = (["int512", "bitand"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVAnd w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_bitand: " ++ show ops
    )

integer_bitor :: (ExplodedDefId, CustomRHS)
integer_bitor = (["int512", "bitor"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVOr w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_bitor: " ++ show ops
    )

integer_eq :: (ExplodedDefId, CustomRHS)
integer_eq = (["int512", "eq"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp C.BoolRepr (S.app $ E.BVEq w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_eq: " ++ show ops
    )

integer_lt :: (ExplodedDefId, CustomRHS)
integer_lt = (["int512", "lt"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp C.BoolRepr (S.app $ E.BVSlt w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_lt: " ++ show ops
    )

integer_add :: (ExplodedDefId, CustomRHS)
integer_add = (["int512", "add"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVAdd w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_add: " ++ show ops
    )

integer_sub :: (ExplodedDefId, CustomRHS)
integer_sub = (["int512", "sub"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVSub w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_sub: " ++ show ops
    )

integer_rem :: (ExplodedDefId, CustomRHS)
integer_rem = (["int512", "rem"], \(Substs []) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) val1_e, MirExp (C.BVRepr w2) val2_e]
          | Just Refl <- testEquality w1 w2 ->
            return $ MirExp (C.BVRepr w1) (S.app $ E.BVSrem w1 val1_e val2_e)
        _ -> mirFail $ "BUG: invalid arguments to integer_rem: " ++ show ops
    )


--------------------------------------------------------------------------------------------------------------------------
-- crucible::bitvector::Bv implementation

bv_convert :: (ExplodedDefId, CustomRHS)
bv_convert = (["crucible", "bitvector", "convert"], \(Substs [_, u]) ->
    Just $ CustomOp $ \_optys ops -> do
        col <- use $ cs . collection
        impl col u ops)
  where
    impl :: HasCallStack => Collection -> Ty -> [MirExp s] -> MirGenerator h s ret (MirExp s) 
    impl col u ops
      | [MirExp (C.BVRepr w1) v] <- ops
      , Some (C.BVRepr w2) <- tyToRepr col u
      = case compareNat w1 w2 of
            NatLT _ -> return $ MirExp (C.BVRepr w2) $
                S.app $ E.BVZext w2 w1 v
            NatGT _ -> return $ MirExp (C.BVRepr w2) $
                S.app $ E.BVTrunc w2 w1 v
            NatEQ -> return $ MirExp (C.BVRepr w2) v
      | otherwise = mirFail $
        "BUG: invalid arguments to bv_convert: " ++ show ops

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
bv_unop name op = (["crucible", "bitvector", "{{impl}}", name], \(Substs [_sz]) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (C.BVRepr w1) v1] ->
            return $ MirExp (C.BVRepr w1) (S.app $ op w1 v1)
        _ -> mirFail $ "BUG: invalid arguments to bv_" ++ Text.unpack name ++ ": " ++ show ops
    )

type BVBinOp = forall ext f w. (1 <= w)
        => (NatRepr w)
        -> (f (C.BVType w))
        -> (f (C.BVType w))
        -> E.App ext f (C.BVType w)

bv_binop :: Text -> BVBinOp -> (ExplodedDefId, CustomRHS)
bv_binop name op = (["crucible", "bitvector", "{{impl}}", name], bv_binop_impl name op)

bv_binop_impl :: Text -> BVBinOp -> CustomRHS
bv_binop_impl name op (Substs [_sz]) = Just $ CustomOp $ \_optys ops -> case ops of
    [MirExp (C.BVRepr w1) v1, MirExp (C.BVRepr w2) v2]
      | Just Refl <- testEquality w1 w2 ->
        return $ MirExp (C.BVRepr w1) (S.app $ op w1 v1 v2)
    _ -> mirFail $ "BUG: invalid arguments to bv_" ++ Text.unpack name ++ ": " ++ show ops

bv_shift_op :: Text -> BVBinOp -> (ExplodedDefId, CustomRHS)
bv_shift_op name op = (["crucible", "bitvector", name], bv_binop_impl name op)

bv_overflowing_binop :: Text -> BinOp -> (ExplodedDefId, CustomRHS)
bv_overflowing_binop name bop =
    ( ["crucible", "bitvector", "{{impl}}", "overflowing_" <> name]
    , makeArithWithOverflow ("bv_overflowing_" ++ Text.unpack name) (Just False) bop
    )

bv_eq :: (ExplodedDefId, CustomRHS)
bv_eq = (["crucible", "bitvector", "{{impl}}", "eq"], \(Substs [_sz]) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (MirReferenceRepr (C.BVRepr w1)) r1, MirExp (MirReferenceRepr (C.BVRepr w2)) r2]
          | Just Refl <- testEquality w1 w2 -> do
            v1 <- readMirRef (C.BVRepr w1) r1
            v2 <- readMirRef (C.BVRepr w2) r2
            return $ MirExp C.BoolRepr $ S.app $ E.BVEq w1 v1 v2
        _ -> mirFail $ "BUG: invalid arguments to bv_eq: " ++ show ops)

bv_lt :: (ExplodedDefId, CustomRHS)
bv_lt = (["crucible", "bitvector", "{{impl}}", "lt"], \(Substs [_sz]) ->
    Just $ CustomOp $ \_optys ops -> case ops of
        [MirExp (MirReferenceRepr (C.BVRepr w1)) r1, MirExp (MirReferenceRepr (C.BVRepr w2)) r2]
          | Just Refl <- testEquality w1 w2 -> do
            v1 <- readMirRef (C.BVRepr w1) r1
            v2 <- readMirRef (C.BVRepr w2) r2
            return $ MirExp C.BoolRepr $ S.app $ E.BVUlt w1 v1 v2
        _ -> mirFail $ "BUG: invalid arguments to bv_lt: " ++ show ops)

type BVMakeLiteral = forall ext f w.
    (1 <= w) => NatRepr w -> E.App ext f (C.BVType w)

bv_literal :: Text -> BVMakeLiteral -> (ExplodedDefId, CustomRHS)
bv_literal name op = (["crucible", "bitvector", "{{impl}}", name], \(Substs [sz]) ->
    Just $ CustomOp $ \_optys _ops -> tyToReprM (CTyBv sz) >>= \(Some tpr) -> case tpr of
        C.BVRepr w ->
            return $ MirExp (C.BVRepr w) $ S.app $ op w
        _ -> mirFail $
            "BUG: invalid type param for bv_" ++ Text.unpack name ++ ": " ++ show sz)

bv_leading_zeros :: (ExplodedDefId, CustomRHS)
bv_leading_zeros =
    ( ["crucible", "bitvector", "{{impl}}", "leading_zeros"]
    , ctlz_impl "bv_leading_zeros" (Just $ Some $ knownNat @32) )



--------------------------------------------------------------------------------------------------------------------------
-- crucible::alloc implementation

-- fn allocate<T>(len: usize) -> *mut T
allocate :: (ExplodedDefId, CustomRHS)
allocate = (["crucible", "alloc", "allocate"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp UsizeRepr len] -> do
            -- Create an uninitialized `MirVector_PartialVector` of length
            -- `len`, and return a pointer to its first element.
            Some tpr <- tyToReprM t
            vec <- mirVector_uninit tpr len
            ref <- newMirRef (MirVectorRepr tpr)
            writeMirRef ref vec
            -- `subindexRef` doesn't do a bounds check (those happen on deref
            -- instead), so this works even when len is 0.
            ptr <- subindexRef tpr ref (R.App $ usizeLit 0)
            return $ MirExp (MirReferenceRepr tpr) ptr
        _ -> mirFail $ "BUG: invalid arguments to allocate: " ++ show ops
    _ -> Nothing)

allocate_zeroed :: (ExplodedDefId, CustomRHS)
allocate_zeroed = (["crucible", "alloc", "allocate_zeroed"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [MirExp UsizeRepr len] -> do
            Some tpr <- tyToReprM t
            zero <- mkZero tpr
            let lenNat = R.App $ usizeToNat len
            let vec = R.App $ E.VectorReplicate tpr lenNat zero
            vec <- mirVector_fromVector tpr vec

            ref <- newMirRef (MirVectorRepr tpr)
            writeMirRef ref vec
            ptr <- subindexRef tpr ref (R.App $ usizeLit 0)
            return $ MirExp (MirReferenceRepr tpr) ptr
        _ -> mirFail $ "BUG: invalid arguments to allocate: " ++ show ops
    _ -> Nothing)

mkZero :: C.TypeRepr tp -> MirGenerator h s ret (R.Expr MIR s tp)
mkZero tpr@(C.BVRepr w) = return $ R.App $ eBVLit w 0
mkZero tpr = mirFail $ "don't know how to zero-initialize " ++ show tpr

-- fn reallocate<T>(ptr: *mut T, new_len: usize)
reallocate :: (ExplodedDefId, CustomRHS)
reallocate = (["crucible", "alloc", "reallocate"], \substs -> case substs of
    Substs [t] -> Just $ CustomOp $ \_ ops -> case ops of
        [ MirExp (MirReferenceRepr tpr) ptr, MirExp UsizeRepr newLen ] -> do
            (vecPtr, idx) <- mirRef_peelIndex tpr ptr

            let isZero = R.App $ usizeEq idx $ R.App $ usizeLit 0
            G.assertExpr isZero $
                S.litExpr "bad pointer in reallocate: not the start of an allocation"

            oldVec <- readMirRef (MirVectorRepr tpr) vecPtr
            newVec <- mirVector_resize tpr oldVec newLen
            writeMirRef vecPtr newVec
            return $ MirExp C.UnitRepr $ R.App E.EmptyApp
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
    [(["core", "intrinsics", "", "atomic_" <> name <> suffix], rhs)
        | suffix <- "" : map ("_" <>) variants]

atomic_store_impl :: CustomRHS
atomic_store_impl = \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp (MirReferenceRepr tpr) ref, MirExp tpr' val]
      | Just Refl <- testEquality tpr tpr' -> do
        writeMirRef ref val
        return $ MirExp C.UnitRepr $ R.App E.EmptyApp
    _ -> mirFail $ "BUG: invalid arguments to atomic_store: " ++ show ops

atomic_load_impl :: CustomRHS
atomic_load_impl = \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [MirExp (MirReferenceRepr tpr) ref] ->
        MirExp tpr <$> readMirRef tpr ref
    _ -> mirFail $ "BUG: invalid arguments to atomic_load: " ++ show ops

atomic_cxchg_impl :: CustomRHS
atomic_cxchg_impl = \_substs -> Just $ CustomOp $ \opTys ops -> case (opTys, ops) of
    ([_, ty, _], [MirExp (MirReferenceRepr tpr) ref, MirExp tpr' expect, MirExp tpr'' val])
      | Just Refl <- testEquality tpr tpr'
      , Just Refl <- testEquality tpr tpr''
      , C.BVRepr w <- tpr -> do
        old <- readMirRef tpr ref
        let eq = R.App $ E.BVEq w old expect
        let new = R.App $ E.BVIte eq w val old
        writeMirRef ref new
        buildTupleMaybeM [ty, TyBool] $
            [Just $ MirExp tpr old, Just $ MirExp C.BoolRepr eq]
    _ -> mirFail $ "BUG: invalid arguments to atomic_cxchg: " ++ show ops

atomic_fence_impl :: CustomRHS
atomic_fence_impl = \_substs -> Just $ CustomOp $ \_ ops -> case ops of
    [] -> return $ MirExp C.UnitRepr $ R.App E.EmptyApp
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
    [MirExp (MirReferenceRepr tpr) ref, MirExp tpr' val]
      | Just Refl <- testEquality tpr tpr'
      , C.BVRepr w <- tpr -> do
        old <- readMirRef tpr ref
        new <- rmw w old val
        writeMirRef ref new
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
    makeAtomicIntrinsics (Text.pack name) ["acq", "rel", "acqrel", "relaxed"] $
        atomic_rmw_impl name rmw

atomic_funcs =
    makeAtomicIntrinsics "store" ["rel", "relaxed"] atomic_store_impl ++
    makeAtomicIntrinsics "load" ["acq", "relaxed"] atomic_load_impl ++
    makeAtomicIntrinsics "cxchg" compareExchangeVariants atomic_cxchg_impl ++
    makeAtomicIntrinsics "cxchgweak" compareExchangeVariants atomic_cxchg_impl ++
    makeAtomicIntrinsics "fence" fenceVariants atomic_fence_impl ++
    makeAtomicIntrinsics "singlethreadfence" fenceVariants atomic_fence_impl ++
    concat [
        makeAtomicRMW "xchg" $ \w old val -> return val,
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
    compareExchangeVariants = ["acq", "rel", "acqrel", "relaxed",
        "acq_failrelaxed", "acqrel_failrelaxed", "failrelaxed", "failacq"]
    fenceVariants = ["acq", "rel", "acqrel"]


--------------------------------------------------------------------------------------------------------------------------
-- MaybeUninit

maybe_uninit_uninit :: (ExplodedDefId, CustomRHS)
maybe_uninit_uninit = (["core", "mem", "maybe_uninit", "{{impl}}", "uninit"],
    \substs -> case substs of
        Substs [t] -> Just $ CustomOp $ \_ _ -> do
            adt <- findAdtInst (M.textId "core::mem::maybe_uninit::MaybeUninit") (Substs [t])
            let t = TyAdt (adt ^. adtname) (adt ^. adtOrigDefId) (adt ^. adtOrigSubsts)
            initialValue t >>= \mv -> case mv of
                Just v -> return v
                Nothing -> mirFail $ "MaybeUninit::uninit unsupported for " ++ show t
        _ -> Nothing)


--------------------------------------------------------------------------------------------------------------------------
-- Implementation for `IkFnPtrShim`.  Function pointer shims are auto-generated
-- `Fn`/`FnMut`/`FnOnce` methods for `TyFnDef` and `TyFnPtr`, allowing ordinary
-- functions to be passed as closures.


fnPtrShimDef :: Ty -> CustomOp
fnPtrShimDef (TyFnDef defId) = CustomMirOp $ \ops -> case ops of
    [_fnptr, argTuple] -> do
        argTys <- case typeOf argTuple of
            TyTuple tys -> return $ tys
            ty -> mirFail $ "unexpected argument tuple type " ++ show ty ++
                " for fnptr shim of " ++ show defId
        argBase <- case argTuple of
            Copy lv -> return lv
            Move lv -> return lv
            _ -> mirFail $ "unsupported argument tuple operand " ++ show argTuple ++
                " for fnptr shim of " ++ show defId
        let argOps = zipWith (\ty i -> Move $ LProj argBase (PField i ty)) argTys [0..]
        callExp defId argOps
    _ -> mirFail $ "unexpected arguments " ++ show ops ++ " for fnptr shim of " ++ show defId
fnPtrShimDef ty = CustomOp $ \_ _ -> mirFail $ "fnPtrShimDef not implemented for " ++ show ty


--------------------------------------------------------------------------------------------------------------------------
-- Implementations for `IkCloneShim`.  Clone shims are auto-generated `clone`
-- and `clone_from` implementations for tuples and arrays.  They dispatch to
-- the `clone`/`clone_from` methods of the individual fields or array elements.

cloneShimDef :: Ty -> [M.DefId] -> CustomOp
cloneShimDef (TyTuple tys) parts = CustomMirOp $ \ops -> do
    when (length tys /= length parts) $ mirFail "cloneShimDef: expected tys and parts to match"
    lv <- case ops of
        [Move lv] -> return lv
        [Copy lv] -> return lv
        [op] -> mirFail $ "cloneShimDef: expected lvalue operand, but got " ++ show op
        _ -> mirFail $ "cloneShimDef: expected exactly one argument, but got " ++ show (length ops)
    -- The argument to the clone shim is `&(A, B, C)`.  The clone methods for
    -- the individual parts require `&A`, `&B`, `&C`, computed as `&arg.0`.
    let fieldRefRvs = zipWith (\ty i ->
            Ref Shared (LProj (LProj lv Deref) (PField i ty)) "_") tys [0..]
    fieldRefExps <- mapM evalRval fieldRefRvs
    fieldRefOps <- zipWithM (\ty exp -> makeTempOperand (TyRef ty Immut) exp) tys fieldRefExps
    clonedExps <- zipWithM (\part op -> callExp part [op]) parts fieldRefOps
    buildTupleMaybeM tys (map Just clonedExps)
cloneShimDef (TyArray ty len) parts
  | [part] <- parts = CustomMirOp $ \ops -> do
    lv <- case ops of
        [Move lv] -> return lv
        [Copy lv] -> return lv
        [op] -> mirFail $ "cloneShimDef: expected lvalue operand, but got " ++ show op
        _ -> mirFail $ "cloneShimDef: expected exactly one argument, but got " ++ show (length ops)
    -- The argument to the clone shim is `&[T; n]`.  The clone method for
    -- elements requires `&T`, computed as `&arg[i]`.
    let elementRefRvs = map (\i ->
            Ref Shared (LProj (LProj lv Deref) (ConstantIndex i len False)) "_") [0 .. len - 1]
    elementRefExps <- mapM evalRval elementRefRvs
    elementRefOps <- mapM (\exp -> makeTempOperand (TyRef ty Immut) exp) elementRefExps
    clonedExps <- mapM (\op -> callExp part [op]) elementRefOps
    Some tpr <- tyToReprM ty
    buildArrayLit tpr clonedExps
  | otherwise = CustomOp $ \_ _ -> mirFail $
    "expected exactly one clone function for in array clone shim, but got " ++ show parts
cloneShimDef ty parts = CustomOp $ \_ _ -> mirFail $ "cloneShimDef not implemented for " ++ show ty

cloneFromShimDef :: Ty -> [M.DefId] -> CustomOp
cloneFromShimDef ty parts = CustomOp $ \_ _ -> mirFail $ "cloneFromShimDef not implemented for " ++ show ty


--------------------------------------------------------------------------------------------------------------------------

unwrapMirExp :: C.TypeRepr tp -> MirExp s -> MirGenerator h s ret (R.Expr MIR s tp)
unwrapMirExp tpr (MirExp tpr' e)
  | Just Refl <- testEquality tpr tpr' = return e
  | otherwise = mirFail $ "bad unwrap of MirExp: expected " ++ show tpr ++
    ", but got " ++ show tpr'

-- Convert a Crucible `MaybeType` into a Rust `Option`.
--
-- The caller is responsible for ensuring that `Option<T>` exists in the crate.
maybeToOption :: Ty -> C.TypeRepr tp -> R.Expr MIR s (C.MaybeType tp) ->
    MirGenerator h s ret (MirExp s)
maybeToOption ty tpr e = do
    adt <- findAdtInst optionDefId (Substs [ty])
    e' <- G.caseMaybe e C.AnyRepr $ G.MatchMaybe
        (\val -> buildEnum adt optionDiscrSome [MirExp tpr val] >>= unwrapMirExp C.AnyRepr)
        (buildEnum adt optionDiscrNone [] >>= unwrapMirExp C.AnyRepr)
    return $ MirExp C.AnyRepr e'
