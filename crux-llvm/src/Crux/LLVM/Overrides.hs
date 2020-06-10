{-# LANGUAGE FlexibleContexts #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language ImplicitParams #-}
{-# Language LambdaCase #-}
{-# Language PatternSynonyms #-}
{-# Language QuasiQuotes #-}
{-# Language RankNTypes #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language ViewPatterns #-}
module Crux.LLVM.Overrides
  ( cruxLLVMOverrides
  , svCompOverrides
  , cbmcOverrides
  , ArchOk
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Control.Lens((%=))
import Control.Monad.IO.Class(liftIO)
import System.IO (hPutStrLn)
import qualified Data.Text as T

import qualified Data.BitVector.Sized as BV
import Data.Parameterized.Context.Unsafe (Assignment)
import Data.Parameterized.Context(pattern Empty, pattern (:>), singleton)

import What4.ProgramLoc( Position(..), ProgramLoc(..) )
import What4.Symbol(userSymbol, emptySymbol)
import What4.Interface
          (freshConstant, bvLit, bvAdd, asBV, predToBV,
          getCurrentProgramLoc, printSymExpr, arrayUpdate, bvIsNonzero)
import What4.InterpretedFloatingPoint (freshFloatConstant, iFloatBaseTypeRepr)

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(GlobalVar)
import Lang.Crucible.Simulator.RegMap(regValue,RegValue,RegEntry)
import Lang.Crucible.Simulator.ExecutionTree
  ( stateContext, cruciblePersonality, printHandle )
import Lang.Crucible.Simulator.OverrideSim
        ( getSymInterface
        , getContext
        , readGlobal
        , writeGlobal
        )
import Lang.Crucible.Simulator.SimError (SimErrorReason(..),SimError(..))
import Lang.Crucible.Backend
          ( IsSymInterface, addDurableAssertion, addFailedAssertion
          , addAssumption, LabeledPred(..), AssumptionReason(..))
import Lang.Crucible.LLVM.QQ( llvmOvr )
import Lang.Crucible.LLVM.DataLayout
  (noAlignment)
import Lang.Crucible.LLVM.MemModel
  (Mem, LLVMPointerType, loadString, HasPtrWidth,
   doMalloc, AllocType(HeapAlloc), Mutability(Mutable),
   doArrayStore, doArrayConstStore, HasLLVMAnn,
   isAllocatedAlignedPointer, Mutability(..),
   pattern PtrWidth
   )

import           Lang.Crucible.LLVM.TypeContext( TypeContext )
import           Lang.Crucible.LLVM.Intrinsics

import Lang.Crucible.LLVM.Extension(ArchWidth)

import Crux.Types
import Crux.Model

-- | This happens quite a lot, so just a shorter name
type ArchOk arch    = HasPtrWidth (ArchWidth arch)
type TPtr arch      = LLVMPointerType (ArchWidth arch)
type TBits n        = BVType n


cruxLLVMOverrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [OverrideTemplate (Model sym) sym arch rtp l a]
cruxLLVMOverrides =
  [ basic_llvm_override $
        [llvmOvr| i8 @crucible_int8_t( i8* ) |]
        (fresh_bits (knownNat @8))

  , basic_llvm_override $
        [llvmOvr| i16 @crucible_int16_t( i8* ) |]
        (fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i32 @crucible_int32_t( i8* ) |]
        (fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i64 @crucible_int64_t( i8* ) |]
        (fresh_bits (knownNat @64))

  , basic_llvm_override $
        [llvmOvr| i8 @crucible_uint8_t( i8* ) |]
        (fresh_bits (knownNat @8))

  , basic_llvm_override $
        [llvmOvr| i16 @crucible_uint16_t( i8* ) |]
        (fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i32 @crucible_uint32_t( i8* ) |]
        (fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i64 @crucible_uint64_t( i8* ) |]
        (fresh_bits (knownNat @64))

  , basic_llvm_override $
        [llvmOvr| float @crucible_float( i8* ) |]
        (fresh_float SingleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| double @crucible_double( i8* ) |]
        (fresh_float DoubleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| i8* @crucible_string( i8*, size_t ) |]
        fresh_str

  , basic_llvm_override $
        [llvmOvr| void @crucible_assume( i8, i8*, i32 ) |]
        do_assume

  , basic_llvm_override $
        [llvmOvr| void @crucible_assert( i8, i8*, i32 ) |]
        do_assert

  , basic_llvm_override $
        [llvmOvr| void @crucible_print_uint32( i32 ) |]
        do_print_uint32

  , basic_llvm_override $
        [llvmOvr| void @crucible_havoc_memory( i8*, size_t ) |]
        do_havoc_memory
  ]


cbmcOverrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [OverrideTemplate (Model sym) sym arch rtp l a]
cbmcOverrides =
  [ basic_llvm_override $
      [llvmOvr| void @__CPROVER_assume( i32 ) |]
      cprover_assume
  , basic_llvm_override $
      [llvmOvr| void @__CPROVER_assert( i32, i8* ) |]
      cprover_assert
  , basic_llvm_override $
      [llvmOvr| i1 @__CPROVER_r_ok( i8*, size_t ) |]
      cprover_r_ok
  , basic_llvm_override $
      [llvmOvr| i1 @__CPROVER_w_ok( i8*, size_t ) |]
      cprover_w_ok

  , basic_llvm_override $
      [llvmOvr| i1 @nondet_bool() |]
      (sv_comp_fresh_bits (knownNat @1))
  , basic_llvm_override $
      [llvmOvr| i8 @nondet_char() |]
      (sv_comp_fresh_bits (knownNat @8))
  , basic_llvm_override $
      [llvmOvr| i8 @nondet_uchar() |]
      (sv_comp_fresh_bits (knownNat @8))
  , basic_llvm_override $
      [llvmOvr| i8 @nondet_uint8_t() |]
      (sv_comp_fresh_bits (knownNat @8))
  , basic_llvm_override $
      [llvmOvr| i8 @nondet_int8_t() |]
      (sv_comp_fresh_bits (knownNat @8))

  , basic_llvm_override $
      [llvmOvr| i16 @nondet_short() |]
      (sv_comp_fresh_bits (knownNat @16))
  , basic_llvm_override $
      [llvmOvr| i16 @nondet_ushort() |]
      (sv_comp_fresh_bits (knownNat @16))
  , basic_llvm_override $
      [llvmOvr| i16 @nondet_int16_t() |]
      (sv_comp_fresh_bits (knownNat @16))
  , basic_llvm_override $
      [llvmOvr| i16 @nondet_uint16_t() |]
      (sv_comp_fresh_bits (knownNat @16))

  , basic_llvm_override $
      [llvmOvr| i32 @nondet_int() |]
      (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
      [llvmOvr| i32 @nondet_uint() |]
      (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
      [llvmOvr| i32 @nondet_int32_t() |]
      (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
      [llvmOvr| i32 @nondet_uint32_t() |]
      (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
      [llvmOvr| i64 @nondet_int64_t() |]
      (sv_comp_fresh_bits (knownNat @64))
  , basic_llvm_override $
      [llvmOvr| i64 @nondet_uint64_t() |]
      (sv_comp_fresh_bits (knownNat @64))

  , basic_llvm_override $
      [llvmOvr| size_t @nondet_long() |]
      (sv_comp_fresh_bits ?ptrWidth)
  , basic_llvm_override $
      [llvmOvr| size_t @nondet_ulong() |]
      (sv_comp_fresh_bits ?ptrWidth)
  , basic_llvm_override $
      [llvmOvr| size_t @nondet_size_t() |]
      (sv_comp_fresh_bits ?ptrWidth)

  , basic_llvm_override $
        [llvmOvr| float @nondet_float() |]
        (sv_comp_fresh_float SingleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| double @nondet_double() |]
        (sv_comp_fresh_float DoubleFloatRepr)

{-
  , basic_llvm_override $
      [llvmOvr| i8* @nondet_voidp() |]
      (sv_comp_fresh_bits ?ptrWidth)
-}
  ]


svCompOverrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [OverrideTemplate (Model sym) sym arch rtp l a]
svCompOverrides =
  [ basic_llvm_override $
        [llvmOvr| size_t @__VERIFIER_nondet_ulong() |]
        (sv_comp_fresh_bits ?ptrWidth)

  , basic_llvm_override $
        [llvmOvr| size_t @__VERIFIER_nondet_long() |]
        (sv_comp_fresh_bits ?ptrWidth)

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_uint() |]
        (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_int() |]
        (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i16 @__VERIFIER_nondet_ushort() |]
        (sv_comp_fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i16 @__VERIFIER_nondet_short() |]
        (sv_comp_fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i8 @__VERIFIER_nondet_uchar() |]
        (sv_comp_fresh_bits (knownNat @8))

  , basic_llvm_override $
        [llvmOvr| i8 @__VERIFIER_nondet_char() |]
        (sv_comp_fresh_bits (knownNat @8))

  , basic_llvm_override $
        [llvmOvr| i1 @__VERIFIER_nondet_bool() |]
        (sv_comp_fresh_bits (knownNat @1))

  , basic_llvm_override $
        [llvmOvr| float @__VERIFIER_nondet_float() |]
        (sv_comp_fresh_float SingleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| double @__VERIFIER_nondet_double() |]
        (sv_comp_fresh_float DoubleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| void @__VERIFIER_assert( i32 ) |]
        sv_comp_assert

  , basic_llvm_override $
        [llvmOvr| void @__VERIFIER_assume( i32 ) |]
        sv_comp_assume

  , basic_llvm_override $
        [llvmOvr| void @__VERIFIER_error( ) |]
        sv_comp_error
  ]

--------------------------------------------------------------------------------

mkFresh ::
  (IsSymInterface sym) =>
  String ->
  BaseTypeRepr ty ->
  OverM sym (LLVM arch) (RegValue sym (BaseToType ty))
mkFresh nm ty =
  do sym  <- getSymInterface
     name <- case userSymbol nm of
               Left err -> fail (show err) -- XXX
               Right a  -> return a
     elt <- liftIO (freshConstant sym name ty)
     loc   <- liftIO $ getCurrentProgramLoc sym
     stateContext.cruciblePersonality %= addVar loc nm ty elt
     return elt

mkFreshFloat
  ::(IsSymInterface sym)
  => String
  -> FloatInfoRepr fi
  -> OverM sym (LLVM arch) (RegValue sym (FloatType fi))
mkFreshFloat nm fi = do
  sym  <- getSymInterface
  name <- case userSymbol nm of
            Left err -> fail (show err) -- XXX
            Right a  -> return a
  elt  <- liftIO $ freshFloatConstant sym name fi
  loc  <- liftIO $ getCurrentProgramLoc sym
  stateContext.cruciblePersonality %=
    addVar loc nm (iFloatBaseTypeRepr sym fi) elt
  return elt

lookupString ::
  (IsSymInterface sym, HasLLVMAnn sym, ArchOk arch) =>
  GlobalVar Mem -> RegEntry sym (TPtr arch) -> OverM sym (LLVM arch) String
lookupString mvar ptr =
  do sym <- getSymInterface
     mem <- readGlobal mvar
     bytes <- liftIO (loadString sym mem (regValue ptr) Nothing)
     return (BS8.unpack (BS.pack bytes))

sv_comp_fresh_bits ::
  (ArchOk arch, IsSymInterface sym, 1 <= w) =>
  NatRepr w ->
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) EmptyCtx ->
  OverM sym (LLVM arch) (RegValue sym (BVType w))
sv_comp_fresh_bits w _mvar _sym Empty = mkFresh "X" (BaseBVRepr w)

sv_comp_fresh_float ::
  (ArchOk arch, IsSymInterface sym) =>
  FloatInfoRepr fi ->
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) EmptyCtx ->
  OverM sym (LLVM arch) (RegValue sym (FloatType fi))
sv_comp_fresh_float fi _mvar _sym Empty = mkFreshFloat "X" fi

fresh_bits ::
  (ArchOk arch, HasLLVMAnn sym, IsSymInterface sym, 1 <= w) =>
  NatRepr w ->
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch) ->
  OverM sym (LLVM arch) (RegValue sym (BVType w))
fresh_bits w mvar _ (Empty :> pName) =
  do name <- lookupString mvar pName
     mkFresh name (BaseBVRepr w)

fresh_float ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  FloatInfoRepr fi ->
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch) ->
  OverM sym (LLVM arch) (RegValue sym (FloatType fi))
fresh_float fi mvar _ (Empty :> pName) =
  do name <- lookupString mvar pName
     mkFreshFloat name fi

fresh_str ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::> BVType (ArchWidth arch)) ->
  OverM sym (LLVM arch) (RegValue sym (TPtr arch))
fresh_str mvar sym (Empty :> pName :> maxLen) =
  do name <- lookupString mvar pName

     -- Compute the allocation length, which is the requested length plus one
     -- to hold the NUL terminator
     one <- liftIO $ bvLit sym ?ptrWidth (BV.one ?ptrWidth)
     -- maxLenBV <- liftIO $ projectLLVM_bv sym (regValue maxLen)
     len <- liftIO $ bvAdd sym (regValue maxLen) one
     mem0 <- readGlobal mvar

     -- Allocate memory to hold the string
     (ptr, mem1) <- liftIO $ doMalloc sym HeapAlloc Mutable name mem0 len noAlignment

     -- Allocate contents for the string - we want to make each byte symbolic,
     -- so we allocate a fresh array (which has unbounded length) with symbolic
     -- contents and write it into our allocation.  This write does not cover
     -- the NUL terminator.
     contentsName <- case userSymbol (name ++ "_contents") of
       Left err -> fail (show err)
       Right nm -> return nm
     let arrayRep = BaseArrayRepr (Empty :> BaseBVRepr ?ptrWidth) (BaseBVRepr (knownNat @8))
     initContents <- liftIO $ freshConstant sym contentsName arrayRep
     zeroByte <- liftIO $ bvLit sym (knownNat @8) (BV.zero knownNat)
     -- Put the NUL terminator in place
     initContentsZ <- liftIO $ arrayUpdate sym initContents (singleton (regValue maxLen)) zeroByte
     mem2 <- liftIO $ doArrayConstStore sym mem1 ptr noAlignment initContentsZ len

     writeGlobal mvar mem2
     return ptr

do_assume ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
do_assume mvar sym (Empty :> p :> pFile :> line) =
  do cond <- liftIO $ bvIsNonzero sym (regValue p)
     file <- lookupString mvar pFile
     l <- case asBV (regValue line) of
            Just (BV.BV l)  -> return (fromInteger l)
            Nothing -> return 0
     let pos = SourcePos (T.pack file) l 0
     loc <- liftIO $ getCurrentProgramLoc sym
     let loc' = loc{ plSourceLoc = pos }
     let msg = AssumptionReason loc' "crucible_assume"
     liftIO $ addAssumption sym (LabeledPred cond msg)

do_assert ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
do_assert mvar sym (Empty :> p :> pFile :> line) =
  do cond <- liftIO $ bvIsNonzero sym (regValue p)
     file <- lookupString mvar pFile
     l <- case asBV (regValue line) of
            Just (BV.BV l)  -> return (fromInteger l)
            Nothing -> return 0
     let pos = SourcePos (T.pack file) l 0
     loc <- liftIO $ getCurrentProgramLoc sym
     let loc' = loc{ plSourceLoc = pos }
     let msg = GenericSimError "crucible_assert"
     liftIO $ addDurableAssertion sym (LabeledPred cond (SimError loc' msg))

do_print_uint32 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
do_print_uint32 _mvar _sym (Empty :> x) =
  do h <- printHandle <$> getContext
     liftIO $ hPutStrLn h (show (printSymExpr (regValue x)))

do_havoc_memory ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::> TBits (ArchWidth arch)) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
do_havoc_memory mvar sym (Empty :> ptr :> len) =
  do let tp = BaseArrayRepr (Empty :> BaseBVRepr ?ptrWidth) (BaseBVRepr (knownNat @8))
     mem <- readGlobal mvar
     mem' <- liftIO $ do
               arr <- freshConstant sym emptySymbol tp
               doArrayStore sym mem (regValue ptr) noAlignment arr (regValue len)
     writeGlobal mvar mem'

cprover_assume ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
cprover_assume _mvar sym (Empty :> p) = liftIO $
  do cond <- bvIsNonzero sym (regValue p)
     loc  <- getCurrentProgramLoc sym
     let msg = AssumptionReason loc "__CPROVER_assume"
     addAssumption sym (LabeledPred cond msg)

cprover_assert ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32 ::> TPtr arch) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
cprover_assert mvar sym (Empty :> p :> pMsg) =
  do cond <- liftIO $ bvIsNonzero sym (regValue p)
     str <- lookupString mvar pMsg
     loc <- liftIO $ getCurrentProgramLoc sym
     let msg = AssertFailureSimError "__CPROVER_assert" str
     liftIO $ addDurableAssertion sym (LabeledPred cond (SimError loc msg))

cprover_r_ok ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::>  BVType (ArchWidth arch)) ->
  OverM sym (LLVM arch) (RegValue sym (BVType 1))
cprover_r_ok mvar sym (Empty :> (regValue -> p) :> (regValue -> sz)) =
  do mem <- readGlobal mvar
     x <- liftIO $ isAllocatedAlignedPointer sym PtrWidth noAlignment Immutable p (Just sz) mem
     liftIO $ predToBV sym x knownNat

cprover_w_ok ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::>  BVType (ArchWidth arch)) ->
  OverM sym (LLVM arch) (RegValue sym (BVType 1))
cprover_w_ok mvar sym (Empty :> (regValue -> p) :> (regValue -> sz)) =
  do mem <- readGlobal mvar
     x <- liftIO $ isAllocatedAlignedPointer sym PtrWidth noAlignment Mutable p (Just sz) mem
     liftIO $ predToBV sym x knownNat

sv_comp_assume ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
sv_comp_assume _mvar sym (Empty :> p) = liftIO $
  do cond <- bvIsNonzero sym (regValue p)
     loc  <- getCurrentProgramLoc sym
     let msg = AssumptionReason loc "__VERIFIER_assume"
     addAssumption sym (LabeledPred cond msg)

sv_comp_assert ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32) ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
sv_comp_assert _mvar sym (Empty :> p) = liftIO $
  do cond <- bvIsNonzero sym (regValue p)
     loc  <- getCurrentProgramLoc sym
     let msg = AssertFailureSimError "__VERIFIER_assert" ""
     addDurableAssertion sym (LabeledPred cond (SimError loc msg))

sv_comp_error ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  sym ->
  Assignment (RegEntry sym) EmptyCtx ->
  OverM sym (LLVM arch) (RegValue sym UnitType)
sv_comp_error _mvar sym Empty = liftIO $
  do let rsn = AssertFailureSimError "__VERIFIER_error" ""
     addFailedAssertion sym rsn
