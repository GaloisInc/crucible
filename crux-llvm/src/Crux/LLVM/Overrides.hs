{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
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
  , TPtr
  ) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Control.Monad (when)
import Control.Monad.IO.Class(liftIO)
import GHC.Exts ( Proxy# )
import System.IO (hPutStrLn)
import qualified Data.Text as T

import qualified Data.BitVector.Sized as BV
import Data.Parameterized.Context.Unsafe (Assignment)
import Data.Parameterized.Context(pattern Empty, pattern (:>), singleton)

import What4.ProgramLoc( Position(..), ProgramLoc(..) )
import What4.Symbol(userSymbol, emptySymbol, safeSymbol)
import What4.Interface
          (freshConstant, bvLit, bvAdd, asBV, predToBV,
          getCurrentProgramLoc, printSymExpr, arrayUpdate, bvIsNonzero)

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(GlobalVar)
import Lang.Crucible.Simulator.RegMap(regValue,RegValue,RegEntry)
import Lang.Crucible.Simulator.ExecutionTree( printHandle )
import Lang.Crucible.Simulator.OverrideSim
        ( getContext
        , getSymInterface
        , readGlobal
        , writeGlobal
        , ovrWithBackend
        )
import Lang.Crucible.Simulator.SimError (SimErrorReason(..),SimError(..))
import Lang.Crucible.Backend
          ( IsSymInterface, addDurableAssertion
          , addAssumption, LabeledPred(..), CrucibleAssumption(..)
          , backendGetSym
          )
import Lang.Crucible.LLVM.QQ( llvmOvr )
import Lang.Crucible.LLVM.DataLayout
  (noAlignment)
import Lang.Crucible.LLVM.MemModel
  (Mem, LLVMPointerType, loadString, HasPtrWidth,
   doMalloc, AllocType(HeapAlloc), Mutability(Mutable),
   doArrayStore, doArrayConstStore, HasLLVMAnn,
   isAllocatedAlignedPointer, Mutability(..),
   pattern PtrWidth, doDumpMem, MemOptions
   )

import           Lang.Crucible.LLVM.TypeContext( TypeContext )
import           Lang.Crucible.LLVM.Intrinsics

import Lang.Crucible.LLVM.Extension ( ArchWidth )

import qualified Crux.Overrides as Crux
import Crux.Types

-- | This happens quite a lot, so just a shorter name
type ArchOk arch    = HasPtrWidth (ArchWidth arch)
type TPtr arch      = LLVMPointerType (ArchWidth arch)
type TBits n        = BVType n


cruxLLVMOverrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch
  , ?lc :: TypeContext, ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  [OverrideTemplate (personality sym) sym arch rtp l a]
cruxLLVMOverrides arch =
  [ basic_llvm_override $
        [llvmOvr| i8 @crucible_int8_t( i8* ) |]
        (fresh_bits arch (knownNat @8))

  , basic_llvm_override $
        [llvmOvr| i16 @crucible_int16_t( i8* ) |]
        (fresh_bits arch (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i32 @crucible_int32_t( i8* ) |]
        (fresh_bits arch (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i64 @crucible_int64_t( i8* ) |]
        (fresh_bits arch (knownNat @64))

  , basic_llvm_override $
        [llvmOvr| i8 @crucible_uint8_t( i8* ) |]
        (fresh_bits arch (knownNat @8))

  , basic_llvm_override $
        [llvmOvr| i16 @crucible_uint16_t( i8* ) |]
        (fresh_bits arch (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i32 @crucible_uint32_t( i8* ) |]
        (fresh_bits arch (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i64 @crucible_uint64_t( i8* ) |]
        (fresh_bits arch (knownNat @64))

  , basic_llvm_override $
        [llvmOvr| float @crucible_float( i8* ) |]
        (fresh_float arch SingleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| double @crucible_double( i8* ) |]
        (fresh_float arch DoubleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| i8* @crucible_string( i8*, size_t ) |]
        (fresh_str arch)

  , basic_llvm_override $
        [llvmOvr| void @crucible_assume( i8, i8*, i32 ) |]
        (do_assume arch)

  , basic_llvm_override $
        [llvmOvr| void @crucible_assert( i8, i8*, i32 ) |]
        (do_assert arch)

  , basic_llvm_override $
        [llvmOvr| void @crucible_print_uint32( i32 ) |]
        do_print_uint32

  , basic_llvm_override $
        [llvmOvr| void @crucible_havoc_memory( i8*, size_t ) |]
        (do_havoc_memory arch)

  , basic_llvm_override $
        [llvmOvr| void @crucible_dump_memory( ) |]
        (\mvar _args ->
          do mem <- readGlobal mvar
             h <- printHandle <$> getContext
             liftIO (doDumpMem h mem))
  ]


cbmcOverrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch
  , ?lc :: TypeContext, ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  [OverrideTemplate (personality sym) sym arch rtp l a]
cbmcOverrides arch =
  [ basic_llvm_override $
      [llvmOvr| void @__CPROVER_assume( i32 ) |]
      cprover_assume
  , basic_llvm_override $
      [llvmOvr| void @__CPROVER_assert( i32, i8* ) |]
      (cprover_assert arch)
  , basic_llvm_override $
      [llvmOvr| i1 @__CPROVER_r_ok( i8*, size_t ) |]
      (cprover_r_ok arch)
  , basic_llvm_override $
      [llvmOvr| i1 @__CPROVER_w_ok( i8*, size_t ) |]
      (cprover_w_ok arch)

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

    -- @nondet_long@ returns a `long`, so we need two overrides for
    -- @nondet_long@. Similarly for @nondet_ulong@.
    -- See Note [Overrides involving (unsigned) long] in
    -- crucible-llvm:Lang.Crucible.LLVM.Intrinsics.
  , basic_llvm_override $
      [llvmOvr| i32 @nondet_long() |]
      (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
      [llvmOvr| i64 @nondet_long() |]
      (sv_comp_fresh_bits (knownNat @64))
  , basic_llvm_override $
      [llvmOvr| i32 @nondet_ulong() |]
      (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
      [llvmOvr| i64 @nondet_ulong() |]
      (sv_comp_fresh_bits (knownNat @64))
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
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  [OverrideTemplate (personality sym) sym arch rtp l a]
svCompOverrides =
  [ basic_llvm_override $
        [llvmOvr| i64 @__VERIFIER_nondet_longlong() |]
        (sv_comp_fresh_bits (knownNat @64))

    -- loff_t is pretty Linux-specific, so we can't point to the C or POSIX
    -- standards for justification about what size it should be. The man page
    -- for lseek64 (https://linux.die.net/man/3/lseek64) is as close to a
    -- definitive reference for this as I can find, which says
    -- "The type loff_t is a 64-bit signed type".
  , basic_llvm_override $
        [llvmOvr| i64 @__VERIFIER_nondet_loff_t() |]
        (sv_comp_fresh_bits (knownNat @64))

    -- @__VERIFIER_nondet_ulong@ returns an `unsigned long`, so we need two
    -- overrides for @__VERIFIER_nondet_ulong@. Similarly for
    -- @__VERIFIER_nondet_long@. See Note [Overrides involving (unsigned) long]
    -- in crucible-llvm:Lang.Crucible.LLVM.Intrinsics.
  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_ulong() |]
        (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
        [llvmOvr| i64 @__VERIFIER_nondet_ulong() |]
        (sv_comp_fresh_bits (knownNat @64))

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_long() |]
        (sv_comp_fresh_bits (knownNat @32))
  , basic_llvm_override $
        [llvmOvr| i64 @__VERIFIER_nondet_long() |]
        (sv_comp_fresh_bits (knownNat @64))

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_unsigned() |]
        (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_u32() |]
        (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_uint() |]
        (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i32 @__VERIFIER_nondet_int() |]
        (sv_comp_fresh_bits (knownNat @32))

  , basic_llvm_override $
        [llvmOvr| i16 @__VERIFIER_nondet_u16() |]
        (sv_comp_fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i16 @__VERIFIER_nondet_ushort() |]
        (sv_comp_fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i16 @__VERIFIER_nondet_short() |]
        (sv_comp_fresh_bits (knownNat @16))

  , basic_llvm_override $
        [llvmOvr| i8 @__VERIFIER_nondet_u8() |]
        (sv_comp_fresh_bits (knownNat @8))

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
        [llvmOvr| size_t @__VERIFIER_nondet_size_t() |]
        (sv_comp_fresh_bits ?ptrWidth)

  , basic_llvm_override $
        [llvmOvr| float @__VERIFIER_nondet_float() |]
        (sv_comp_fresh_float SingleFloatRepr)

  , basic_llvm_override $
        [llvmOvr| double @__VERIFIER_nondet_double() |]
        (sv_comp_fresh_float DoubleFloatRepr)
  ]

--------------------------------------------------------------------------------

lookupString ::
  ( IsSymInterface sym, HasLLVMAnn sym, ArchOk arch
  , ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  GlobalVar Mem -> RegEntry sym (TPtr arch) -> OverM personality sym ext String
lookupString _ mvar ptr =
  ovrWithBackend $ \bak ->
    do mem <- readGlobal mvar
       bytes <- liftIO (loadString bak mem (regValue ptr) Nothing)
       return (BS8.unpack (BS.pack bytes))

sv_comp_fresh_bits ::
  (IsSymInterface sym, 1 <= w) =>
  NatRepr w ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) EmptyCtx ->
  OverM personality sym ext (RegValue sym (BVType w))
sv_comp_fresh_bits w _mvar Empty = Crux.mkFresh (safeSymbol "X") (BaseBVRepr w)

sv_comp_fresh_float ::
  IsSymInterface sym =>
  FloatInfoRepr fi ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) EmptyCtx ->
  OverM personality sym ext (RegValue sym (FloatType fi))
sv_comp_fresh_float fi _mvar Empty = Crux.mkFreshFloat (safeSymbol "X") fi

fresh_bits ::
  ( ArchOk arch, IsSymInterface sym, HasLLVMAnn sym, 1 <= w
  , ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  NatRepr w ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch) ->
  OverM personality sym ext (RegValue sym (BVType w))
fresh_bits arch w mvar (Empty :> pName) =
  do name <- lookupString arch mvar pName
     Crux.mkFresh (safeSymbol name) (BaseBVRepr w)

fresh_float ::
  ( ArchOk arch, IsSymInterface sym, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  FloatInfoRepr fi ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch) ->
  OverM personality sym ext (RegValue sym (FloatType fi))
fresh_float arch fi mvar (Empty :> pName) =
  do name <- lookupString arch mvar pName
     Crux.mkFreshFloat (safeSymbol name) fi

fresh_str ::
  ( ArchOk arch, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::> BVType (ArchWidth arch)) ->
  OverM personality sym ext (RegValue sym (TPtr arch))
fresh_str arch mvar (Empty :> pName :> maxLen) =
  ovrWithBackend $ \bak -> do 
    let sym = backendGetSym bak
    name <- lookupString arch mvar pName

    -- Compute the allocation length, which is the requested length plus one
    -- to hold the NUL terminator
    one <- liftIO $ bvLit sym ?ptrWidth (BV.one ?ptrWidth)
    -- maxLenBV <- liftIO $ projectLLVM_bv sym (regValue maxLen)
    len <- liftIO $ bvAdd sym (regValue maxLen) one
    mem0 <- readGlobal mvar

    -- Allocate memory to hold the string
    (ptr, mem1) <- liftIO $ doMalloc bak HeapAlloc Mutable name mem0 len noAlignment

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
    mem2 <- liftIO $ doArrayConstStore bak mem1 ptr noAlignment initContentsZ len

    writeGlobal mvar mem2
    return ptr

do_assume ::
  ( ArchOk arch, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) ->
  OverM personality sym ext (RegValue sym UnitType)
do_assume arch mvar (Empty :> p :> pFile :> line) =
  ovrWithBackend $ \bak -> do 
    let sym = backendGetSym bak
    cond <- liftIO $ bvIsNonzero sym (regValue p)
    file <- lookupString arch mvar pFile
    l <- case asBV (regValue line) of
           Just (BV.BV l)  -> return (fromInteger l)
           Nothing -> return 0
    let pos = SourcePos (T.pack file) l 0
    loc <- liftIO $ getCurrentProgramLoc sym
    let loc' = loc{ plSourceLoc = pos }
    liftIO $ addAssumption bak (GenericAssumption loc' "crucible_assume" cond)

do_assert ::
  ( ArchOk arch, HasLLVMAnn sym
  , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) ->
  OverM personality sym ext (RegValue sym UnitType)
do_assert arch mvar (Empty :> p :> pFile :> line) =
  when (abnormalExitBehavior ?intrinsicsOpts == AlwaysFail) $
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
    cond <- liftIO $ bvIsNonzero sym (regValue p)
    file <- lookupString arch mvar pFile
    l <- case asBV (regValue line) of
           Just (BV.BV l)  -> return (fromInteger l)
           Nothing -> return 0
    let pos = SourcePos (T.pack file) l 0
    loc <- liftIO $ getCurrentProgramLoc sym
    let loc' = loc{ plSourceLoc = pos }
    let msg = GenericSimError "crucible_assert"
    liftIO $ addDurableAssertion bak (LabeledPred cond (SimError loc' msg))

do_print_uint32 :: 
  IsSymInterface sym =>
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32) ->
  OverM personality sym ext (RegValue sym UnitType)
do_print_uint32 _mvar (Empty :> x) =
  do h <- printHandle <$> getContext
     liftIO $ hPutStrLn h (show (printSymExpr (regValue x)))

do_havoc_memory ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::> TBits (ArchWidth arch)) ->
  OverM personality sym ext (RegValue sym UnitType)
do_havoc_memory _ mvar (Empty :> ptr :> len) =
  ovrWithBackend $ \bak ->
    do let sym = backendGetSym bak
       let tp = BaseArrayRepr (Empty :> BaseBVRepr ?ptrWidth) (BaseBVRepr (knownNat @8))
       mem <- readGlobal mvar
       mem' <- liftIO $ do
                 arr <- freshConstant sym emptySymbol tp
                 doArrayStore bak mem (regValue ptr) noAlignment arr (regValue len)
       writeGlobal mvar mem'

cprover_assume ::
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32) ->
  OverM personality sym ext (RegValue sym UnitType)
cprover_assume _mvar (Empty :> p) =
  ovrWithBackend $ \bak -> liftIO $ do
    let sym = backendGetSym bak
    cond <- bvIsNonzero sym (regValue p)
    loc  <- getCurrentProgramLoc sym
    addAssumption bak (GenericAssumption loc "__CPROVER_assume" cond)


cprover_assert ::
  ( ArchOk arch, HasLLVMAnn sym
  , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TBits 32 ::> TPtr arch) ->
  OverM personality sym ext (RegValue sym UnitType)
cprover_assert arch mvar (Empty :> p :> pMsg) =
  when (abnormalExitBehavior ?intrinsicsOpts == AlwaysFail) $
  ovrWithBackend $ \bak ->
    do let sym = backendGetSym bak
       cond <- liftIO $ bvIsNonzero sym (regValue p)
       str <- lookupString arch mvar pMsg
       loc <- liftIO $ getCurrentProgramLoc sym
       let msg = AssertFailureSimError "__CPROVER_assert" str
       liftIO $ addDurableAssertion bak (LabeledPred cond (SimError loc msg))

cprover_r_ok ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::>  BVType (ArchWidth arch)) ->
  OverM personality sym ext (RegValue sym (BVType 1))
cprover_r_ok _ mvar (Empty :> (regValue -> p) :> (regValue -> sz)) =
  do sym <- getSymInterface
     mem <- readGlobal mvar
     x <- liftIO $ isAllocatedAlignedPointer sym PtrWidth noAlignment Immutable p (Just sz) mem
     liftIO $ predToBV sym x knownNat

cprover_w_ok ::
  (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
  Proxy# arch ->
  GlobalVar Mem ->
  Assignment (RegEntry sym) (EmptyCtx ::> TPtr arch ::>  BVType (ArchWidth arch)) ->
  OverM personality sym ext (RegValue sym (BVType 1))
cprover_w_ok _ mvar (Empty :> (regValue -> p) :> (regValue -> sz)) =
  do sym <- getSymInterface
     mem <- readGlobal mvar
     x <- liftIO $ isAllocatedAlignedPointer sym PtrWidth noAlignment Mutable p (Just sz) mem
     liftIO $ predToBV sym x knownNat
