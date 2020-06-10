-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.LLVM
-- Description      : Override definitions for LLVM intrinsic and basic
--                    library functions
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.LLVM where

import           GHC.TypeNats (KnownNat)
import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.Reader
import           Data.Bits ((.&.))
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError (SimErrorReason(AssertFailureSimError))

import           Lang.Crucible.LLVM.Bytes (Bytes(..))
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVM)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.QQ( llvmOvr )

import           Lang.Crucible.LLVM.Intrinsics.Common
import qualified Lang.Crucible.LLVM.Intrinsics.Libc as Libc

------------------------------------------------------------------------
-- ** Declarations

-- | This intrinsic is currently a no-op.
--
-- We might want to support this in the future to catch undefined memory
-- accesses.
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-start-intrinsic LLVM docs>
llvmLifetimeStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeStartOverride =
  [llvmOvr| void @llvm.lifetime.start( i64, i8* ) |]
  (\_ops _sym _args -> return ())

-- | See comment on 'llvmLifetimeStartOverride'
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-end-intrinsic LLVM docs>
llvmLifetimeEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeEndOverride =
  [llvmOvr| void @llvm.lifetime.end( i64, i8* ) |]
  (\_ops _sym _args -> return ())

-- | This is a no-op.
--
-- The language reference doesn't mention the use of this intrinsic.
llvmLifetimeOverrideOverload
  :: forall width sym wptr arch p
   . ( 1 <= width, KnownNat width
     , IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => String -- ^ "start" or "end"
  -> NatRepr width
  -> LLVMOverride p sym arch
        (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
        UnitType -- It appears in practice that this is always void
llvmLifetimeOverrideOverload startOrEnd w =
  let nm = L.Symbol ("llvm.lifetime." ++ startOrEnd ++ ".p0i" ++ show (widthVal w)) in
    [llvmOvr| void $nm ( i64, #w * ) |]
    (\_ops _sym _args -> return ())

-- | This intrinsic is currently a no-op.
--
-- We might want to support this in the future to catch undefined memory
-- writes.
--
-- <https://llvm.org/docs/LangRef.html#llvm-invariant-start-intrinsic LLVM docs>
llvmInvariantStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr width
  -> LLVMOverride p sym arch
       (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
       (LLVMPointerType wptr)
llvmInvariantStartOverride w =
  let nm = L.Symbol ("llvm.invariant.start.p0i" ++ show (widthVal w)) in
    [llvmOvr| {}* $nm ( i64, #w * ) |]
    (\_ops sym _args -> liftIO (mkNullPointer sym PtrWidth))

-- | See comment on 'llvmInvariantStartOverride'.
llvmInvariantEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr width
  -> LLVMOverride p sym arch
       (EmptyCtx ::> LLVMPointerType wptr ::> BVType 64 ::> LLVMPointerType wptr)
       UnitType
llvmInvariantEndOverride w =
  let nm = L.Symbol ("llvm.invariant.end.p0i" ++ show (widthVal w)) in
    [llvmOvr| void $nm ( {}*, i64, #w * ) |]
    (\_ops _sym _args -> return ())

-- | This instruction is a hint to optimizers, it isn't really useful for us.
--
-- Its runtime behavior of that of Haskell\'s 'const': just ignore the second
-- argument.
llvmExpectOverride
  :: (IsSymInterface sym, 1 <= width)
  => NatRepr width
  -> LLVMOverride p sym arch
       (EmptyCtx ::> BVType width ::> BVType width)
       (BVType width)
llvmExpectOverride w =
  let nm = L.Symbol ("llvm.expect.i" ++ show (widthVal w)) in
    [llvmOvr| #w $nm ( #w, #w ) |]
    (\_ops _sym args ->
        Ctx.uncurryAssignment (\val _ -> pure (regValue val)) args)

-- | This intrinsic asserts that its argument is equal to 1.
--
-- We could have this generate a verification condition, but that would catch
-- clang compiler bugs (or Crucible bugs) more than user code bugs.
llvmAssumeOverride
  :: (IsSymInterface sym)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 1) UnitType
llvmAssumeOverride =
   [llvmOvr| void @llvm.assume ( i1 ) |]
   (\_ops _sym _args -> return ())

-- | This intrinsic is sometimes inserted by clang, and we interpret it
--   as an assertion failure, similar to calling @abort()@.
llvmTrapOverride
  :: (IsSymInterface sym)
  => LLVMOverride p sym arch EmptyCtx UnitType
llvmTrapOverride =
  [llvmOvr| void @llvm.trap() |]
  (\_ops sym _args -> liftIO $ addFailedAssertion sym $ AssertFailureSimError "llvm.trap() called" "")


llvmStacksave
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch EmptyCtx (LLVMPointerType wptr)
llvmStacksave =
  [llvmOvr| i8* @llvm.stacksave() |]
  (\_memOps sym _args -> liftIO (mkNullPointer sym PtrWidth))

llvmStackrestore
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) UnitType
llvmStackrestore =
  [llvmOvr| void @llvm.stackrestore( i8* ) |]
  (\_memOps _sym _args -> return ())

llvmMemmoveOverride_8_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32 =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i32( i8*, i8*, i32, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemmove sym memOps dst src len v) args)

llvmMemmoveOverride_8_8_32_noalign
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32_noalign =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i32( i8*, i8*, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemmove sym memOps) args)


llvmMemmoveOverride_8_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64 =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i64( i8*, i8*, i64, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemmove sym memOps dst src len v) args)


llvmMemmoveOverride_8_8_64_noalign
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64_noalign =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i64( i8*, i8*, i64, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemmove sym memOps) args)

llvmMemsetOverride_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64 =
  [llvmOvr| void @llvm.memset.p0i8.i64( i8*, i8, i64, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\dst val len _align v -> Libc.callMemset sym memOps dst val len v) args)

llvmMemsetOverride_8_64_noalign
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64_noalign =
  [llvmOvr| void @llvm.memset.p0i8.i64( i8*, i8, i64, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemset sym memOps) args)


llvmMemsetOverride_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32 =
  [llvmOvr| void @llvm.memset.p0i8.i32( i8*, i8, i32, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\dst val len _align v -> Libc.callMemset sym memOps dst val len v) args)

llvmMemsetOverride_8_32_noalign
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32_noalign =
  [llvmOvr| void @llvm.memset.p0i8.i32( i8*, i8, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemset sym memOps) args)


llvmMemcpyOverride_8_8_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32 =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i32( i8*, i8*, i32, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemcpy sym memOps dst src len v) args)

llvmMemcpyOverride_8_8_32_noalign
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32_noalign =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i32( i8*, i8*, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemcpy sym memOps) args)


llvmMemcpyOverride_8_8_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64 =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i64( i8*, i8*, i64, i32, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemcpy sym memOps dst src len v) args)


llvmMemcpyOverride_8_8_64_noalign
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64_noalign =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i64( i8*, i8*, i64, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (Libc.callMemcpy sym memOps) args)


llvmObjectsizeOverride_32
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32 =
  [llvmOvr| i32 @llvm.objectsize.i32.p0i8( i8*, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args)

llvmObjectsizeOverride_32_null
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32_null =
  [llvmOvr| i32 @llvm.objectsize.i32.p0i8( i8*, i1, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize_null sym memOps knownNat) args)

llvmObjectsizeOverride_32_null_dynamic
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32_null_dynamic =
  [llvmOvr| i32 @llvm.objectsize.i32.p0i8( i8*, i1, i1, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize_null_dynamic sym memOps knownNat) args)

llvmObjectsizeOverride_64
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64 =
  [llvmOvr| i64 @llvm.objectsize.i64.p0i8( i8*, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize sym memOps knownNat) args)

llvmObjectsizeOverride_64_null
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64_null =
  [llvmOvr| i64 @llvm.objectsize.i64.p0i8( i8*, i1, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize_null sym memOps knownNat) args)

llvmObjectsizeOverride_64_null_dynamic
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64_null_dynamic =
  [llvmOvr| i64 @llvm.objectsize.i64.p0i8( i8*, i1, i1, i1 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callObjectsize_null_dynamic sym memOps knownNat) args)

llvmFshl ::
  (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  NatRepr w ->
  LLVMOverride p sym arch
    (EmptyCtx ::> BVType w ::> BVType w ::> BVType w)
    (BVType w)
llvmFshl w =
 let nm = L.Symbol ("llvm.fshl.i" ++ show (natValue w)) in
 [llvmOvr| #w $nm ( #w, #w, #w ) |]
 (\_memOps sym args -> Ctx.uncurryAssignment (callFshl sym w) args)

llvmFshr ::
  (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  NatRepr w ->
  LLVMOverride p sym arch
    (EmptyCtx ::> BVType w ::> BVType w ::> BVType w)
    (BVType w)
llvmFshr w =
 let nm = L.Symbol ("llvm.fshr.i" ++ show (natValue w)) in
 [llvmOvr| #w $nm ( #w, #w, #w ) |]
 (\_memOps sym args -> Ctx.uncurryAssignment (callFshr sym w) args)

llvmSaddWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSaddWithOverflow w =
  let nm = L.Symbol ("llvm.sadd.with.overflow.i" ++ show (natValue w)) in
  [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callSaddWithOverflow sym memOps) args)

llvmUaddWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUaddWithOverflow w =
  let nm = L.Symbol ("llvm.uadd.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callUaddWithOverflow sym memOps) args)


llvmSsubWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSsubWithOverflow w =
  let nm = L.Symbol ("llvm.ssub.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callSsubWithOverflow sym memOps) args)


llvmUsubWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUsubWithOverflow w =
  let nm = L.Symbol ("llvm.usub.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callUsubWithOverflow sym memOps) args)

llvmSmulWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSmulWithOverflow w =
  let nm = L.Symbol ("llvm.smul.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callSmulWithOverflow sym memOps) args)

llvmUmulWithOverflow
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUmulWithOverflow w =
  let nm = L.Symbol ("llvm.umul.with.overflow.i" ++ show (natValue w)) in
  [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callUmulWithOverflow sym memOps) args)

llvmCtlz
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w ->
     LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCtlz w =
  let nm = L.Symbol ("llvm.ctlz.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm ( #w, i1 ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callCtlz sym memOps) args)

llvmCttz
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCttz w =
  let nm = L.Symbol ("llvm.cttz.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm ( #w, i1 ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callCttz sym memOps) args)

llvmCtpop
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmCtpop w =
  let nm = L.Symbol ("llvm.ctpop.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callCtpop sym memOps) args)

llvmBitreverse
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr w
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmBitreverse w =
  let nm = L.Symbol ("llvm.bitreverse.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w ) |]
    (\memOps sym args -> Ctx.uncurryAssignment (callBitreverse sym memOps) args)

-- | <https://llvm.org/docs/LangRef.html#llvm-bswap-intrinsics LLVM docs>
llvmBSwapOverride
  :: forall width sym wptr arch p
   . ( 1 <= width, IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => NatRepr width
  -> LLVMOverride p sym arch
         (EmptyCtx ::> BVType (width * 8))
         (BVType (width * 8))
llvmBSwapOverride widthRepr =
  let width8 = natMultiply widthRepr (knownNat @8)
      nm = L.Symbol ("llvm.bswap.i" ++ show (widthVal width8))
  in
    case mulComm widthRepr (knownNat @8) of { Refl ->
    case leqMulMono (knownNat @8) widthRepr :: LeqProof width (width * 8) of { LeqProof ->
    case leqTrans (LeqProof :: LeqProof 1 width)
                  (LeqProof :: LeqProof width (width * 8)) of { LeqProof ->
        -- From the LLVM docs:
        -- declare i16 @llvm.bswap.i16(i16 <id>)
        [llvmOvr| #width8 $nm( #width8 ) |]
        (\_ sym args -> liftIO $
            let vec :: SymBV sym (width * 8)
                vec = regValue (args^._1)
            in bvSwap sym widthRepr vec)
    }}}


llvmX86_pclmulqdq
--declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) #1
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> VectorType (BVType 64)
                   ::> VectorType (BVType 64)
                   ::> BVType 8)
         (VectorType (BVType 64))
llvmX86_pclmulqdq =
  [llvmOvr| <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callX86_pclmulqdq sym memOps) args)


llvmX86_SSE2_storeu_dq
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType (BVType 8))
         UnitType
llvmX86_SSE2_storeu_dq =
  [llvmOvr| void @llvm.x86.sse2.storeu.dq( i8*, <16 x i8> ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callStoreudq sym memOps) args)

------------------------------------------------------------------------
-- ** Implementations

callX86_pclmulqdq :: forall p sym arch wptr r args ret.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  sym ->
  GlobalVar Mem ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (BVType 8) ->
  OverrideSim p sym (LLVM arch) r args ret (RegValue sym (VectorType (BVType 64)))
callX86_pclmulqdq sym _mvar
  (regValue -> xs)
  (regValue -> ys)
  (regValue -> imm) =
    do unless (V.length xs == 2) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError
           ("Vector length mismatch in llvm.x86.pclmulqdq intrinsic")
           (unwords ["Expected <2 x i64>, but got vector of length", show (V.length xs)])
       unless (V.length ys == 2) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError
           ("Vector length mismatch in llvm.x86.pclmulqdq intrinsic")
           (unwords ["Expected <2 x i64>, but got vector of length", show (V.length ys)])
       case BV.asUnsigned <$> asBV imm of
         Just byte ->
           do let xidx = if byte .&. 0x01 == 0 then 0 else 1
              let yidx = if byte .&. 0x10 == 0 then 0 else 1
              liftIO $ doPcmul (xs V.! xidx) (ys V.! yidx)
         _ ->
             liftIO $ addFailedAssertion sym $ AssertFailureSimError
                ("Illegal selector argument to llvm.x86.pclmulqdq")
                (unwords ["Expected concrete value but got", show (printSymExpr imm)])
  where
  doPcmul :: SymBV sym 64 -> SymBV sym 64 -> IO (V.Vector (SymBV sym 64))
  doPcmul x y =
    do r <- carrylessMultiply sym x y
       lo <- bvTrunc sym (knownNat @64) r
       hi <- bvSelect sym (knownNat @64) (knownNat @64) r
       -- NB, little endian because X86
       return $ V.fromList [ lo, hi ]

callStoreudq
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType (BVType 8))
  -> OverrideSim p sym (LLVM arch) r args ret ()
callStoreudq sym mvar
  (regValue -> dest)
  (regValue -> vec) =
    do mem <- readGlobal mvar
       unless (V.length vec == 16) $
          liftIO $ addFailedAssertion sym $ AssertFailureSimError
           ("Vector length mismatch in stored_qu intrinsic.")
           (unwords ["Expected <16 x i8>, but got vector of length", show (V.length vec)])
       mem' <- liftIO $ doStore
                 sym
                 mem
                 dest
                 (VectorRepr (KnownBV @8))
                 (arrayType 16 (bitvectorType (Bytes 1)))
                 noAlignment
                 vec
       writeGlobal mvar mem'


-- Excerpt from the LLVM documentation:
--
-- The llvm.objectsize intrinsic is designed to provide information to
-- the optimizers to determine at compile time whether a) an operation
-- (like memcpy) will overflow a buffer that corresponds to an object,
-- or b) that a runtime check for overflow isn’t necessary. An object
-- in this context means an allocation of a specific class, structure,
-- array, or other object.
--
-- The llvm.objectsize intrinsic takes two arguments. The first
-- argument is a pointer to or into the object. The second argument is
-- a boolean and determines whether llvm.objectsize returns 0 (if
-- true) or -1 (if false) when the object size is unknown. The second
-- argument only accepts constants.
--
-- The llvm.objectsize intrinsic is lowered to a constant representing
-- the size of the object concerned. If the size cannot be determined
-- at compile time, llvm.objectsize returns i32/i64 -1 or 0 (depending
-- on the min argument).
callObjectsize
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize sym _mvar w
  (regValue -> _ptr)
  (regValue -> flag) = liftIO $ do
    -- Ignore the pointer value, and just return the value for unknown, as
    -- defined by the documenatation.  If an `objectsize` invocation survives
    -- through compilation for us to see, that means the compiler could not
    -- determine the value.
    t <- bvIsNonzero sym flag
    z <- bvLit sym w (BV.zero w)
    n <- bvNotBits sym z -- NB: -1 is the boolean negation of zero
    bvIte sym t z n

callObjectsize_null
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize_null sym mvar w ptr flag _nullUnknown = callObjectsize sym mvar w ptr flag

callObjectsize_null_dynamic
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callObjectsize_null_dynamic sym mvar w ptr flag _nullUnknown (regValue -> dynamic) =
  do liftIO $
       do notDynamic <- notPred sym =<< bvIsNonzero sym dynamic
          assert sym notDynamic (AssertFailureSimError "llvm.objectsize called with `dynamic` set to `true`" "")
     callObjectsize sym mvar w ptr flag

callCtlz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCtlz sym _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       assert sym p (AssertFailureSimError "Ctlz called with disallowed zero value" "")
       bvCountLeadingZeros sym val

callFshl
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callFshl sym w x y amt = liftIO $
  do LeqProof <- return (dblPosIsPos (leqProof (knownNat @1) w))
     Just LeqProof <- return (testLeq (addNat w (knownNat @1)) (addNat w w))

     -- concatenate the values together
     xy <- bvConcat sym (regValue x) (regValue y)

     -- The shift argument is treated as an unsigned amount modulo the element size of the arguments.
     m <- bvLit sym w (BV.width w)
     mamt <- bvUrem sym (regValue amt) m
     mamt' <- bvZext sym (addNat w w) mamt

     -- shift left, select high bits
     z <- bvShl sym xy mamt'
     bvSelect sym w w z

callFshr
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callFshr sym w x y amt = liftIO $
  do LeqProof <- return (dblPosIsPos (leqProof (knownNat @1) w))
     LeqProof <- return (addPrefixIsLeq w w)
     Just LeqProof <- return (testLeq (addNat w (knownNat @1)) (addNat w w))

     -- concatenate the values together
     xy <- bvConcat sym (regValue x) (regValue y)

     -- The shift argument is treated as an unsigned amount modulo the element size of the arguments.
     m <- bvLit sym w (BV.width w)
     mamt <- bvUrem sym (regValue amt) m
     mamt' <- bvZext sym (addNat w w) mamt

     -- shift right, select low bits
     z <- bvLshr sym xy mamt'
     bvSelect sym (knownNat @0) w z

callSaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSaddWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- addSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUaddWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- addUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUsubWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- subUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callSsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSsubWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- subSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callSmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSmulWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- mulSignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUmulWithOverflow sym _mvar
  (regValue -> x)
  (regValue -> y) = liftIO $
    do (ov, z) <- mulUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')


callCttz
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCttz sym _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) = liftIO $
    do isNonzero <- bvIsNonzero sym val
       zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
       p <- orPred sym isNonzero zeroOK
       assert sym p (AssertFailureSimError "Cttz called with disallowed zero value" "")
       bvCountTrailingZeros sym val

callCtpop
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callCtpop sym _mvar
  (regValue -> val) = liftIO $ bvPopcount sym val

callBitreverse
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType w))
callBitreverse sym _mvar
  (regValue -> val) = liftIO $ bvBitreverse sym val
