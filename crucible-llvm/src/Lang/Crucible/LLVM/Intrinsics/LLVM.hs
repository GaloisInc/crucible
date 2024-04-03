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
{-# LANGUAGE ImplicitParams #-}
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
import           Control.Monad (foldM, unless)
import           Control.Monad.IO.Class (MonadIO(..))
import           Data.Bits ((.&.))
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )

import           What4.Interface
import           What4.InterpretedFloatingPoint
import qualified What4.SpecialFunctions as W4

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError (SimErrorReason(AssertFailureSimError))

import           Lang.Crucible.LLVM.Bytes (Bytes(..))
import           Lang.Crucible.LLVM.DataLayout (noAlignment)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.QQ( llvmOvr )

import           Lang.Crucible.LLVM.Intrinsics.Common
import qualified Lang.Crucible.LLVM.Intrinsics.Libc as Libc
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

-- | Local helper to make a null pointer in 'OverrideSim'
mkNull
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => OverrideSim p sym ext rtp args ret (LLVMPtr sym wptr)
mkNull = do
  sym <- getSymInterface
  liftIO (mkNullPointer sym PtrWidth)

------------------------------------------------------------------------
-- ** Lists

-- | All \"basic\"/\"monomorphic\" LLVM overrides.
--
-- Can be turned into 'Lang.Crucible.LLVM.Intrinsics.Common.OverrideTemplate's
-- via 'Lang.Crucible.LLVM.Intrinsics.Common.basic_llvm_override'.
basic_llvm_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?lc :: TypeContext, ?memOpts :: MemOptions ) =>
  [SomeLLVMOverride p sym ext]
basic_llvm_overrides =
  [ SomeLLVMOverride llvmLifetimeStartOverride
  , SomeLLVMOverride llvmLifetimeEndOverride
  , SomeLLVMOverride (llvmLifetimeOverrideOverload "start" (knownNat @8))
  , SomeLLVMOverride (llvmLifetimeOverrideOverload "end" (knownNat @8))
  , SomeLLVMOverride (llvmLifetimeOverrideOverload_opaque "start")
  , SomeLLVMOverride (llvmLifetimeOverrideOverload_opaque "end")
  , SomeLLVMOverride (llvmInvariantStartOverride (knownNat @8))
  , SomeLLVMOverride llvmInvariantStartOverride_opaque
  , SomeLLVMOverride (llvmInvariantEndOverride (knownNat @8))
  , SomeLLVMOverride llvmInvariantEndOverride_opaque

  , SomeLLVMOverride llvmAssumeOverride
  , SomeLLVMOverride llvmTrapOverride
  , SomeLLVMOverride llvmUBSanTrapOverride

  , SomeLLVMOverride llvmMemcpyOverride_8_8_32
  , SomeLLVMOverride llvmMemcpyOverride_8_8_32_noalign
  , SomeLLVMOverride llvmMemcpyOverride_8_8_32_noalign_opaque
  , SomeLLVMOverride llvmMemcpyOverride_8_8_64
  , SomeLLVMOverride llvmMemcpyOverride_8_8_64_noalign
  , SomeLLVMOverride llvmMemcpyOverride_8_8_64_noalign_opaque

  , SomeLLVMOverride llvmMemmoveOverride_8_8_32
  , SomeLLVMOverride llvmMemmoveOverride_8_8_32_noalign
  , SomeLLVMOverride llvmMemmoveOverride_8_8_32_noalign_opaque
  , SomeLLVMOverride llvmMemmoveOverride_8_8_64
  , SomeLLVMOverride llvmMemmoveOverride_8_8_64_noalign
  , SomeLLVMOverride llvmMemmoveOverride_8_8_64_noalign_opaque

  , SomeLLVMOverride llvmMemsetOverride_8_32
  , SomeLLVMOverride llvmMemsetOverride_8_32_noalign
  , SomeLLVMOverride llvmMemsetOverride_8_32_noalign_opaque
  , SomeLLVMOverride llvmMemsetOverride_8_64
  , SomeLLVMOverride llvmMemsetOverride_8_64_noalign
  , SomeLLVMOverride llvmMemsetOverride_8_64_noalign_opaque

  , SomeLLVMOverride llvmObjectsizeOverride_32
  , SomeLLVMOverride llvmObjectsizeOverride_64

  , SomeLLVMOverride llvmObjectsizeOverride_32_null
  , SomeLLVMOverride llvmObjectsizeOverride_64_null

  , SomeLLVMOverride llvmObjectsizeOverride_32_null_dynamic
  , SomeLLVMOverride llvmObjectsizeOverride_64_null_dynamic

  , SomeLLVMOverride llvmObjectsizeOverride_32_null_dynamic_opaque
  , SomeLLVMOverride llvmObjectsizeOverride_64_null_dynamic_opaque

  , SomeLLVMOverride llvmPrefetchOverride
  , SomeLLVMOverride llvmPrefetchOverride_opaque
  , SomeLLVMOverride llvmPrefetchOverride_preLLVM10

  , SomeLLVMOverride llvmStacksave
  , SomeLLVMOverride llvmStackrestore

  , SomeLLVMOverride (llvmBSwapOverride (knownNat @2))  -- 16 = 2 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @4))  -- 32 = 4 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @6))  -- 48 = 6 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @8))  -- 64 = 8 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @10)) -- 80 = 10 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @12)) -- 96 = 12 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @14)) -- 112 = 14 * 8
  , SomeLLVMOverride (llvmBSwapOverride (knownNat @16)) -- 128 = 16 * 8

  , SomeLLVMOverride llvmCopysignOverride_F32
  , SomeLLVMOverride llvmCopysignOverride_F64
  , SomeLLVMOverride llvmFabsF32
  , SomeLLVMOverride llvmFabsF64

  , SomeLLVMOverride llvmCeilOverride_F32
  , SomeLLVMOverride llvmCeilOverride_F64
  , SomeLLVMOverride llvmFloorOverride_F32
  , SomeLLVMOverride llvmFloorOverride_F64
  , SomeLLVMOverride llvmSqrtOverride_F32
  , SomeLLVMOverride llvmSqrtOverride_F64
  , SomeLLVMOverride llvmSinOverride_F32
  , SomeLLVMOverride llvmSinOverride_F64
  , SomeLLVMOverride llvmCosOverride_F32
  , SomeLLVMOverride llvmCosOverride_F64
  , SomeLLVMOverride llvmPowOverride_F32
  , SomeLLVMOverride llvmPowOverride_F64
  , SomeLLVMOverride llvmExpOverride_F32
  , SomeLLVMOverride llvmExpOverride_F64
  , SomeLLVMOverride llvmLogOverride_F32
  , SomeLLVMOverride llvmLogOverride_F64
  , SomeLLVMOverride llvmExp2Override_F32
  , SomeLLVMOverride llvmExp2Override_F64
  , SomeLLVMOverride llvmLog2Override_F32
  , SomeLLVMOverride llvmLog2Override_F64
  , SomeLLVMOverride llvmLog10Override_F32
  , SomeLLVMOverride llvmLog10Override_F64
  , SomeLLVMOverride llvmFmaOverride_F32
  , SomeLLVMOverride llvmFmaOverride_F64
  , SomeLLVMOverride llvmFmuladdOverride_F32
  , SomeLLVMOverride llvmFmuladdOverride_F64
  , SomeLLVMOverride llvmIsFpclassOverride_F32
  , SomeLLVMOverride llvmIsFpclassOverride_F64

  -- Some architecture-dependent intrinsics
  , SomeLLVMOverride llvmX86_SSE2_storeu_dq
  , SomeLLVMOverride llvmX86_pclmulqdq
  ]

-- | An LLVM override that is polymorphic in a single argument
newtype Poly1LLVMOverride p sym ext
  = Poly1LLVMOverride (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym ext)

poly1_llvm_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?lc :: TypeContext, ?memOpts :: MemOptions ) =>
  [(String, Poly1LLVMOverride p sym ext)]
poly1_llvm_overrides =
  [ ("llvm.ctlz"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmCtlz w)
    )
  , ("llvm.cttz"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmCttz w)
    )
  , ("llvm.ctpop"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmCtpop w)
    )
  , ("llvm.bitreverse"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmBitreverse w)
    )
  , ("llvm.abs"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmAbsOverride w)
    )

  , ("llvm.fshl"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmFshl w)
    )
  , ("llvm.fshr"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmFshr w)
    )

  , ("llvm.expect"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmExpectOverride w)
    )
  , ("llvm.sadd.with.overflow"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmSaddWithOverflow w)
    )
  , ("llvm.uadd.with.overflow"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmUaddWithOverflow w)
    )
  , ("llvm.ssub.with.overflow"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmSsubWithOverflow w)
    )
  , ("llvm.usub.with.overflow"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmUsubWithOverflow w)
    )
  , ("llvm.smul.with.overflow"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmSmulWithOverflow w)
    )
  , ("llvm.umul.with.overflow"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmUmulWithOverflow w)
    )

  , ("llvm.smax"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmSmax w)
    )
  , ("llvm.smin"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmSmin w)
    )
  , ("llvm.umax"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmUmax w)
    )
  , ("llvm.umin"
    , Poly1LLVMOverride $ \w -> SomeLLVMOverride (llvmUmin w)
    )
  ]

------------------------------------------------------------------------
-- ** Declarations

-- | This intrinsic is currently a no-op.
--
-- We might want to support this in the future to catch undefined memory
-- accesses.
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-start-intrinsic LLVM docs>
llvmLifetimeStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeStartOverride =
  [llvmOvr| void @llvm.lifetime.start( i64, i8* ) |]
  (\_ops _args -> return ())

-- | See comment on 'llvmLifetimeStartOverride'
--
-- <https://llvm.org/docs/LangRef.html#llvm-lifetime-end-intrinsic LLVM docs>
llvmLifetimeEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr) UnitType
llvmLifetimeEndOverride =
  [llvmOvr| void @llvm.lifetime.end( i64, i8* ) |]
  (\_ops _args -> return ())

-- | This is a no-op.
--
-- The language reference doesn't mention the use of this intrinsic.
llvmLifetimeOverrideOverload
  :: forall width sym wptr p ext
   . ( 1 <= width, KnownNat width
     , IsSymInterface sym, HasPtrWidth wptr)
  => String -- ^ "start" or "end"
  -> NatRepr width
  -> LLVMOverride p sym ext
        (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
        UnitType -- It appears in practice that this is always void
llvmLifetimeOverrideOverload startOrEnd w =
  let nm = L.Symbol ("llvm.lifetime." ++ startOrEnd ++ ".p0i" ++ show (widthVal w)) in
    [llvmOvr| void $nm ( i64, #w * ) |]
    (\_ops _args -> return ())

-- | Like 'llvmLifetimeOverrideOverload', but with an opaque pointer type.
llvmLifetimeOverrideOverload_opaque
  :: forall sym wptr p ext
   . (IsSymInterface sym, HasPtrWidth wptr)
  => String -- ^ "start" or "end"
  -> LLVMOverride p sym ext
        (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
        UnitType -- It appears in practice that this is always void
llvmLifetimeOverrideOverload_opaque startOrEnd =
  let nm = L.Symbol ("llvm.lifetime." ++ startOrEnd ++ ".p0") in
    [llvmOvr| void $nm ( i64, ptr ) |]
    (\_ops _args -> return ())

-- | This intrinsic is currently a no-op.
--
-- We might want to support this in the future to catch undefined memory
-- writes.
--
-- <https://llvm.org/docs/LangRef.html#llvm-invariant-start-intrinsic LLVM docs>
llvmInvariantStartOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => NatRepr width
  -> LLVMOverride p sym ext
       (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
       (LLVMPointerType wptr)
llvmInvariantStartOverride w =
  let nm = L.Symbol ("llvm.invariant.start.p0i" ++ show (widthVal w)) in
    [llvmOvr| {}* $nm ( i64, #w * ) |]
    (\_ops _args -> mkNull)

-- | Like 'llvmInvariantStartOverride', but with an opaque pointer type.
llvmInvariantStartOverride_opaque
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
       (EmptyCtx ::> BVType 64 ::> LLVMPointerType wptr)
       (LLVMPointerType wptr)
llvmInvariantStartOverride_opaque =
  let nm = L.Symbol "llvm.invariant.start.p0" in
    [llvmOvr| {}* $nm ( i64, ptr ) |]
    (\_ops _args -> mkNull)

-- | See comment on 'llvmInvariantStartOverride'.
llvmInvariantEndOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => NatRepr width
  -> LLVMOverride p sym ext
       (EmptyCtx ::> LLVMPointerType wptr ::> BVType 64 ::> LLVMPointerType wptr)
       UnitType
llvmInvariantEndOverride w =
  let nm = L.Symbol ("llvm.invariant.end.p0i" ++ show (widthVal w)) in
    [llvmOvr| void $nm ( {}*, i64, #w * ) |]
    (\_ops _args -> return ())

-- | See comment on 'llvmInvariantStartOverride_opaque'.
llvmInvariantEndOverride_opaque
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
       (EmptyCtx ::> LLVMPointerType wptr ::> BVType 64 ::> LLVMPointerType wptr)
       UnitType
llvmInvariantEndOverride_opaque =
  let nm = L.Symbol "llvm.invariant.end.p0" in
    [llvmOvr| void $nm ( {}*, i64, ptr ) |]
    (\_ops _args -> return ())

-- | This instruction is a hint to optimizers, it isn't really useful for us.
--
-- Its runtime behavior of that of Haskell\'s 'const': just ignore the second
-- argument.
llvmExpectOverride
  :: (IsSymInterface sym, 1 <= width)
  => NatRepr width
  -> LLVMOverride p sym ext
       (EmptyCtx ::> BVType width ::> BVType width)
       (BVType width)
llvmExpectOverride w =
  let nm = L.Symbol ("llvm.expect.i" ++ show (widthVal w)) in
    [llvmOvr| #w $nm ( #w, #w ) |]
    (\_ops args ->
        Ctx.uncurryAssignment (\val _ -> pure (regValue val)) args)

-- | This intrinsic asserts that its argument is equal to 1.
--
-- We could have this generate a verification condition, but that would catch
-- clang compiler bugs (or Crucible bugs) more than user code bugs.
llvmAssumeOverride
  :: (IsSymInterface sym)
  => LLVMOverride p sym ext (EmptyCtx ::> BVType 1) UnitType
llvmAssumeOverride =
   [llvmOvr| void @llvm.assume ( i1 ) |]
   (\_ops _args -> return ())

-- | This intrinsic is sometimes inserted by clang, and we interpret it
--   as an assertion failure, similar to calling @abort()@.
llvmTrapOverride
  :: (IsSymInterface sym)
  => LLVMOverride p sym ext EmptyCtx UnitType
llvmTrapOverride =
  [llvmOvr| void @llvm.trap() |]
  (\_ops _args -> 
    ovrWithBackend $ \bak ->
      liftIO $ addFailedAssertion bak $ AssertFailureSimError "llvm.trap() called" "")

-- | This is like @llvm.trap()@, but with an argument indicating which sort of
-- undefined behavior was trapped. The argument acts as an index into
-- <https://github.com/llvm/llvm-project/blob/650bbc56203c947bb85176c40ca9c7c7a91c3c57/clang/lib/CodeGen/CodeGenFunction.h#L118-L143 this list>.
-- Ideally, we would do something intelligent with this argument—see #368.
llvmUBSanTrapOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym ext (EmptyCtx ::> BVType 8) UnitType
llvmUBSanTrapOverride =
  [llvmOvr| void @llvm.ubsantrap( i8 ) |]
  (\_ops _args -> 
    ovrWithBackend $ \bak ->
      liftIO $ addFailedAssertion bak $ AssertFailureSimError "llvm.ubsantrap() called" "")

llvmStacksave
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext EmptyCtx (LLVMPointerType wptr)
llvmStacksave =
  [llvmOvr| i8* @llvm.stacksave() |]
  (\_memOps _args -> mkNull)

llvmStackrestore
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr) UnitType
llvmStackrestore =
  [llvmOvr| void @llvm.stackrestore( i8* ) |]
  (\_memOps _args -> return ())

llvmMemmoveOverride_8_8_32
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32 =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i32( i8*, i8*, i32, i32, i1 ) |]
  (\memOps args ->
     Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemmove memOps dst src len v) args)

llvmMemmoveOverride_8_8_32_noalign
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32_noalign =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i32( i8*, i8*, i32, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemmove memOps) args)

llvmMemmoveOverride_8_8_32_noalign_opaque
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_32_noalign_opaque =
  [llvmOvr| void @llvm.memmove.p0.p0.i32( ptr, ptr, i32, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemmove memOps) args)


llvmMemmoveOverride_8_8_64
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64 =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i64( i8*, i8*, i64, i32, i1 ) |]
  (\memOps args ->
      Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemmove memOps dst src len v) args)

llvmMemmoveOverride_8_8_64_noalign
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64_noalign =
  [llvmOvr| void @llvm.memmove.p0i8.p0i8.i64( i8*, i8*, i64, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemmove memOps) args)

llvmMemmoveOverride_8_8_64_noalign_opaque
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 1)
         UnitType
llvmMemmoveOverride_8_8_64_noalign_opaque =
  [llvmOvr| void @llvm.memmove.p0.p0.i64( ptr, ptr, i64, i1 ) |]
  (\memOps args ->
      Ctx.uncurryAssignment (Libc.callMemmove memOps) args)


llvmMemsetOverride_8_64
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64 =
  [llvmOvr| void @llvm.memset.p0i8.i64( i8*, i8, i64, i32, i1 ) |]
  (\memOps args ->
    Ctx.uncurryAssignment (\dst val len _align v -> Libc.callMemset memOps dst val len v) args)

llvmMemsetOverride_8_64_noalign
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64_noalign =
  [llvmOvr| void @llvm.memset.p0i8.i64( i8*, i8, i64, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemset memOps) args)

llvmMemsetOverride_8_64_noalign_opaque
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 64
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_64_noalign_opaque =
  [llvmOvr| void @llvm.memset.p0.i64( ptr, i8, i64, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemset memOps) args)


llvmMemsetOverride_8_32
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32 =
  [llvmOvr| void @llvm.memset.p0i8.i32( i8*, i8, i32, i32, i1 ) |]
  (\memOps args ->
    Ctx.uncurryAssignment (\dst val len _align v -> Libc.callMemset memOps dst val len v) args)

llvmMemsetOverride_8_32_noalign
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32_noalign =
  [llvmOvr| void @llvm.memset.p0i8.i32( i8*, i8, i32, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemset memOps) args)

llvmMemsetOverride_8_32_noalign_opaque
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType  8
                   ::> BVType 32
                   ::> BVType 1)
         UnitType
llvmMemsetOverride_8_32_noalign_opaque =
  [llvmOvr| void @llvm.memset.p0.i32( ptr, i8, i32, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemset memOps) args)


llvmMemcpyOverride_8_8_32
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32 =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i32( i8*, i8*, i32, i32, i1 ) |]
  (\memOps args ->
    Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemcpy memOps dst src len v) args)

llvmMemcpyOverride_8_8_32_noalign
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32_noalign =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i32( i8*, i8*, i32, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemcpy memOps) args)

llvmMemcpyOverride_8_8_32_noalign_opaque
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
          (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                    ::> BVType 32 ::> BVType 1)
          UnitType
llvmMemcpyOverride_8_8_32_noalign_opaque =
  [llvmOvr| void @llvm.memcpy.p0.p0.i32( ptr, ptr, i32, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemcpy memOps) args)


llvmMemcpyOverride_8_8_64
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 32 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64 =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i64( i8*, i8*, i64, i32, i1 ) |]
  (\memOps args ->
    Ctx.uncurryAssignment (\dst src len _align v -> Libc.callMemcpy memOps dst src len v) args)

llvmMemcpyOverride_8_8_64_noalign
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64_noalign =
  [llvmOvr| void @llvm.memcpy.p0i8.p0i8.i64( i8*, i8*, i64, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemcpy memOps) args)

llvmMemcpyOverride_8_8_64_noalign_opaque
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr
                   ::> BVType 64 ::> BVType 1)
         UnitType
llvmMemcpyOverride_8_8_64_noalign_opaque =
  [llvmOvr| void @llvm.memcpy.p0.p0.i64( ptr, ptr, i64, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (Libc.callMemcpy memOps) args)


llvmObjectsizeOverride_32
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32 =
  [llvmOvr| i32 @llvm.objectsize.i32.p0i8( i8*, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize memOps knownNat) args)

llvmObjectsizeOverride_32_null
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32_null =
  [llvmOvr| i32 @llvm.objectsize.i32.p0i8( i8*, i1, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize_null memOps knownNat) args)

llvmObjectsizeOverride_32_null_dynamic
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32_null_dynamic =
  [llvmOvr| i32 @llvm.objectsize.i32.p0i8( i8*, i1, i1, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize_null_dynamic memOps knownNat) args)

llvmObjectsizeOverride_32_null_dynamic_opaque
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1 ::> BVType 1) (BVType 32)
llvmObjectsizeOverride_32_null_dynamic_opaque =
  [llvmOvr| i32 @llvm.objectsize.i32.p0( ptr, i1, i1, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize_null_dynamic memOps knownNat) args)

llvmObjectsizeOverride_64
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64 =
  [llvmOvr| i64 @llvm.objectsize.i64.p0i8( i8*, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize memOps knownNat) args)

llvmObjectsizeOverride_64_null
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64_null =
  [llvmOvr| i64 @llvm.objectsize.i64.p0i8( i8*, i1, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize_null memOps knownNat) args)

llvmObjectsizeOverride_64_null_dynamic
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64_null_dynamic =
  [llvmOvr| i64 @llvm.objectsize.i64.p0i8( i8*, i1, i1, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize_null_dynamic memOps knownNat) args)

llvmObjectsizeOverride_64_null_dynamic_opaque
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType 1 ::> BVType 1 ::> BVType 1) (BVType 64)
llvmObjectsizeOverride_64_null_dynamic_opaque =
  [llvmOvr| i64 @llvm.objectsize.i64.p0( ptr, i1, i1, i1 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callObjectsize_null_dynamic memOps knownNat) args)

-- | This instruction is a hint to code generators, which means that it is a
-- no-op for us.
--
-- <https://releases.llvm.org/12.0.0/docs/LangRef.html#llvm-prefetch-intrinsic LLVM docs>
llvmPrefetchOverride ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  LLVMOverride p sym ext
    (EmptyCtx ::> LLVMPointerType wptr ::> BVType 32 ::> BVType 32 ::> BVType 32)
    UnitType
llvmPrefetchOverride =
  [llvmOvr| void @llvm.prefetch.p0i8( i8*, i32, i32, i32 ) |]
  (\_memOps _args -> pure ())

-- | Like 'llvmPrefetchOverride', but with an opaque pointer type.
llvmPrefetchOverride_opaque ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  LLVMOverride p sym ext
    (EmptyCtx ::> LLVMPointerType wptr ::> BVType 32 ::> BVType 32 ::> BVType 32)
    UnitType
llvmPrefetchOverride_opaque =
  [llvmOvr| void @llvm.prefetch.p0( ptr, i32, i32, i32 ) |]
  (\_memOps _args -> pure ())

-- | This instruction is a hint to code generators, which means that it is a
-- no-op for us.
--
-- See also 'llvmPrefetchOverride'. This version exists for compatibility with
-- pre-10 versions of LLVM, where llvm.prefetch always assumed that the first
-- argument resides in address space 0.
--
-- <https://releases.llvm.org/12.0.0/docs/LangRef.html#llvm-prefetch-intrinsic LLVM docs>
llvmPrefetchOverride_preLLVM10 ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  LLVMOverride p sym ext
    (EmptyCtx ::> LLVMPointerType wptr ::> BVType 32 ::> BVType 32 ::> BVType 32)
    UnitType
llvmPrefetchOverride_preLLVM10 =
  [llvmOvr| void @llvm.prefetch( i8*, i32, i32, i32 ) |]
  (\_memOps _args -> pure ())

llvmFshl ::
  (1 <= w, IsSymInterface sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
    (EmptyCtx ::> BVType w ::> BVType w ::> BVType w)
    (BVType w)
llvmFshl w =
 let nm = L.Symbol ("llvm.fshl.i" ++ show (natValue w)) in
 [llvmOvr| #w $nm ( #w, #w, #w ) |]
 (\_memOps args -> Ctx.uncurryAssignment (callFshl w) args)

llvmFshr ::
  (1 <= w, IsSymInterface sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
    (EmptyCtx ::> BVType w ::> BVType w ::> BVType w)
    (BVType w)
llvmFshr w =
 let nm = L.Symbol ("llvm.fshr.i" ++ show (natValue w)) in
 [llvmOvr| #w $nm ( #w, #w, #w ) |]
 (\_memOps args -> Ctx.uncurryAssignment (callFshr w) args)

llvmSaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSaddWithOverflow w =
  let nm = L.Symbol ("llvm.sadd.with.overflow.i" ++ show (natValue w)) in
  [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
  (\memOps args -> Ctx.uncurryAssignment (callSaddWithOverflow memOps) args)

llvmUaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUaddWithOverflow w =
  let nm = L.Symbol ("llvm.uadd.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callUaddWithOverflow memOps) args)


llvmSsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSsubWithOverflow w =
  let nm = L.Symbol ("llvm.ssub.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callSsubWithOverflow memOps) args)


llvmUsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUsubWithOverflow w =
  let nm = L.Symbol ("llvm.usub.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callUsubWithOverflow memOps) args)

llvmSmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmSmulWithOverflow w =
  let nm = L.Symbol ("llvm.smul.with.overflow.i" ++ show (natValue w)) in
    [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callSmulWithOverflow memOps) args)

llvmUmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType w)
         (StructType (EmptyCtx ::> BVType w ::> BVType 1))
llvmUmulWithOverflow w =
  let nm = L.Symbol ("llvm.umul.with.overflow.i" ++ show (natValue w)) in
  [llvmOvr| { #w, i1 } $nm ( #w, #w ) |]
  (\memOps args -> Ctx.uncurryAssignment (callUmulWithOverflow memOps) args)

llvmUmax ::
  (1 <= w, IsSymInterface sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
     (EmptyCtx ::> BVType w ::> BVType w)
     (BVType w)
llvmUmax w =
  let nm = L.Symbol ("llvm.umax.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callUmax memOps) args)

llvmUmin ::
  (1 <= w, IsSymInterface sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
     (EmptyCtx ::> BVType w ::> BVType w)
     (BVType w)
llvmUmin w =
  let nm = L.Symbol ("llvm.umin.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callUmin memOps) args)

llvmSmax ::
  (1 <= w, IsSymInterface sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
     (EmptyCtx ::> BVType w ::> BVType w)
     (BVType w)
llvmSmax w =
  let nm = L.Symbol ("llvm.smax.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callSmax memOps) args)

llvmSmin ::
  (1 <= w, IsSymInterface sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
     (EmptyCtx ::> BVType w ::> BVType w)
     (BVType w)
llvmSmin w =
  let nm = L.Symbol ("llvm.smin.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w, #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callSmin memOps) args)

llvmCtlz
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w ->
     LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCtlz w =
  let nm = L.Symbol ("llvm.ctlz.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm ( #w, i1 ) |]
    (\memOps args -> Ctx.uncurryAssignment (callCtlz memOps) args)

llvmCttz
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w
  -> LLVMOverride p sym ext
         (EmptyCtx ::> BVType w ::> BVType 1)
         (BVType w)
llvmCttz w =
  let nm = L.Symbol ("llvm.cttz.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm ( #w, i1 ) |]
    (\memOps args -> Ctx.uncurryAssignment (callCttz memOps) args)

llvmCtpop
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w
  -> LLVMOverride p sym ext
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmCtpop w =
  let nm = L.Symbol ("llvm.ctpop.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callCtpop memOps) args)

llvmBitreverse
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w
  -> LLVMOverride p sym ext
         (EmptyCtx ::> BVType w)
         (BVType w)
llvmBitreverse w =
  let nm = L.Symbol ("llvm.bitreverse.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w ) |]
    (\memOps args -> Ctx.uncurryAssignment (callBitreverse memOps) args)

-- | <https://llvm.org/docs/LangRef.html#llvm-bswap-intrinsics LLVM docs>
llvmBSwapOverride
  :: forall width sym p ext
   . ( 1 <= width, IsSymInterface sym)
  => NatRepr width
  -> LLVMOverride p sym ext
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
        (\_ args -> Ctx.uncurryAssignment (Libc.callBSwap widthRepr) args)
    }}}

llvmAbsOverride ::
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  NatRepr w ->
  LLVMOverride p sym ext
     (EmptyCtx ::> BVType w ::> BVType 1)
     (BVType w)
llvmAbsOverride w =
  let nm = L.Symbol ("llvm.abs.i" ++ show (natValue w)) in
    [llvmOvr| #w $nm( #w, i1 ) |]
    (\mvar args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (Libc.callLLVMAbs callStack w) args)

llvmCopysignOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCopysignOverride_F32 =
  [llvmOvr| float @llvm.copysign.f32( float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment callCopysign args)

llvmCopysignOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCopysignOverride_F64 =
  [llvmOvr| double @llvm.copysign.f64( double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment callCopysign args)


llvmFabsF32
  :: forall sym p ext
   . ( IsSymInterface sym)
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType SingleFloat)
        (FloatType SingleFloat)
llvmFabsF32 =
  [llvmOvr| float @llvm.fabs.f32( float ) |]
  (\_memOps (Empty :> (regValue -> x)) -> do
    sym <- getSymInterface
    liftIO (iFloatAbs @_ @SingleFloat sym x))


llvmFabsF64
  :: forall sym p ext
   . ( IsSymInterface sym)
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType DoubleFloat)
        (FloatType DoubleFloat)
llvmFabsF64 =
  [llvmOvr| double @llvm.fabs.f64( double ) |]
  (\_memOps (Empty :> (regValue -> x)) -> do
    sym <- getSymInterface
    liftIO (iFloatAbs @_ @DoubleFloat sym x))

llvmCeilOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCeilOverride_F32 =
  [llvmOvr| float @llvm.ceil.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callCeil args)

llvmCeilOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCeilOverride_F64 =
  [llvmOvr| double @llvm.ceil.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callCeil args)

llvmFloorOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmFloorOverride_F32 =
  [llvmOvr| float @llvm.floor.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callFloor args)

llvmFloorOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmFloorOverride_F64 =
  [llvmOvr| double @llvm.floor.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callFloor args)

llvmSqrtOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSqrtOverride_F32 =
  [llvmOvr| float @llvm.sqrt.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callSqrt args)

llvmSqrtOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSqrtOverride_F64 =
  [llvmOvr| double @llvm.sqrt.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callSqrt args)

llvmSinOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSinOverride_F32 =
  [llvmOvr| float @llvm.sin.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Sin) args)

llvmSinOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSinOverride_F64 =
  [llvmOvr| double @llvm.sin.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Sin) args)

llvmCosOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCosOverride_F32 =
  [llvmOvr| float @llvm.cos.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Cos) args)

llvmCosOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCosOverride_F64 =
  [llvmOvr| double @llvm.cos.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Cos) args)

llvmPowOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmPowOverride_F32 =
  [llvmOvr| float @llvm.pow.f32( float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction2 W4.Pow) args)

llvmPowOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmPowOverride_F64 =
  [llvmOvr| double @llvm.pow.f64( double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction2 W4.Pow) args)

llvmExpOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExpOverride_F32 =
  [llvmOvr| float @llvm.exp.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Exp) args)

llvmExpOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExpOverride_F64 =
  [llvmOvr| double @llvm.exp.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Exp) args)

llvmLogOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLogOverride_F32 =
  [llvmOvr| float @llvm.log.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Log) args)

llvmLogOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLogOverride_F64 =
  [llvmOvr| double @llvm.log.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Log) args)

llvmExp2Override_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExp2Override_F32 =
  [llvmOvr| float @llvm.exp2.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Exp2) args)

llvmExp2Override_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExp2Override_F64 =
  [llvmOvr| double @llvm.exp2.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Exp2) args)

llvmLog2Override_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog2Override_F32 =
  [llvmOvr| float @llvm.log2.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Log2) args)

llvmLog2Override_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog2Override_F64 =
  [llvmOvr| double @llvm.log2.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Log2) args)

llvmLog10Override_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog10Override_F32 =
  [llvmOvr| float @llvm.log10.f32( float ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Log10) args)

llvmLog10Override_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog10Override_F64 =
  [llvmOvr| double @llvm.log10.f64( double ) |]
  (\_memOps args -> Ctx.uncurryAssignment (Libc.callSpecialFunction1 W4.Log10) args)

llvmIsFpclassOverride_F32 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType SingleFloat
               ::> BVType 32)
     (BVType 1)
llvmIsFpclassOverride_F32 =
  [llvmOvr| i1 @llvm.is.fpclass.f32( float, i32 ) |]
  (\_memOps args -> Ctx.uncurryAssignment callIsFpclass args)

llvmIsFpclassOverride_F64 ::
  IsSymInterface sym =>
  LLVMOverride p sym ext
     (EmptyCtx ::> FloatType DoubleFloat
               ::> BVType 32)
     (BVType 1)
llvmIsFpclassOverride_F64 =
  [llvmOvr| i1 @llvm.is.fpclass.f64( double, i32 ) |]
  (\_memOps args -> Ctx.uncurryAssignment callIsFpclass args)

llvmFmaOverride_F32 ::
     forall sym p ext
   . IsSymInterface sym
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType SingleFloat
                  ::> FloatType SingleFloat
                  ::> FloatType SingleFloat)
        (FloatType SingleFloat)
llvmFmaOverride_F32 =
  [llvmOvr| float @llvm.fma.f32( float, float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callFMA args)

llvmFmaOverride_F64 ::
     forall sym p ext
   . IsSymInterface sym
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType DoubleFloat
                  ::> FloatType DoubleFloat
                  ::> FloatType DoubleFloat)
        (FloatType DoubleFloat)
llvmFmaOverride_F64 =
  [llvmOvr| double @llvm.fma.f64( double, double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callFMA args)

llvmFmuladdOverride_F32 ::
     forall sym p ext
   . IsSymInterface sym
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType SingleFloat
                  ::> FloatType SingleFloat
                  ::> FloatType SingleFloat)
        (FloatType SingleFloat)
llvmFmuladdOverride_F32 =
  [llvmOvr| float @llvm.fmuladd.f32( float, float, float ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callFMA args)

llvmFmuladdOverride_F64 ::
     forall sym p ext
   . IsSymInterface sym
  => LLVMOverride p sym ext
        (EmptyCtx ::> FloatType DoubleFloat
                  ::> FloatType DoubleFloat
                  ::> FloatType DoubleFloat)
        (FloatType DoubleFloat)
llvmFmuladdOverride_F64 =
  [llvmOvr| double @llvm.fmuladd.f64( double, double, double ) |]
  (\_memOps args -> Ctx.uncurryAssignment Libc.callFMA args)


llvmX86_pclmulqdq
--declare <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) #1
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> VectorType (BVType 64)
                   ::> VectorType (BVType 64)
                   ::> BVType 8)
         (VectorType (BVType 64))
llvmX86_pclmulqdq =
  [llvmOvr| <2 x i64> @llvm.x86.pclmulqdq(<2 x i64>, <2 x i64>, i8) |]
  (\memOps args -> Ctx.uncurryAssignment (callX86_pclmulqdq memOps) args)


llvmX86_SSE2_storeu_dq
  :: ( IsSymInterface sym
     , HasLLVMAnn sym
     , HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType (BVType 8))
         UnitType
llvmX86_SSE2_storeu_dq =
  [llvmOvr| void @llvm.x86.sse2.storeu.dq( i8*, <16 x i8> ) |]
  (\memOps args -> Ctx.uncurryAssignment (callStoreudq memOps) args)

------------------------------------------------------------------------
-- ** Implementations

callX86_pclmulqdq :: forall p sym ext wptr r args ret.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  GlobalVar Mem ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (VectorType (BVType 64)) ->
  RegEntry sym (BVType 8) ->
  OverrideSim p sym ext r args ret (RegValue sym (VectorType (BVType 64)))
callX86_pclmulqdq _mvar
  (regValue -> xs)
  (regValue -> ys)
  (regValue -> imm) =
    ovrWithBackend $ \bak -> do 
      unless (V.length xs == 2) $
         liftIO $ addFailedAssertion bak $ AssertFailureSimError
          ("Vector length mismatch in llvm.x86.pclmulqdq intrinsic")
          (unwords ["Expected <2 x i64>, but got vector of length", show (V.length xs)])
      unless (V.length ys == 2) $
         liftIO $ addFailedAssertion bak $ AssertFailureSimError
          ("Vector length mismatch in llvm.x86.pclmulqdq intrinsic")
          (unwords ["Expected <2 x i64>, but got vector of length", show (V.length ys)])
      case BV.asUnsigned <$> asBV imm of
        Just byte ->
          do let xidx = if byte .&. 0x01 == 0 then 0 else 1
             let yidx = if byte .&. 0x10 == 0 then 0 else 1
             let sym = backendGetSym bak
             liftIO $ doPcmul sym (xs V.! xidx) (ys V.! yidx)
        _ ->
            liftIO $ addFailedAssertion bak $ AssertFailureSimError
               ("Illegal selector argument to llvm.x86.pclmulqdq")
               (unwords ["Expected concrete value but got", show (printSymExpr imm)])
  where

  doPcmul :: sym -> SymBV sym 64 -> SymBV sym 64 -> IO (V.Vector (SymBV sym 64))
  doPcmul sym x y =
    do r <- carrylessMultiply sym x y
       lo <- bvTrunc sym (knownNat @64) r
       hi <- bvSelect sym (knownNat @64) (knownNat @64) r
       -- NB, little endian because X86
       return $ V.fromList [ lo, hi ]

callStoreudq
  :: ( IsSymInterface sym
     , HasLLVMAnn sym
     , HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType (BVType 8))
  -> OverrideSim p sym ext r args ret ()
callStoreudq mvar
  (regValue -> dest)
  (regValue -> vec) =
    ovrWithBackend $ \bak -> do
      mem <- readGlobal mvar
      unless (V.length vec == 16) $
         liftIO $ addFailedAssertion bak $ AssertFailureSimError
          ("Vector length mismatch in stored_qu intrinsic.")
          (unwords ["Expected <16 x i8>, but got vector of length", show (V.length vec)])
      mem' <- liftIO $ doStore
                bak
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
  => GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callObjectsize _mvar w
  (regValue -> _ptr)
  (regValue -> flag) = do
    sym <- getSymInterface
    liftIO $ do
      -- Ignore the pointer value, and just return the value for unknown, as
      -- defined by the documenatation.  If an `objectsize` invocation survives
      -- through compilation for us to see, that means the compiler could not
      -- determine the value.
      t <- bvIsNonzero sym flag
      z <- bvZero sym w
      n <- bvNotBits sym z -- NB: -1 is the boolean negation of zero
      bvIte sym t z n

callObjectsize_null
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callObjectsize_null mvar w ptr flag _nullUnknown = callObjectsize mvar w ptr flag

callObjectsize_null_dynamic
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> NatRepr w
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callObjectsize_null_dynamic mvar w ptr flag _nullUnknown (regValue -> dynamic) =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
    liftIO $
      do notDynamic <- notPred sym =<< bvIsNonzero sym dynamic
         assert bak notDynamic (AssertFailureSimError "llvm.objectsize called with `dynamic` set to `true`" "")
    callObjectsize mvar w ptr flag

callCtlz
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callCtlz _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) =
    ovrWithBackend $ \bak -> do
      sym <- getSymInterface
      liftIO $ do
        isNonzero <- bvIsNonzero sym val
        zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
        p <- orPred sym isNonzero zeroOK
        assert bak p (AssertFailureSimError "Ctlz called with disallowed zero value" "")
        bvCountLeadingZeros sym val

callFshl
  :: (1 <= w, IsSymInterface sym)
  => NatRepr w
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callFshl w x y amt =
  ovrWithBackend $ \bak -> liftIO $ do
     let sym = backendGetSym bak
     LeqProof <- return (dblPosIsPos (leqProof (knownNat @1) w))
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
  => NatRepr w
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callFshr w x y amt =
  ovrWithBackend $ \bak -> liftIO $ do
    LeqProof <- return (dblPosIsPos (leqProof (knownNat @1) w))
    LeqProof <- return (addPrefixIsLeq w w)
    Just LeqProof <- return (testLeq (addNat w (knownNat @1)) (addNat w w))
    let sym = backendGetSym bak

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
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSaddWithOverflow _mvar
  (regValue -> x)
  (regValue -> y) =
    ovrWithBackend $ \bak -> liftIO $ do
      let sym = backendGetSym bak
      (ov, z) <- addSignedOF sym x y
      ov' <- predToBV sym ov (knownNat @1)
      return (Empty :> RV z :> RV ov')

callUaddWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUaddWithOverflow _mvar
  (regValue -> x)
  (regValue -> y) = do
    sym <- getSymInterface
    liftIO $ do
       (ov, z) <- addUnsignedOF sym x y
       ov' <- predToBV sym ov (knownNat @1)
       return (Empty :> RV z :> RV ov')

callUsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUsubWithOverflow _mvar
  (regValue -> x)
  (regValue -> y) = do
    sym <- getSymInterface
    liftIO $ do
      (ov, z) <- subUnsignedOF sym x y
      ov' <- predToBV sym ov (knownNat @1)
      return (Empty :> RV z :> RV ov')

callSsubWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSsubWithOverflow _mvar
  (regValue -> x)
  (regValue -> y) = do
    sym <- getSymInterface
    liftIO $ do
      (ov, z) <- subSignedOF sym x y
      ov' <- predToBV sym ov (knownNat @1)
      return (Empty :> RV z :> RV ov')

callSmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callSmulWithOverflow _mvar
  (regValue -> x)
  (regValue -> y) = do
    sym <- getSymInterface
    liftIO $ do
      (ov, z) <- mulSignedOF sym x y
      ov' <- predToBV sym ov (knownNat @1)
      return (Empty :> RV z :> RV ov')

callUmulWithOverflow
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (StructType (EmptyCtx ::> BVType w ::> BVType 1)))
callUmulWithOverflow _mvar
  (regValue -> x)
  (regValue -> y) = do
    sym <- getSymInterface
    liftIO $ do
      (ov, z) <- mulUnsignedOF sym x y
      ov' <- predToBV sym ov (knownNat @1)
      return (Empty :> RV z :> RV ov')

callUmax
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callUmax _mvar (regValue -> x) (regValue -> y) = do
  sym <- getSymInterface
  liftIO $ do
    xGtY <- bvUgt sym x y
    bvIte sym xGtY x y

callUmin
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callUmin _mvar (regValue -> x) (regValue -> y) = do
  sym <- getSymInterface
  liftIO $ do
    xLtY <- bvUlt sym x y
    bvIte sym xLtY x y

callSmax
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callSmax _mvar (regValue -> x) (regValue -> y) = do
  sym <- getSymInterface
  liftIO $ do
    xGtY <- bvSgt sym x y
    bvIte sym xGtY x y

callSmin
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callSmin _mvar (regValue -> x) (regValue -> y) = do
  sym <- getSymInterface
  liftIO $ do
    xLtY <- bvSlt sym x y
    bvIte sym xLtY x y


callCttz
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callCttz _mvar
  (regValue -> val)
  (regValue -> isZeroUndef) =
    ovrWithBackend $ \bak -> do
      let sym = backendGetSym bak
      liftIO $ do
        isNonzero <- bvIsNonzero sym val
        zeroOK    <- notPred sym =<< bvIsNonzero sym isZeroUndef
        p <- orPred sym isNonzero zeroOK
        assert bak p (AssertFailureSimError "Cttz called with disallowed zero value" "")
        bvCountTrailingZeros sym val

callCtpop
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callCtpop _mvar
  (regValue -> val) = do
    sym <- getSymInterface
    liftIO $ bvPopcount sym val

callBitreverse
  :: (1 <= w, IsSymInterface sym)
  => GlobalVar Mem
  -> RegEntry sym (BVType w)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callBitreverse _mvar
  (regValue -> val) = do
    sym <- getSymInterface
    liftIO $ bvBitreverse sym val

-- | Strictly speaking, this doesn't quite conform to the C99 description of
-- @copysign@, since @copysign(NaN, -1.0)@ should return @NaN@ with a negative
-- sign bit. @libBF@ does not provide a way to distinguish between @NaN@ values
-- with different sign bits, however, so @copysign@ will always turn a @NaN@
-- argument into a positive, \"quiet\" @NaN@.
callCopysign ::
  forall fi p sym ext r args ret.
  IsSymInterface sym =>
  RegEntry sym (FloatType fi) ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callCopysign
  (regValue -> x)
  (regValue -> y) = do
    sym <- getSymInterface
    liftIO $ do
      xIsNeg    <- iFloatIsNeg @_ @fi sym x
      yIsNeg    <- iFloatIsNeg @_ @fi sym y
      signsSame <- eqPred sym xIsNeg yIsNeg
      xNegated  <- iFloatNeg @_ @fi sym x
      iFloatIte @_ @fi sym signsSame x xNegated

-- | An implementation of the @llvm.is.fpclass@ intrinsic. This essentially
-- combines several different floating-point checks (checking for @NaN@,
-- infinity, zero, etc.) into a single function. The second argument is a
-- bitmask that controls which properties to check of the first argument.
-- The different checks in the bitmask are described by the table here:
-- <https://llvm.org/docs/LangRef.html#id1566>
--
-- The specification requires being able to distinguish between signaling
-- @NaN@s (bit 0 of the bitmask) and quit @NaN@s (bit 1 of the bitmask), but
-- @crucible-llvm@ does not have the ability to do this. As a result, both
-- @NaN@ checks will always return true in this implementation, regardless of
-- whether they are signaling or quiet @NaN@s.
callIsFpclass ::
  forall fi p sym ext r args ret.
  IsSymInterface sym =>
  RegEntry sym (FloatType fi) ->
  RegEntry sym (BVType 32) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType 1))
callIsFpclass regOp@(regValue -> op) (regValue -> test) = do
  sym <- getSymInterface
  let w1 = knownNat @1
  bv1 <- liftIO $ bvZero sym w1
  bv0 <- liftIO $ bvOne sym w1

  let negative bit = liftIO $ do
        isNeg <- iFloatIsNeg @_ @fi sym op
        liftIO $ bvIte sym isNeg bit bv0

  let positive bit = liftIO $ do
        isPos <- iFloatIsPos @_ @fi sym op
        liftIO $ bvIte sym isPos bit bv0

  let negAndPos doCheck = liftIO $ do
        check <- doCheck
        checkN <- negative check
        checkP <- positive check
        pure (checkN, checkP)

  let callIsInf x = do
        isInf <- iFloatIsInf @_ @fi sym x
        bvIte sym isInf bv1 bv0

  let callIsNormal x = do
        isNorm <- iFloatIsNorm @_ @fi sym x
        bvIte sym isNorm bv1 bv0

  let callIsSubnormal x = do
        isSubnorm <- iFloatIsSubnorm @_ @fi sym x
        bvIte sym isSubnorm bv1 bv0

  let callIsZero x = do
        is0 <- iFloatIsZero @_ @fi sym x
        bvIte sym is0 bv1 bv0

  isNan <- Libc.callIsnan w1 regOp
  (isInfN, isInfP) <- negAndPos $ callIsInf op
  (isNormN, isNormP) <- negAndPos $ callIsNormal op
  (isSubnormN, isSubnormP) <- negAndPos $ callIsSubnormal op
  (isZeroN, isZeroP) <- negAndPos $ callIsZero op

  foldM
    (\bits (bitNum, check) -> liftIO $ do
        isBitSet <- liftIO $ testBitBV sym bitNum test
        newBit <- liftIO $ bvIte sym isBitSet check bv0
        liftIO $ bvOrBits sym newBit bits)
    bv0
    [ (0, isNan)      -- Signaling NaN
    , (1, isNan)      -- Quiet NaN
    , (2, isInfN)     -- Negative infinity
    , (3, isNormN)    -- Negative normal
    , (4, isSubnormN) -- Negative subnormal
    , (5, isZeroN)    -- Negative zero
    , (6, isZeroP)    -- Positive zero
    , (7, isSubnormP) -- Positive subnormal
    , (8, isNormP)    -- Positive normal
    , (9, isInfP)     -- Positive infinity
    ]
