-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics
-- Description      : Override definitions for LLVM intrinsic and basic
--                    library functions
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Intrinsics
( LLVM
, llvmIntrinsicTypes
, LLVMOverride(..)

, register_llvm_overrides
, register_llvm_overrides_
, llvmDeclToFunHandleRepr

, module Lang.Crucible.LLVM.Intrinsics.Common
, module Lang.Crucible.LLVM.Intrinsics.Options
) where

import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad (forM_)
import           Control.Monad.Reader (ReaderT(..))
import           Control.Monad.Trans.Maybe
import           Data.Foldable (asum)
import           Data.List (stripPrefix, tails, isPrefixOf)
import qualified Text.LLVM.AST as L

import qualified ABI.Itanium as ABI
import qualified Data.Parameterized.Map as MapF

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim

import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVM)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Types
import           Lang.Crucible.LLVM.TypeContext (TypeContext)

import           Lang.Crucible.LLVM.Intrinsics.Common
import qualified Lang.Crucible.LLVM.Intrinsics.LLVM as LLVM
import qualified Lang.Crucible.LLVM.Intrinsics.Libc as Libc
import qualified Lang.Crucible.LLVM.Intrinsics.Libcxx as Libcxx
import           Lang.Crucible.LLVM.Intrinsics.Options

llvmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmIntrinsicTypes =
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_memory") IntrinsicMuxFn $
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn $
   MapF.empty

-- | Register all declare and define overrides
register_llvm_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch
  , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  L.Module ->
  [OverrideTemplate p sym arch rtp l a] {- ^ Additional "define" overrides -} ->
  [OverrideTemplate p sym arch rtp l a] {- ^ Additional "declare" overrides -} ->
  LLVMContext arch ->
  OverrideSim p sym LLVM rtp l a ()
register_llvm_overrides llvmModule defineOvrs declareOvrs llvmctx =
  do register_llvm_define_overrides llvmModule defineOvrs llvmctx
     register_llvm_declare_overrides llvmModule declareOvrs llvmctx

-- | Filter the initial list of templates to only those that could
-- possibly match the given declaration based on straightforward,
-- relatively cheap string tests on the name of the declaration.
--
-- Any remaining templates will then examine the declaration in
-- more detail, including examining function arguments
-- and the structure of C++ demangled names to extract more information.
filterTemplates ::
  [OverrideTemplate p sym arch rtp l a] ->
  L.Declare ->
  [OverrideTemplate p sym arch rtp l a]
filterTemplates ts decl = filter (f . overrideTemplateMatcher) ts
 where
 L.Symbol nm = L.decName decl

 f (ExactMatch x)       = x == nm
 f (PrefixMatch pfx)    = pfx `isPrefixOf` nm
 f (SubstringsMatch as) = filterSubstrings as nm

 filterSubstrings [] _ = True
 filterSubstrings (a:as) xs =
   case restAfterSubstring a xs of
     Nothing   -> False
     Just rest -> filterSubstrings as rest

 restAfterSubstring :: String -> String -> Maybe String
 restAfterSubstring sub xs = asum [ stripPrefix sub tl | tl <- tails xs ]


-- | Helper function for registering overrides
register_llvm_overrides_ ::
  LLVMContext arch ->
  [OverrideTemplate p sym arch rtp l a] ->
  [L.Declare] ->
  OverrideSim p sym LLVM rtp l a ()
register_llvm_overrides_ llvmctx acts decls =
    forM_ decls $ \decl ->
      do let acts' = filterTemplates acts decl
         let L.Symbol nm = L.decName decl
         let declnm = either (const Nothing) Just $ ABI.demangleName nm
         runMaybeT (flip runReaderT (decl,declnm,llvmctx) $ asum (map overrideTemplateAction acts'))

register_llvm_define_overrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  [OverrideTemplate p sym arch rtp l a] ->
  LLVMContext arch ->
  OverrideSim p sym LLVM rtp l a ()
register_llvm_define_overrides llvmModule addlOvrs llvmctx =
  let ?lc = llvmctx^.llvmTypeCtx in
  register_llvm_overrides_ llvmctx (addlOvrs ++ define_overrides) $
     (allModuleDeclares llvmModule)

register_llvm_declare_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch
  , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  L.Module ->
  [OverrideTemplate p sym arch rtp l a] ->
  LLVMContext arch ->
  OverrideSim p sym LLVM rtp l a ()
register_llvm_declare_overrides llvmModule addlOvrs llvmctx =
  let ?lc = llvmctx^.llvmTypeCtx
  in register_llvm_overrides_ llvmctx (addlOvrs ++ declare_overrides) $
       L.modDeclares llvmModule


-- | Register overrides for declared-but-not-defined functions
declare_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch
  , ?lc :: TypeContext, ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  [OverrideTemplate p sym arch rtp l a]
declare_overrides =
  [ basic_llvm_override LLVM.llvmLifetimeStartOverride
  , basic_llvm_override LLVM.llvmLifetimeEndOverride
  , basic_llvm_override (LLVM.llvmLifetimeOverrideOverload "start" (knownNat @8))
  , basic_llvm_override (LLVM.llvmLifetimeOverrideOverload "end" (knownNat @8))
  , basic_llvm_override (LLVM.llvmLifetimeOverrideOverload_opaque "start")
  , basic_llvm_override (LLVM.llvmLifetimeOverrideOverload_opaque "end")
  , basic_llvm_override (LLVM.llvmInvariantStartOverride (knownNat @8))
  , basic_llvm_override LLVM.llvmInvariantStartOverride_opaque
  , basic_llvm_override (LLVM.llvmInvariantEndOverride (knownNat @8))
  , basic_llvm_override LLVM.llvmInvariantEndOverride_opaque

  , basic_llvm_override LLVM.llvmAssumeOverride
  , basic_llvm_override LLVM.llvmTrapOverride
  , basic_llvm_override LLVM.llvmUBSanTrapOverride

  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_32
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_32_noalign
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_32_noalign_opaque
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_64
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_64_noalign
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_64_noalign_opaque

  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_32
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_32_noalign
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_32_noalign_opaque
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_64
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_64_noalign
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_64_noalign_opaque

  , basic_llvm_override LLVM.llvmMemsetOverride_8_32
  , basic_llvm_override LLVM.llvmMemsetOverride_8_32_noalign
  , basic_llvm_override LLVM.llvmMemsetOverride_8_32_noalign_opaque
  , basic_llvm_override LLVM.llvmMemsetOverride_8_64
  , basic_llvm_override LLVM.llvmMemsetOverride_8_64_noalign
  , basic_llvm_override LLVM.llvmMemsetOverride_8_64_noalign_opaque

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32_null
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64_null

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32_null_dynamic
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64_null_dynamic

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32_null_dynamic_opaque
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64_null_dynamic_opaque

  , basic_llvm_override LLVM.llvmPrefetchOverride
  , basic_llvm_override LLVM.llvmPrefetchOverride_opaque
  , basic_llvm_override LLVM.llvmPrefetchOverride_preLLVM10

  , basic_llvm_override LLVM.llvmStacksave
  , basic_llvm_override LLVM.llvmStackrestore

  , polymorphic1_llvm_override "llvm.ctlz"
      (\w -> SomeLLVMOverride (LLVM.llvmCtlz w))
  , polymorphic1_llvm_override "llvm.cttz"
      (\w -> SomeLLVMOverride (LLVM.llvmCttz w))
  , polymorphic1_llvm_override "llvm.ctpop"
      (\w -> SomeLLVMOverride (LLVM.llvmCtpop w))
  , polymorphic1_llvm_override "llvm.bitreverse"
      (\w -> SomeLLVMOverride (LLVM.llvmBitreverse w))
  , polymorphic1_llvm_override "llvm.abs"
      (\w -> SomeLLVMOverride (LLVM.llvmAbsOverride w))

  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @2))  -- 16 = 2 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @4))  -- 32 = 4 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @6))  -- 48 = 6 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @8))  -- 64 = 8 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @10)) -- 80 = 10 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @12)) -- 96 = 12 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @14)) -- 112 = 14 * 8
  , basic_llvm_override (LLVM.llvmBSwapOverride (knownNat @16)) -- 128 = 16 * 8

  , polymorphic1_llvm_override "llvm.fshl"
      (\w -> SomeLLVMOverride (LLVM.llvmFshl w))
  , polymorphic1_llvm_override "llvm.fshr"
      (\w -> SomeLLVMOverride (LLVM.llvmFshr w))

  , polymorphic1_llvm_override "llvm.expect"
      (\w -> SomeLLVMOverride (LLVM.llvmExpectOverride w))
  , polymorphic1_llvm_override "llvm.sadd.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmSaddWithOverflow w))
  , polymorphic1_llvm_override "llvm.uadd.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmUaddWithOverflow w))
  , polymorphic1_llvm_override "llvm.ssub.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmSsubWithOverflow w))
  , polymorphic1_llvm_override "llvm.usub.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmUsubWithOverflow w))
  , polymorphic1_llvm_override "llvm.smul.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmSmulWithOverflow w))
  , polymorphic1_llvm_override "llvm.umul.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmUmulWithOverflow w))

  , polymorphic1_llvm_override "llvm.smax"
      (\w -> SomeLLVMOverride (LLVM.llvmSmax w))
  , polymorphic1_llvm_override "llvm.smin"
      (\w -> SomeLLVMOverride (LLVM.llvmSmin w))
  , polymorphic1_llvm_override "llvm.umax"
      (\w -> SomeLLVMOverride (LLVM.llvmUmax w))
  , polymorphic1_llvm_override "llvm.umin"
      (\w -> SomeLLVMOverride (LLVM.llvmUmin w))

  , basic_llvm_override LLVM.llvmCopysignOverride_F32
  , basic_llvm_override LLVM.llvmCopysignOverride_F64
  , basic_llvm_override LLVM.llvmFabsF32
  , basic_llvm_override LLVM.llvmFabsF64

  , basic_llvm_override LLVM.llvmCeilOverride_F32
  , basic_llvm_override LLVM.llvmCeilOverride_F64
  , basic_llvm_override LLVM.llvmFloorOverride_F32
  , basic_llvm_override LLVM.llvmFloorOverride_F64
  , basic_llvm_override LLVM.llvmSqrtOverride_F32
  , basic_llvm_override LLVM.llvmSqrtOverride_F64
  , basic_llvm_override LLVM.llvmSinOverride_F32
  , basic_llvm_override LLVM.llvmSinOverride_F64
  , basic_llvm_override LLVM.llvmCosOverride_F32
  , basic_llvm_override LLVM.llvmCosOverride_F64
  , basic_llvm_override LLVM.llvmPowOverride_F32
  , basic_llvm_override LLVM.llvmPowOverride_F64
  , basic_llvm_override LLVM.llvmExpOverride_F32
  , basic_llvm_override LLVM.llvmExpOverride_F64
  , basic_llvm_override LLVM.llvmLogOverride_F32
  , basic_llvm_override LLVM.llvmLogOverride_F64
  , basic_llvm_override LLVM.llvmExp2Override_F32
  , basic_llvm_override LLVM.llvmExp2Override_F64
  , basic_llvm_override LLVM.llvmLog2Override_F32
  , basic_llvm_override LLVM.llvmLog2Override_F64
  , basic_llvm_override LLVM.llvmLog10Override_F32
  , basic_llvm_override LLVM.llvmLog10Override_F64
  , basic_llvm_override LLVM.llvmFmaOverride_F32
  , basic_llvm_override LLVM.llvmFmaOverride_F64
  , basic_llvm_override LLVM.llvmFmuladdOverride_F32
  , basic_llvm_override LLVM.llvmFmuladdOverride_F64
  , basic_llvm_override LLVM.llvmIsFpclassOverride_F32
  , basic_llvm_override LLVM.llvmIsFpclassOverride_F64

  -- C standard library functions
  , basic_llvm_override Libc.llvmAbortOverride
  , basic_llvm_override Libc.llvmAssertRtnOverride
  , basic_llvm_override Libc.llvmAssertFailOverride
  , basic_llvm_override Libc.llvmMemcpyOverride
  , basic_llvm_override Libc.llvmMemcpyChkOverride
  , basic_llvm_override Libc.llvmMemmoveOverride
  , basic_llvm_override Libc.llvmMemsetOverride
  , basic_llvm_override Libc.llvmMemsetChkOverride
  , basic_llvm_override Libc.llvmMallocOverride
  , basic_llvm_override Libc.llvmCallocOverride
  , basic_llvm_override Libc.llvmFreeOverride
  , basic_llvm_override Libc.llvmReallocOverride
  , basic_llvm_override Libc.llvmStrlenOverride
  , basic_llvm_override Libc.llvmPrintfOverride
  , basic_llvm_override Libc.llvmPrintfChkOverride
  , basic_llvm_override Libc.llvmPutsOverride
  , basic_llvm_override Libc.llvmPutCharOverride
  , basic_llvm_override Libc.llvmExitOverride
  , basic_llvm_override Libc.llvmGetenvOverride
  , basic_llvm_override Libc.llvmHtonlOverride
  , basic_llvm_override Libc.llvmHtonsOverride
  , basic_llvm_override Libc.llvmNtohlOverride
  , basic_llvm_override Libc.llvmNtohsOverride
  , basic_llvm_override Libc.llvmAbsOverride
  , basic_llvm_override Libc.llvmLAbsOverride_32
  , basic_llvm_override Libc.llvmLAbsOverride_64
  , basic_llvm_override Libc.llvmLLAbsOverride

  , basic_llvm_override Libc.llvmCeilOverride
  , basic_llvm_override Libc.llvmCeilfOverride
  , basic_llvm_override Libc.llvmFloorOverride
  , basic_llvm_override Libc.llvmFloorfOverride
  , basic_llvm_override Libc.llvmFmaOverride
  , basic_llvm_override Libc.llvmFmafOverride
  , basic_llvm_override Libc.llvmIsinfOverride
  , basic_llvm_override Libc.llvm__isinfOverride
  , basic_llvm_override Libc.llvm__isinffOverride
  , basic_llvm_override Libc.llvmIsnanOverride
  , basic_llvm_override Libc.llvm__isnanOverride
  , basic_llvm_override Libc.llvm__isnanfOverride
  , basic_llvm_override Libc.llvmSqrtOverride
  , basic_llvm_override Libc.llvmSqrtfOverride
  , basic_llvm_override Libc.llvmSinOverride
  , basic_llvm_override Libc.llvmSinfOverride
  , basic_llvm_override Libc.llvmCosOverride
  , basic_llvm_override Libc.llvmCosfOverride
  , basic_llvm_override Libc.llvmTanOverride
  , basic_llvm_override Libc.llvmTanfOverride
  , basic_llvm_override Libc.llvmAsinOverride
  , basic_llvm_override Libc.llvmAsinfOverride
  , basic_llvm_override Libc.llvmAcosOverride
  , basic_llvm_override Libc.llvmAcosfOverride
  , basic_llvm_override Libc.llvmAtanOverride
  , basic_llvm_override Libc.llvmAtanfOverride
  , basic_llvm_override Libc.llvmSinhOverride
  , basic_llvm_override Libc.llvmSinhfOverride
  , basic_llvm_override Libc.llvmCoshOverride
  , basic_llvm_override Libc.llvmCoshfOverride
  , basic_llvm_override Libc.llvmTanhOverride
  , basic_llvm_override Libc.llvmTanhfOverride
  , basic_llvm_override Libc.llvmAsinhOverride
  , basic_llvm_override Libc.llvmAsinhfOverride
  , basic_llvm_override Libc.llvmAcoshOverride
  , basic_llvm_override Libc.llvmAcoshfOverride
  , basic_llvm_override Libc.llvmAtanhOverride
  , basic_llvm_override Libc.llvmAtanhfOverride
  , basic_llvm_override Libc.llvmHypotOverride
  , basic_llvm_override Libc.llvmHypotfOverride
  , basic_llvm_override Libc.llvmAtan2Override
  , basic_llvm_override Libc.llvmAtan2fOverride
  , basic_llvm_override Libc.llvmPowfOverride
  , basic_llvm_override Libc.llvmPowOverride
  , basic_llvm_override Libc.llvmExpOverride
  , basic_llvm_override Libc.llvmExpfOverride
  , basic_llvm_override Libc.llvmLogOverride
  , basic_llvm_override Libc.llvmLogfOverride
  , basic_llvm_override Libc.llvmExpm1Override
  , basic_llvm_override Libc.llvmExpm1fOverride
  , basic_llvm_override Libc.llvmLog1pOverride
  , basic_llvm_override Libc.llvmLog1pfOverride
  , basic_llvm_override Libc.llvmExp2Override
  , basic_llvm_override Libc.llvmExp2fOverride
  , basic_llvm_override Libc.llvmLog2Override
  , basic_llvm_override Libc.llvmLog2fOverride
  , basic_llvm_override Libc.llvmExp10Override
  , basic_llvm_override Libc.llvmExp10fOverride
  , basic_llvm_override Libc.llvmLog10Override
  , basic_llvm_override Libc.llvmLog10fOverride

  , basic_llvm_override Libc.cxa_atexitOverride
  , basic_llvm_override Libc.posixMemalignOverride

  -- C++ standard library functions
  , Libcxx.register_cpp_override Libcxx.endlOverride

  -- Some architecture-dependent intrinsics
  , basic_llvm_override LLVM.llvmX86_SSE2_storeu_dq
  , basic_llvm_override LLVM.llvmX86_pclmulqdq
  ]


-- | Register those overrides that should apply even when the corresponding
-- function has a definition
define_overrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [OverrideTemplate p sym arch rtp l a]
define_overrides =
  [ Libcxx.register_cpp_override Libcxx.putToOverride12
  , Libcxx.register_cpp_override Libcxx.putToOverride9
  , Libcxx.register_cpp_override Libcxx.endlOverride
  , Libcxx.register_cpp_override Libcxx.sentryOverride
  , Libcxx.register_cpp_override Libcxx.sentryBoolOverride
  ]

{-
Note [Overrides involving (unsigned) long]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Registering overrides for functions with `long` argument or result types is
tricky, as the size of a `long` varies wildly between different operating
systems and architectures. On Linux and macOS, `long` is 32 or 64 bits on
32- or 64-bit architectures, respectively. On Windows, however, `long` is
always 32 bits, regardless of architecture. There is a similar story for the
`unsigned long` type as well.

To ensure that overrides for functions involving `long` are (at least to some
degree) portable, we register each override for `long`-using function twice:
once where `long` is assumed to be 32 bits, and once again where `long` is
assumed to be 64 bits. This is a somewhat heavy-handed solution, but it avoids
the need to predict what size `long` will be on a given target ahead of time.
-}
