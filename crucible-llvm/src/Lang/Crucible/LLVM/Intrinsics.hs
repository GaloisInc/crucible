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
) where

import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.Reader
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

llvmIntrinsicTypes :: IsSymInterface sym => IntrinsicTypes sym
llvmIntrinsicTypes =
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_memory") IntrinsicMuxFn $
   MapF.insert (knownSymbol :: SymbolRepr "LLVM_pointer") IntrinsicMuxFn $
   MapF.empty

-- | Register all declare and define overrides
register_llvm_overrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  [OverrideTemplate p sym arch rtp l a] {- ^ Additional "define" overrides -} ->
  [OverrideTemplate p sym arch rtp l a] {- ^ Additional "declare" overrides -} ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a ()
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
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMContext arch ->
  [OverrideTemplate p sym arch rtp l a] ->
  [L.Declare] ->
  OverrideSim p sym (LLVM arch) rtp l a ()
register_llvm_overrides_ llvmctx acts decls =
    forM_ decls $ \decl ->
      do let acts' = filterTemplates acts decl
         let L.Symbol nm = L.decName decl
         let declnm = either (const Nothing) Just $ ABI.demangleName nm
         runMaybeT (flip runReaderT (decl,declnm,llvmctx) $ asum (map overrideTemplateAction acts'))

register_llvm_define_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  [OverrideTemplate p sym arch rtp l a] ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a ()
register_llvm_define_overrides llvmModule addlOvrs llvmctx =
  let ?lc = llvmctx^.llvmTypeCtx in
  register_llvm_overrides_ llvmctx (addlOvrs ++ define_overrides) $
     (allModuleDeclares llvmModule)

register_llvm_declare_overrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  [OverrideTemplate p sym arch rtp l a] ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a ()
register_llvm_declare_overrides llvmModule addlOvrs llvmctx =
  let ?lc = llvmctx^.llvmTypeCtx
  in register_llvm_overrides_ llvmctx (addlOvrs ++ declare_overrides) $
       L.modDeclares llvmModule


-- | Register overrides for declared-but-not-defined functions
declare_overrides ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [OverrideTemplate p sym arch rtp l a]
declare_overrides =
  [ basic_llvm_override LLVM.llvmLifetimeStartOverride
  , basic_llvm_override LLVM.llvmLifetimeEndOverride
  , basic_llvm_override (LLVM.llvmLifetimeOverrideOverload "start" (knownNat @8))
  , basic_llvm_override (LLVM.llvmLifetimeOverrideOverload "end" (knownNat @8))
  , basic_llvm_override (LLVM.llvmInvariantStartOverride (knownNat @8))
  , basic_llvm_override (LLVM.llvmInvariantEndOverride (knownNat @8))

  , basic_llvm_override LLVM.llvmAssumeOverride
  , basic_llvm_override LLVM.llvmTrapOverride

  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_32
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_32_noalign
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_64
  , basic_llvm_override LLVM.llvmMemcpyOverride_8_8_64_noalign

  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_32
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_32_noalign
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_64
  , basic_llvm_override LLVM.llvmMemmoveOverride_8_8_64_noalign

  , basic_llvm_override LLVM.llvmMemsetOverride_8_32
  , basic_llvm_override LLVM.llvmMemsetOverride_8_32_noalign
  , basic_llvm_override LLVM.llvmMemsetOverride_8_64
  , basic_llvm_override LLVM.llvmMemsetOverride_8_64_noalign

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32_null
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64_null

  , basic_llvm_override LLVM.llvmObjectsizeOverride_32_null_dynamic
  , basic_llvm_override LLVM.llvmObjectsizeOverride_64_null_dynamic

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
  , basic_llvm_override Libc.llvmGetenvOverride

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
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [OverrideTemplate p sym arch rtp l a]
define_overrides =
  [ Libcxx.register_cpp_override Libcxx.putToOverride12
  , Libcxx.register_cpp_override Libcxx.putToOverride9
  , Libcxx.register_cpp_override Libcxx.endlOverride
  , Libcxx.register_cpp_override Libcxx.sentryOverride
  , Libcxx.register_cpp_override Libcxx.sentryBoolOverride
  ]
