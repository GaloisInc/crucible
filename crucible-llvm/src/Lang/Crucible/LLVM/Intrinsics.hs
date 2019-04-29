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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}


module Lang.Crucible.LLVM.Intrinsics
( LLVM
, llvmIntrinsicTypes
, LLVMHandleInfo(..)
, LLVMContext(..)
, LLVMOverride(..)
, SymbolHandleMap
, symbolMap
, llvmTypeCtx
, mkLLVMContext
, register_llvm_override
, register_llvm_overrides
, build_llvm_override
, llvmDeclToFunHandleRepr
) where

import           Control.Lens hiding (op, (:>), Empty)
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Trans.Maybe
import           Data.Foldable (asum)
import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Map as MapF

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim

import           Lang.Crucible.LLVM.Extension (ArchWidth, LLVM)
import           Lang.Crucible.LLVM.MemModel
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
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a (LLVMContext arch)
register_llvm_overrides llvmModule llvmctx =
  register_llvm_define_overrides llvmModule llvmctx >>=
    register_llvm_declare_overrides llvmModule

-- | Helper function for registering overrides
register_llvm_overrides_ ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMContext arch ->
  [RegOverrideM p sym arch rtp l a ()] ->
  [L.Declare] ->
  OverrideSim p sym (LLVM arch) rtp l a (LLVMContext arch)
register_llvm_overrides_ llvmctx acts decls =
  flip execStateT llvmctx $
    forM_ decls $ \decl ->
      runMaybeT (flip runReaderT decl $ asum acts) >> return ()

register_llvm_define_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a (LLVMContext arch)
register_llvm_define_overrides llvmModule llvmctx =
  let ?lc = llvmctx^.llvmTypeCtx
  in register_llvm_overrides_ llvmctx define_overrides $
       map defToDecl (L.modDefines llvmModule) ++ L.modDeclares llvmModule
  where defToDecl :: L.Define -> L.Declare
        defToDecl def =
          L.Declare { L.decRetType = L.defRetType def
                    , L.decName    = L.defName def
                    , L.decArgs    = map L.typedType (L.defArgs def)
                    , L.decVarArgs = L.defVarArgs def
                    , L.decAttrs   = L.defAttrs def
                    , L.decComdat  = Nothing
                    }

register_llvm_declare_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  L.Module ->
  LLVMContext arch ->
  OverrideSim p sym (LLVM arch) rtp l a (LLVMContext arch)
register_llvm_declare_overrides llvmModule llvmctx =
  let ?lc = llvmctx^.llvmTypeCtx
  in register_llvm_overrides_ llvmctx declare_overrides $
       L.modDeclares llvmModule


-- | Register overrides for declared-but-not-defined functions
declare_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [RegOverrideM p sym arch rtp l a ()]
declare_overrides =
  [ register_llvm_override LLVM.llvmLifetimeStartOverride
  , register_llvm_override LLVM.llvmLifetimeEndOverride
  , register_llvm_override (LLVM.llvmLifetimeOverrideOverload "start" (knownNat @8))
  , register_llvm_override (LLVM.llvmLifetimeOverrideOverload "end" (knownNat @8))
  , register_llvm_override (LLVM.llvmInvariantStartOverride (knownNat @8))
  , register_llvm_override (LLVM.llvmInvariantEndOverride (knownNat @8))
  , register_llvm_override (LLVM.llvmExpectOverride (knownNat @64))
  , register_llvm_override LLVM.llvmAssumeOverride

  , register_llvm_override LLVM.llvmMemcpyOverride_8_8_32
  , register_llvm_override LLVM.llvmMemcpyOverride_8_8_32_noalign
  , register_llvm_override LLVM.llvmMemcpyOverride_8_8_64
  , register_llvm_override LLVM.llvmMemcpyOverride_8_8_64_noalign

  , register_llvm_override LLVM.llvmMemmoveOverride_8_8_32
  , register_llvm_override LLVM.llvmMemmoveOverride_8_8_32_noalign
  , register_llvm_override LLVM.llvmMemmoveOverride_8_8_64
  , register_llvm_override LLVM.llvmMemmoveOverride_8_8_64_noalign

  , register_llvm_override LLVM.llvmMemsetOverride_8_32
  , register_llvm_override LLVM.llvmMemsetOverride_8_32_noalign
  , register_llvm_override LLVM.llvmMemsetOverride_8_64
  , register_llvm_override LLVM.llvmMemsetOverride_8_64_noalign

  , register_llvm_override LLVM.llvmObjectsizeOverride_32
  , register_llvm_override LLVM.llvmObjectsizeOverride_64

  , register_llvm_override LLVM.llvmObjectsizeOverride_32'
  , register_llvm_override LLVM.llvmObjectsizeOverride_64'

  , register_llvm_override LLVM.llvmStacksave
  , register_llvm_override LLVM.llvmStackrestore

  , register_1arg_polymorphic_override "llvm.ctlz"
      (\w -> SomeLLVMOverride (LLVM.llvmCtlz w))
  , register_1arg_polymorphic_override "llvm.cttz"
      (\w -> SomeLLVMOverride (LLVM.llvmCttz w))
  , register_1arg_polymorphic_override "llvm.ctpop"
      (\w -> SomeLLVMOverride (LLVM.llvmCtpop w))
  , register_1arg_polymorphic_override "llvm.bitreverse"
      (\w -> SomeLLVMOverride (LLVM.llvmBitreverse w))

  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @2))  -- 16 = 2 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @4))  -- 32 = 4 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @6))  -- 48 = 6 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @8))  -- 64 = 8 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @10)) -- 80 = 10 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @12)) -- 96 = 12 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @14)) -- 112 = 14 * 8
  , register_llvm_override (LLVM.llvmBSwapOverride (knownNat @16)) -- 128 = 16 * 8

  , register_1arg_polymorphic_override "llvm.sadd.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmSaddWithOverflow w))
  , register_1arg_polymorphic_override "llvm.uadd.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmUaddWithOverflow w))
  , register_1arg_polymorphic_override "llvm.ssub.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmSsubWithOverflow w))
  , register_1arg_polymorphic_override "llvm.usub.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmUsubWithOverflow w))
  , register_1arg_polymorphic_override "llvm.smul.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmSmulWithOverflow w))
  , register_1arg_polymorphic_override "llvm.umul.with.overflow"
      (\w -> SomeLLVMOverride (LLVM.llvmUmulWithOverflow w))

  -- C standard library functions
  , register_llvm_override Libc.llvmAssertRtnOverride
  , register_llvm_override Libc.llvmMemcpyOverride
  , register_llvm_override Libc.llvmMemcpyChkOverride
  , register_llvm_override Libc.llvmMemmoveOverride
  , register_llvm_override Libc.llvmMemsetOverride
  , register_llvm_override Libc.llvmMemsetChkOverride
  , register_llvm_override Libc.llvmMallocOverride
  , register_llvm_override Libc.llvmCallocOverride
  , register_llvm_override Libc.llvmFreeOverride
  , register_llvm_override Libc.llvmReallocOverride
  , register_llvm_override Libc.llvmStrlenOverride
  , register_llvm_override Libc.llvmPrintfOverride
  , register_llvm_override Libc.llvmPrintfChkOverride
  , register_llvm_override Libc.llvmPutsOverride
  , register_llvm_override Libc.llvmPutCharOverride

  -- C++ standard library functions
  , Libcxx.register_cpp_override Libcxx.endlOverride

  -- Some architecture-dependent intrinsics
  , register_llvm_override LLVM.llvmX86_SSE2_storeu_dq
  , register_llvm_override LLVM.llvmX86_pclmulqdq
  ]


-- | Register those overrides that should apply even when the corresponding
-- function has a definition
define_overrides ::
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  [RegOverrideM p sym arch rtp l a ()]
define_overrides =
  [ Libcxx.register_cpp_override Libcxx.putToOverride12
  , Libcxx.register_cpp_override Libcxx.putToOverride9
  , Libcxx.register_cpp_override Libcxx.endlOverride
  , Libcxx.register_cpp_override Libcxx.sentryOverride
  , Libcxx.register_cpp_override Libcxx.sentryBoolOverride
  ]
