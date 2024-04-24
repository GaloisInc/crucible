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
import qualified Text.LLVM.AST as L

import qualified ABI.Itanium as ABI
import qualified Data.Parameterized.Map as MapF

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
import qualified Lang.Crucible.LLVM.Intrinsics.Match as Match
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
filterTemplates ts decl = filter (Match.matches nm . overrideTemplateMatcher) ts
 where L.Symbol nm = L.decName decl

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
  concat
  [ map (\(SomeLLVMOverride ov) -> basic_llvm_override ov) Libc.libc_overrides
  , map (\(SomeLLVMOverride ov) -> basic_llvm_override ov) LLVM.basic_llvm_overrides
  , map (\(pfx, LLVM.Poly1LLVMOverride ov) -> polymorphic1_llvm_override pfx ov) LLVM.poly1_llvm_overrides

  -- C++ standard library functions
  , [ Libcxx.register_cpp_override Libcxx.endlOverride ]
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
