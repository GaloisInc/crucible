-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libc
-- Description      : Override definitions for C standard library functions
-- Copyright        : (c) Galois, Inc 2015-2019
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.Libc
  ( module Lang.Crucible.LLVM.Intrinsics.Libc
  , module Lang.Crucible.LLVM.Intrinsics.Libc.Math
  , module Lang.Crucible.LLVM.Intrinsics.Libc.Stdio
  , module Lang.Crucible.LLVM.Intrinsics.Libc.Stdlib
  , module Lang.Crucible.LLVM.Intrinsics.Libc.String
  ) where

import           Control.Lens ((^.))
import qualified Codec.Binary.UTF8.Generic as UTF8
import           Control.Monad (when)
import           Control.Monad.IO.Class (liftIO)

import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.Strings as CStr
import           Lang.Crucible.LLVM.QQ( llvmOvr )
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.LLVM.Intrinsics.Common
import           Lang.Crucible.LLVM.Intrinsics.Libc.Math
import           Lang.Crucible.LLVM.Intrinsics.Libc.Stdio
import           Lang.Crucible.LLVM.Intrinsics.Libc.Stdlib
import           Lang.Crucible.LLVM.Intrinsics.Libc.String
import           Lang.Crucible.LLVM.Intrinsics.Options

-- | All libc overrides.
--
-- This list is useful to other Crucible frontends based on the LLVM memory
-- model (e.g., Macaw).
libc_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?lc :: TypeContext, ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  [SomeLLVMOverride p sym ext]
libc_overrides =
  [ SomeLLVMOverride llvmAssertRtnOverride
  , SomeLLVMOverride llvmAssertFailOverride
  , SomeLLVMOverride llvmHtonlOverride
  , SomeLLVMOverride llvmHtonsOverride
  , SomeLLVMOverride llvmNtohlOverride
  , SomeLLVMOverride llvmNtohsOverride
  ]
  ++ mathOverrides
  ++ stdioOverrides
  ++ stdlibOverrides
  ++ stringOverrides

------------------------------------------------------------------------
-- ** Implementations

callAssert
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> Ctx.Assignment (RegEntry sym)
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
  -> forall r args reg.
     OverrideSim p sym ext r args reg (RegValue sym UnitType)
callAssert mvar (Empty :> _pfn :> _pfile :> _pline :> ptxt ) =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
    when failUponExit $
      do mem <- readGlobal mvar
         txt <- liftIO $ CStr.loadString bak mem (regValue ptxt) Nothing
         let err = AssertFailureSimError "Call to assert()" (UTF8.toString txt)
         liftIO $ addFailedAssertion bak err
    liftIO $
      do loc <- liftIO $ getCurrentProgramLoc sym
         abortExecBecause $ EarlyExit loc
  where
    failUponExit :: Bool
    failUponExit
      = abnormalExitBehavior ?intrinsicsOpts `elem` [AlwaysFail, OnlyAssertFail]


------------------------------------------------------------------------
-- *** Other

-- from OSX libc
llvmAssertRtnOverride
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
        UnitType
llvmAssertRtnOverride =
  [llvmOvr| void @__assert_rtn( i8*, i8*, i32, i8* ) |]
  callAssert

-- From glibc
llvmAssertFailOverride
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
        UnitType
llvmAssertFailOverride =
  [llvmOvr| void @__assert_fail( i8*, i8*, i32, i8* ) |]
  callAssert



llvmHtonlOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmHtonlOverride =
  [llvmOvr| i32 @htonl( i32 ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian (knownNat @4)) args)

llvmHtonsOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 16)
      (BVType 16)
llvmHtonsOverride =
  [llvmOvr| i16 @htons( i16 ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian (knownNat @2)) args)

llvmNtohlOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmNtohlOverride =
  [llvmOvr| i32 @ntohl( i32 ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian (knownNat @4)) args)

llvmNtohsOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 16)
      (BVType 16)
llvmNtohsOverride =
  [llvmOvr| i16 @ntohs( i16 ) |]
  (\_memOps args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian (knownNat @2)) args)


callBSwap ::
  (1 <= width, IsSymInterface sym) =>
  NatRepr width ->
  RegEntry sym (BVType (width * 8)) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType (width * 8)))
callBSwap widthRepr (regValue -> vec) = do
  sym <- getSymInterface
  liftIO $ bvSwap sym widthRepr vec


-- | If the data layout is little-endian, run 'callBSwap' on the input.
-- Otherwise, return the input unchanged. This is the workhorse for the
-- @hton{s,l}@ and @ntoh{s,l}@ overrides.
callBSwapIfLittleEndian ::
  (1 <= width, IsSymInterface sym, ?lc :: TypeContext) =>
  NatRepr width ->
  RegEntry sym (BVType (width * 8)) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType (width * 8)))
callBSwapIfLittleEndian widthRepr vec =
  case (llvmDataLayout ?lc)^.intLayout of
    BigEndian    -> pure (regValue vec)
    LittleEndian -> callBSwap widthRepr vec


----------------------------------------------------------------------------

