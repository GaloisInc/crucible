-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libc.String
-- Description      : Override definitions for C @string.h@ functions
-- Copyright        : (c) Galois, Inc 2026
-- License          : BSD3
-- Maintainer       : Galois, Inc. <crux@galois.com>
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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.Libc.String
  ( -- * string.h overrides
    string_overrides
    -- * Override declarations
  , llvmMemcpyOverride
  , llvmMemcpyChkOverride
  , llvmMemmoveOverride
  , llvmMemsetOverride
  , llvmMemsetChkOverride
  , llvmStrlenOverride
  , llvmStrnlenOverride
  , llvmStrcpyOverride
  , llvmStrdupOverride
  , llvmStrndupOverride
    -- * Implementation functions
  , callMemcpy
  , callMemmove
  , callMemset
  , callStrlen
  , callStrnlen
  , callStrcpy
  , callStrdup
  , callStrndup
  ) where

import           Control.Lens ((^.), _1, _2, _3)
import           Control.Monad.IO.Class (liftIO)
import qualified Data.BitVector.Sized as BV

import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface
import           What4.ProgramLoc (plSourceLoc)

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

import           Lang.Crucible.LLVM.Intrinsics.Common

-- | All string.h overrides
string_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?memOpts :: MemOptions ) =>
  [SomeLLVMOverride p sym ext]
string_overrides =
  [ SomeLLVMOverride llvmMemcpyOverride
  , SomeLLVMOverride llvmMemcpyChkOverride
  , SomeLLVMOverride llvmMemmoveOverride
  , SomeLLVMOverride llvmMemsetOverride
  , SomeLLVMOverride llvmMemsetChkOverride
  , SomeLLVMOverride llvmStrlenOverride
  , SomeLLVMOverride llvmStrnlenOverride
  , SomeLLVMOverride llvmStrcpyOverride
  , SomeLLVMOverride llvmStrdupOverride
  , SomeLLVMOverride llvmStrndupOverride
  ]

------------------------------------------------------------------------
-- ** Declarations

llvmMemcpyOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (LLVMPointerType wptr)
llvmMemcpyOverride =
  [llvmOvr| i8* @memcpy( i8*, i8*, size_t ) |]
  (\memOps args ->
       do sym <- getSymInterface
          volatile <- liftIO $ RegEntry knownRepr <$> bvZero sym knownNat
          Ctx.uncurryAssignment (callMemcpy memOps)
                                (args :> volatile)
          return $ regValue $ args^._1 -- return first argument
    )


llvmMemcpyChkOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> LLVMPointerType wptr
                   ::> BVType wptr
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemcpyChkOverride =
  [llvmOvr| i8* @__memcpy_chk ( i8*, i8*, size_t, size_t ) |]
  (\memOps args ->
      do let args' = Empty :> (args^._1) :> (args^._2) :> (args^._3)
         sym <- getSymInterface
         volatile <- liftIO $ RegEntry knownRepr <$> bvZero sym knownNat
         Ctx.uncurryAssignment (callMemcpy memOps)
                               (args' :> volatile)
         return $ regValue $ args^._1 -- return first argument
    )

llvmMemmoveOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> (LLVMPointerType wptr)
                   ::> (LLVMPointerType wptr)
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemmoveOverride =
  [llvmOvr| i8* @memmove( i8*, i8*, size_t ) |]
  (\memOps args ->
      do sym <- getSymInterface
         volatile <- liftIO (RegEntry knownRepr <$> bvZero sym knownNat)
         Ctx.uncurryAssignment (callMemmove memOps)
                               (args :> volatile)
         return $ regValue $ args^._1 -- return first argument
    )

llvmMemsetOverride :: forall p sym ext wptr.
     (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType 32
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetOverride =
  [llvmOvr| i8* @memset( i8*, i32, size_t ) |]
  (\memOps args ->
      do sym <- getSymInterface
         LeqProof <- return (leqTrans @9 @16 @wptr LeqProof LeqProof)
         let dest = args^._1
         val <- liftIO (RegEntry knownRepr <$> bvTrunc sym (knownNat @8) (regValue (args^._2)))
         let len = args^._3
         volatile <- liftIO
            (RegEntry knownRepr <$> bvZero sym knownNat)
         callMemset memOps dest val len volatile
         return (regValue dest)
    )

llvmMemsetChkOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                 ::> BVType 32
                 ::> BVType wptr
                 ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetChkOverride =
  [llvmOvr| i8* @__memset_chk( i8*, i32, size_t, size_t ) |]
  (\memOps args ->
      do sym <- getSymInterface
         let dest = args^._1
         val <- liftIO
              (RegEntry knownRepr <$> bvTrunc sym knownNat (regValue (args^._2)))
         let len = args^._3
         volatile <- liftIO
            (RegEntry knownRepr <$> bvZero sym knownNat)
         callMemset memOps dest val len volatile
         return (regValue dest)
    )

llvmStrlenOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr) (BVType wptr)
llvmStrlenOverride =
  [llvmOvr| size_t @strlen( i8* ) |]
  (\memOps args -> Ctx.uncurryAssignment (callStrlen memOps) args)

llvmStrnlenOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType wptr) (BVType wptr)
llvmStrnlenOverride =
  [llvmOvr| size_t @strnlen( i8*, size_t ) |]
  (\memOps args -> Ctx.uncurryAssignment (callStrnlen memOps) args)

llvmStrcpyOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr) (LLVMPointerType wptr)
llvmStrcpyOverride =
  [llvmOvr| i8* @strcpy( i8*, i8* ) |]
  (\memOps args -> Ctx.uncurryAssignment (callStrcpy memOps) args)

llvmStrdupOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr) (LLVMPointerType wptr)
llvmStrdupOverride =
  [llvmOvr| i8* @strdup( i8* ) |]
  (\memOps args -> Ctx.uncurryAssignment (callStrdup memOps) args)

llvmStrndupOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr ::> BVType wptr) (LLVMPointerType wptr)
llvmStrndupOverride =
  [llvmOvr| i8* @strndup( i8*, size_t ) |]
  (\memOps args -> Ctx.uncurryAssignment (callStrndup memOps) args)

------------------------------------------------------------------------
-- ** Implementations

------------------------------------------------------------------------
-- *** Memory manipulation

callMemcpy
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret ()
callMemcpy mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _volatile =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $
      do mem' <- doMemcpy bak w mem True dest src len
         return ((), mem')

-- NB the only difference between memcpy and memove
-- is that memmove does not assert that the memory
-- ranges are disjoint.  The underlying operation
-- works correctly in both cases.
callMemmove
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret ()
callMemmove mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _volatile =
  -- FIXME? add assertions about alignment
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $
      do mem' <- doMemcpy bak w mem False dest src len
         return ((), mem')

callMemset
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 8)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret ()
callMemset mvar
           (regValue -> dest)
           (regValue -> val)
           (RegEntry (BVRepr w) len)
           _volatile =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $
      do mem' <- doMemset bak w mem dest val len
         return ((), mem')

------------------------------------------------------------------------
-- *** Strings

callStrlen
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType wptr))
callStrlen mvar (regValue -> strPtr) =
  ovrWithBackend $ \bak -> do
    mem <- readGlobal mvar
    liftIO $ strLen bak mem strPtr

callStrnlen
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType wptr))
callStrnlen mvar (regValue -> strPtr) (regValue -> bound) =
  ovrWithBackend $ \bak -> do
    mem <- readGlobal mvar
    liftIO $ CStr.strnlen bak mem strPtr bound

callStrcpy
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callStrcpy mvar (regValue -> dst) (regValue -> src) =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> do
      mem' <- liftIO $ CStr.copyConcretelyNullTerminatedString bak mem dst src Nothing
      pure (dst, mem')

callStrdup
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callStrdup mvar (regValue -> src) =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $ do
      let sym = backendGetSym bak
      loc <- plSourceLoc <$> getCurrentProgramLoc sym
      let loc' = "<strdup> " ++ show loc
      CStr.dupConcretelyNullTerminatedString bak mem src Nothing loc' noAlignment

callStrndup
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callStrndup mvar (regValue -> src) (regValue -> bound) =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $ do
      let sym = backendGetSym bak
      loc <- plSourceLoc <$> getCurrentProgramLoc sym
      let loc' = "<strndup> " ++ show loc
      case BV.asUnsigned <$> asBV bound of
        Nothing -> do
          let err = AssertFailureSimError "`strndup` called with symbolic max length" ""
          addFailedAssertion bak err
        Just b ->
          let bound' = Just (fromIntegral b) in
          CStr.dupConcretelyNullTerminatedString bak mem src bound' loc' noAlignment
