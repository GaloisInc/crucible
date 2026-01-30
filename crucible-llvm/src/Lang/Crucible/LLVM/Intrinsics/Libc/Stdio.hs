-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libc.Stdio
-- Description      : Override definitions for C @stdio.h@ functions
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

module Lang.Crucible.LLVM.Intrinsics.Libc.Stdio
  ( -- * stdio.h overrides
    stdio_overrides
    -- * Override declarations
  , llvmPrintfOverride
  , llvmPrintfChkOverride
  , llvmPutsOverride
  , llvmPutCharOverride
    -- * Implementation functions
  , callPrintf
  , callPutChar
  , callPuts
  , printfOps
  ) where

import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.State (StateT(..), get, put)
import           Control.Monad.Trans.Class (MonadTrans(..))
import qualified Codec.Binary.UTF8.Generic as UTF8
import qualified Data.ByteString as BS
import qualified Data.Vector as V
import           System.IO
import qualified GHC.Stack as GHC

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Context (pattern Empty)
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Simulator (printHandle)
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.MemModel.Pointer as Ptr
import           Lang.Crucible.LLVM.MemModel.Strings as CStr
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import           Lang.Crucible.LLVM.Printf
import           Lang.Crucible.LLVM.QQ( llvmOvr )

import           Lang.Crucible.LLVM.Intrinsics.Common

-- | All stdio.h overrides
stdio_overrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?memOpts :: MemOptions ) =>
  [SomeLLVMOverride p sym ext]
stdio_overrides =
  [ SomeLLVMOverride llvmPrintfOverride
  , SomeLLVMOverride llvmPrintfChkOverride
  , SomeLLVMOverride llvmPutsOverride
  , SomeLLVMOverride llvmPutCharOverride
  ]

------------------------------------------------------------------------
-- ** Declarations

llvmPrintfOverride
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfOverride =
  [llvmOvr| i32 @printf( i8*, ... ) |]
  (\memOps args -> Ctx.uncurryAssignment (callPrintf memOps) args)

llvmPrintfChkOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> BVType 32
                   ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfChkOverride =
  [llvmOvr| i32 @__printf_chk( i32, i8*, ... ) |]
  (\memOps args -> Ctx.uncurryAssignment (\_flg -> callPrintf memOps) args)


llvmPutCharOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext (EmptyCtx ::> BVType 32) (BVType 32)
llvmPutCharOverride =
  [llvmOvr| i32 @putchar( i32 ) |]
  (\memOps args -> Ctx.uncurryAssignment (callPutChar memOps) args)


llvmPutsOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym ext (EmptyCtx ::> LLVMPointerType wptr) (BVType 32)
llvmPutsOverride =
  [llvmOvr| i32 @puts( i8* ) |]
  (\memOps args -> Ctx.uncurryAssignment (callPuts memOps) args)

------------------------------------------------------------------------
-- ** Implementations

callPutChar
  :: IsSymInterface sym
  => GlobalVar Mem
  -> RegEntry sym (BVType 32)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPutChar _mvar
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (BV.asUnsigned <$> asBV ch)
    liftIO $ hPutChar h chval
    return ch

callPuts
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPuts mvar
  (regValue -> strPtr) =
    ovrWithBackend $ \bak -> do
      mem <- readGlobal mvar
      str <- liftIO $ CStr.loadString bak mem strPtr Nothing
      h <- printHandle <$> getContext
      liftIO $ hPutStrLn h (UTF8.toString str)
      -- return non-negative value on success
      liftIO $ bvLit (backendGetSym bak) knownNat (BV.one knownNat)

callPrintf
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType AnyType)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPrintf mvar
  (regValue -> strPtr)
  (regValue -> valist) =
    ovrWithBackend $ \bak -> do
      mem <- readGlobal mvar
      formatStr <- liftIO $ CStr.loadString bak mem strPtr Nothing
      case parseDirectives formatStr of
        Left err -> overrideError $ AssertFailureSimError "Format string parsing failed" err
        Right ds -> do
          ((str, n), mem') <- liftIO $ runStateT (executeDirectives (printfOps bak valist) ds) mem
          writeGlobal mvar mem'
          h <- printHandle <$> getContext
          liftIO $ BS.hPutStr h str
          liftIO $ bvLit (backendGetSym bak) knownNat (BV.mkBV knownNat (toInteger n))

printfOps :: ( IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr
             , ?memOpts :: MemOptions )
          => bak
          -> V.Vector (AnyValue sym)
          -> PrintfOperations (StateT (MemImpl sym) IO)
printfOps bak valist =
  let sym = backendGetSym bak in
  PrintfOperations
  { printfUnsupported = \x -> lift $ addFailedAssertion bak
                                   $ Unsupported GHC.callStack x

  , printfGetInteger = \i sgn _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (LLVMPointerRepr w) p@(LLVMPointer _blk bv)) ->
         do isBv <- liftIO (Ptr.ptrIsBv sym p)
            liftIO $ assert bak isBv $
              AssertFailureSimError
               "Passed a pointer to printf where a bitvector was expected"
               ""
            if sgn then
              return $ BV.asSigned w <$> asBV bv
            else
              return $ BV.asUnsigned <$> asBV bv
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Type mismatch in printf"
                (unwords ["Expected integer, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
               "Out-of-bounds argument access in printf"
               (unwords ["Index:", show i])

  , printfGetFloat = \i _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (FloatRepr (_fi :: FloatInfoRepr fi)) x) ->
         do xr <- liftIO (iFloatToReal @_ @fi sym x)
            return (asRational xr)
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected floating-point, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])

  , printfGetString  = \i numchars ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
           do mem <- get
              liftIO $ CStr.loadString bak mem ptr numchars
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected char*, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])

  , printfGetPointer = \i ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         return $ show (G.ppPtr ptr)
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected void*, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])

  , printfSetInteger = \i len v ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         do mem <- get
            case len of
              Len_Byte  -> do
                 let w8 = knownNat :: NatRepr 8
                 let tp = G.bitvectorType 1
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w8 (BV.mkBV w8 (toInteger v)))
                 mem' <- liftIO $ doStore bak mem ptr (LLVMPointerRepr w8) tp noAlignment x
                 put mem'
              Len_Short -> do
                 let w16 = knownNat :: NatRepr 16
                 let tp = G.bitvectorType 2
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w16 (BV.mkBV w16 (toInteger v)))
                 mem' <- liftIO $ doStore bak mem ptr (LLVMPointerRepr w16) tp noAlignment x
                 put mem'
              Len_NoMod -> do
                 let w32  = knownNat :: NatRepr 32
                 let tp = G.bitvectorType 4
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w32 (BV.mkBV w32 (toInteger v)))
                 mem' <- liftIO $ doStore bak mem ptr (LLVMPointerRepr w32) tp noAlignment x
                 put mem'
              Len_Long  -> do
                 let w64 = knownNat :: NatRepr 64
                 let tp = G.bitvectorType 8
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w64 (BV.mkBV w64 (toInteger v)))
                 mem' <- liftIO $ doStore bak mem ptr (LLVMPointerRepr w64) tp noAlignment x
                 put mem'
              _ ->
                lift $ addFailedAssertion bak
                     $ Unsupported GHC.callStack
                     $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected void*, but got:", show tpr])

       Nothing ->
         lift $ addFailedAssertion bak
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])
  }
