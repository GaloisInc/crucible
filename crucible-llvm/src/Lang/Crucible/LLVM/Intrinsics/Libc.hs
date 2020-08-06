-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libc
-- Description      : Override definitions for C standard library functions
-- Copyright        : (c) Galois, Inc 2015-2019
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
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.Libc where

import           Control.Lens ((^.), _1, _2, _3)
import qualified Codec.Binary.UTF8.Generic as UTF8
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Vector as V
import           System.IO

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface
import           What4.ProgramLoc (plSourceLoc)

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.Printf
import           Lang.Crucible.LLVM.QQ( llvmOvr )
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.LLVM.Intrinsics.Common

------------------------------------------------------------------------
-- ** Declarations


llvmMemcpyOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (LLVMPointerType wptr)
llvmMemcpyOverride =
  [llvmOvr| i8* @memcpy( i8*, i8*, size_t ) |]
  (\memOps sym args ->
       do volatile <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat)
          Ctx.uncurryAssignment (callMemcpy sym memOps)
                                (args :> volatile)
          return $ regValue $ args^._1 -- return first argument
    )


llvmMemcpyChkOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> LLVMPointerType wptr
                   ::> BVType wptr
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemcpyChkOverride =
  [llvmOvr| i8* @__memcpy_chk ( i8*, i8*, size_t, size_t ) |]
  (\memOps sym args ->
      do let args' = Empty :> (args^._1) :> (args^._2) :> (args^._3)
         volatile <- liftIO $ RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat)
         Ctx.uncurryAssignment (callMemcpy sym memOps)
                               (args' :> volatile)
         return $ regValue $ args^._1 -- return first argument
    )

llvmMemmoveOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> (LLVMPointerType wptr)
                   ::> (LLVMPointerType wptr)
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemmoveOverride =
  [llvmOvr| i8* @memmove( i8*, i8*, size_t ) |]
  (\memOps sym args ->
      do volatile <- liftIO (RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat))
         Ctx.uncurryAssignment (callMemmove sym memOps)
                               (args :> volatile)
         return $ regValue $ args^._1 -- return first argument
    )

llvmMemsetOverride :: forall p sym arch wptr.
     (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType 32
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetOverride =
  [llvmOvr| i8* @memset( i8*, i32, size_t ) |]
  (\memOps sym args ->
      do LeqProof <- return (leqTrans @9 @16 @wptr LeqProof LeqProof)
         let dest = args^._1
         val <- liftIO (RegEntry knownRepr <$> bvTrunc sym (knownNat @8) (regValue (args^._2)))
         let len = args^._3
         volatile <- liftIO
            (RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat))
         callMemset sym memOps dest val len volatile
         return (regValue dest)
    )

llvmMemsetChkOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                 ::> BVType 32
                 ::> BVType wptr
                 ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetChkOverride =
  [llvmOvr| i8* @__memset_chk( i8*, i32, size_t, size_t ) |]
  (\memOps sym args ->
      do let dest = args^._1
         val <- liftIO
              (RegEntry knownRepr <$> bvTrunc sym knownNat (regValue (args^._2)))
         let len = args^._3
         volatile <- liftIO
            (RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat))
         callMemset sym memOps dest val len volatile
         return (regValue dest)
    )

------------------------------------------------------------------------
-- *** Allocation

llvmCallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => LLVMOverride p sym arch
         (EmptyCtx ::> BVType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmCallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @calloc( size_t, size_t ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callCalloc sym memOps alignment) args)


llvmReallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmReallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @realloc( i8*, size_t ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callRealloc sym memOps alignment) args)

llvmMallocOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => LLVMOverride p sym arch
         (EmptyCtx ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @malloc( size_t ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callMalloc sym memOps alignment) args)

posixMemalignOverride ::
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext) =>
  LLVMOverride p sym arch
      (EmptyCtx ::> LLVMPointerType wptr
                ::> BVType wptr
                ::> BVType wptr)
      (BVType 32)
posixMemalignOverride =
  [llvmOvr| i32 @posix_memalign( i8**, size_t, size_t ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callPosixMemalign sym memOps) args)


llvmFreeOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr)
         UnitType
llvmFreeOverride =
  [llvmOvr| void @free( i8* ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callFree sym memOps) args)

------------------------------------------------------------------------
-- *** Strings and I/O

llvmPrintfOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfOverride =
  [llvmOvr| i32 @printf( i8*, ... ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callPrintf sym memOps) args)

llvmPrintfChkOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
         (EmptyCtx ::> BVType 32
                   ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfChkOverride =
  [llvmOvr| i32 @__printf_chk( i32, i8*, ... ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (\_flg -> callPrintf sym memOps) args)


llvmPutCharOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> BVType 32) (BVType 32)
llvmPutCharOverride =
  [llvmOvr| i32 @putchar( i32 ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callPutChar sym memOps) args)


llvmPutsOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) (BVType 32)
llvmPutsOverride =
  [llvmOvr| i32 @puts( i8* ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callPuts sym memOps) args)

llvmStrlenOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch (EmptyCtx ::> LLVMPointerType wptr) (BVType wptr)
llvmStrlenOverride =
  [llvmOvr| size_t @strlen( i8* ) |]
  (\memOps sym args -> Ctx.uncurryAssignment (callStrlen sym memOps) args)

------------------------------------------------------------------------
-- ** Implementations

------------------------------------------------------------------------
-- *** Allocation

callRealloc
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (LLVMPointerType wptr))
callRealloc sym mvar alignment (regValue -> ptr) (regValue -> sz) =
  do szZero  <- liftIO (notPred sym =<< bvIsNonzero sym sz)
     ptrNull <- liftIO (ptrIsNull sym PtrWidth ptr)
     symbolicBranches emptyRegMap
       -- If the pointer is null, behave like malloc
       [ ( ptrNull
         , modifyGlobal mvar $ \mem -> liftIO $ doMalloc sym G.HeapAlloc G.Mutable "<realloc>" mem sz alignment
         , Nothing
         )

       -- If the size is zero, behave like malloc (of zero bytes) then free
       , (szZero
         , modifyGlobal mvar $ \mem -> liftIO $
              do (newp, mem1) <- doMalloc sym G.HeapAlloc G.Mutable "<realloc>" mem sz alignment
                 mem2 <- doFree sym mem1 ptr
                 return (newp, mem2)
         , Nothing
         )

       -- Otherwise, allocate a new region, memcopy `sz` bytes and free the old pointer
       , (truePred sym
         , modifyGlobal mvar $ \mem -> liftIO $
              do (newp, mem1) <- doMalloc sym G.HeapAlloc G.Mutable "<realloc>" mem sz alignment
                 mem2 <- uncheckedMemcpy sym mem1 newp ptr sz
                 mem3 <- doFree sym mem2 ptr
                 return (newp, mem3)
         , Nothing)
       ]


callPosixMemalign
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr, wptr ~ ArchWidth arch, ?lc :: TypeContext)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPosixMemalign sym mvar (regValue -> outPtr) (regValue -> align) (regValue -> sz) =
  case asBV align of
    Nothing -> fail $ unwords ["posix_memalign: alignment value must be concrete:", show (printSymExpr align)]
    Just concrete_align ->
      case toAlignment (toBytes (BV.asUnsigned concrete_align)) of
        Nothing -> fail $ unwords ["posix_memalign: invalid alignment value:", show concrete_align]
        Just a ->
          let dl = llvmDataLayout ?lc in
          modifyGlobal mvar $ \mem -> liftIO $
             do loc <- plSourceLoc <$> getCurrentProgramLoc sym
                (p, mem') <- doMalloc sym G.HeapAlloc G.Mutable (show loc) mem sz a
                mem'' <- storeRaw sym mem' outPtr (bitvectorType (dl^.ptrSize)) (dl^.ptrAlign) (ptrToPtrVal p)
                z <- bvLit sym knownNat (BV.zero knownNat)
                return (z, mem'')

callMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (LLVMPointerType wptr))
callMalloc sym mvar alignment (regValue -> sz) =
  modifyGlobal mvar $ \mem -> liftIO $
    do loc <- plSourceLoc <$> getCurrentProgramLoc sym
       doMalloc sym G.HeapAlloc G.Mutable (show loc) mem sz alignment

callCalloc
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (LLVMPointerType wptr))
callCalloc sym mvar alignment
           (regValue -> sz)
           (regValue -> num) =
  modifyGlobal mvar $ \mem -> liftIO $
    doCalloc sym mem sz num alignment

callFree
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callFree sym mvar
           (regValue -> ptr) =
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doFree sym mem ptr
       return ((), mem')

------------------------------------------------------------------------
-- *** Memory manipulation

callMemcpy
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callMemcpy sym mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _volatile =
  modifyGlobal mvar $ \mem -> liftIO $
    do assertDisjointRegions sym w dest src len
       mem' <- doMemcpy sym w mem dest src len
       return ((), mem')

-- NB the only difference between memcpy and memove
-- is that memmove does not assert that the memory
-- ranges are disjoint.  The underlying operation
-- works correctly in both cases.
callMemmove
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callMemmove sym mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _volatile =
  -- FIXME? add assertions about alignment
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doMemcpy sym w mem dest src len
       return ((), mem')

callMemset
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 8)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym (LLVM arch) r args ret ()
callMemset sym mvar
           (regValue -> dest)
           (regValue -> val)
           (RegEntry (BVRepr w) len)
           _volatile =
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doMemset sym w mem dest val len
       return ((), mem')

------------------------------------------------------------------------
-- *** Strings and I/O

callPutChar
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (BVType 32)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPutChar _sym _mvar
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (BV.asUnsigned <$> asBV ch)
    liftIO $ hPutChar h chval
    return ch

callPuts
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPuts sym mvar
  (regValue -> strPtr) = do
    mem <- readGlobal mvar
    str <- liftIO $ loadString sym mem strPtr Nothing
    h <- printHandle <$> getContext
    liftIO $ hPutStrLn h (UTF8.toString str)
    -- return non-negative value on success
    liftIO $ bvLit sym knownNat (BV.one knownNat)

callStrlen
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType wptr))
callStrlen sym mvar (regValue -> strPtr) = do
  mem <- readGlobal mvar
  liftIO $ strLen sym mem strPtr

callAssert
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym)
  => GlobalVar Mem
  -> sym
  -> Ctx.Assignment (RegEntry sym)
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
  -> OverrideSim p sym (LLVM arch) r args reg (RegValue sym UnitType)
callAssert mvar sym (Empty :> _pfn :> _pfile :> _pline :> ptxt ) =
     do mem <- readGlobal mvar
        txt <- liftIO $ loadString sym mem (regValue ptxt) Nothing
        let err = AssertFailureSimError "Call to assert()" (UTF8.toString txt)
        liftIO $ addFailedAssertion sym err

callPrintf
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym)
  => sym
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType AnyType)
  -> OverrideSim p sym (LLVM arch) r args ret (RegValue sym (BVType 32))
callPrintf sym mvar
  (regValue -> strPtr)
  (regValue -> valist) = do
    mem <- readGlobal mvar
    formatStr <- liftIO $ loadString sym mem strPtr Nothing
    case parseDirectives formatStr of
      Left err -> overrideError $ AssertFailureSimError "Format string parsing failed" err
      Right ds -> do
        ((str, n), mem') <- liftIO $ runStateT (executeDirectives (printfOps sym valist) ds) mem
        writeGlobal mvar mem'
        h <- printHandle <$> getContext
        liftIO $ hPutStr h str
        liftIO $ bvLit sym knownNat (BV.mkBV knownNat (toInteger n))

printfOps :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
          => sym
          -> V.Vector (AnyValue sym)
          -> PrintfOperations (StateT (MemImpl sym) IO)
printfOps sym valist =
  PrintfOperations
  { printfUnsupported = \x -> lift $ addFailedAssertion sym
                                   $ Unsupported x

  , printfGetInteger = \i sgn _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (LLVMPointerRepr w) x) ->
         do bv <- liftIO (projectLLVM_bv sym x)
            if sgn then
              return $ BV.asSigned w <$> asBV bv
            else
              return $ BV.asUnsigned <$> asBV bv
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Type mismatch in printf"
                (unwords ["Expected integer, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
               "Out-of-bounds argument access in printf"
               (unwords ["Index:", show i])

  , printfGetFloat = \i _len ->
     case valist V.!? (i-1) of
       Just (AnyValue (FloatRepr _fi) _x) ->
         -- TODO: handle interpreted floats
         return Nothing
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected floating-point, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])

  , printfGetString  = \i numchars ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
           do mem <- get
              liftIO $ loadString sym mem ptr numchars
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected char*, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])

  , printfGetPointer = \i ->
     case valist V.!? (i-1) of
       Just (AnyValue PtrRepr ptr) ->
         return $ show (G.ppPtr ptr)
       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected void*, but got:", show tpr])
       Nothing ->
         lift $ addFailedAssertion sym
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
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w8) tp noAlignment x
                 put mem'
              Len_Short -> do
                 let w16 = knownNat :: NatRepr 16
                 let tp = G.bitvectorType 2
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w16 (BV.mkBV w16 (toInteger v)))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w16) tp noAlignment x
                 put mem'
              Len_NoMod -> do
                 let w32  = knownNat :: NatRepr 32
                 let tp = G.bitvectorType 4
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w32 (BV.mkBV w32 (toInteger v)))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w32) tp noAlignment x
                 put mem'
              Len_Long  -> do
                 let w64 = knownNat :: NatRepr 64
                 let tp = G.bitvectorType 8
                 x <- liftIO (llvmPointer_bv sym =<< bvLit sym w64 (BV.mkBV w64 (toInteger v)))
                 mem' <- liftIO $ doStore sym mem ptr (LLVMPointerRepr w64) tp noAlignment x
                 put mem'
              _ ->
                lift $ addFailedAssertion sym
                     $ Unsupported
                     $ unwords ["Unsupported size modifier in %n conversion:", show len]

       Just (AnyValue tpr _) ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Type mismatch in printf."
                (unwords ["Expected void*, but got:", show tpr])

       Nothing ->
         lift $ addFailedAssertion sym
              $ AssertFailureSimError
                "Out-of-bounds argument access in printf:"
                (unwords ["Index:", show i])
  }

------------------------------------------------------------------------
-- *** Other

-- from OSX libc
llvmAssertRtnOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
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
  :: (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
        UnitType
llvmAssertFailOverride =
  [llvmOvr| void @__assert_fail( i8*, i8*, i32, i8* ) |]
  callAssert


llvmAbortOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch EmptyCtx UnitType
llvmAbortOverride =
  [llvmOvr| void @abort() |]
  (\_ sym _args ->
     do let err = AssertFailureSimError "Call to abort" ""
        liftIO $ assert sym (falsePred sym) err
  )

llvmGetenvOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
        (EmptyCtx ::> LLVMPointerType wptr)
        (LLVMPointerType wptr)
llvmGetenvOverride =
  [llvmOvr| i8* @getenv( i8* ) |]
  (\_ sym _args -> liftIO $ mkNullPointer sym PtrWidth)

----------------------------------------------------------------------------
-- atexit stuff

cxa_atexitOverride
  :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
  => LLVMOverride p sym arch
        (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr ::> LLVMPointerType wptr)
        (BVType 32)
cxa_atexitOverride =
  [llvmOvr| i32 @__cxa_atexit( void (i8*)*, i8*, i8* ) |]
  (\_ sym _args -> liftIO $ bvLit sym knownNat (BV.zero knownNat))
