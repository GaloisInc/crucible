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
import           Control.Monad (when)
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.State (MonadState(..), StateT(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import qualified Data.ByteString as BS
import qualified Data.Vector as V
import           System.IO
import qualified GHC.Stack as GHC

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Context ( pattern (:>), pattern Empty )
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface
import           What4.InterpretedFloatingPoint (IsInterpretedFloatExprBuilder(..))
import           What4.ProgramLoc (plSourceLoc)
import qualified What4.SpecialFunctions as W4

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.Errors.Poison as Poison
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MalformedLLVMModule
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack)
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Partial
import           Lang.Crucible.LLVM.Printf
import           Lang.Crucible.LLVM.QQ( llvmOvr )
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.LLVM.Intrinsics.Common
import           Lang.Crucible.LLVM.Intrinsics.Options

------------------------------------------------------------------------
-- ** Declarations


llvmMemcpyOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym
           (EmptyCtx ::> LLVMPointerType wptr
                     ::> LLVMPointerType wptr
                     ::> BVType wptr)
           (LLVMPointerType wptr)
llvmMemcpyOverride =
  [llvmOvr| i8* @memcpy( i8*, i8*, size_t ) |]
  (\memOps bak args ->
       do volatile <- liftIO $ RegEntry knownRepr <$> bvLit (backendGetSym bak) knownNat (BV.zero knownNat)
          Ctx.uncurryAssignment (callMemcpy bak memOps)
                                (args :> volatile)
          return $ regValue $ args^._1 -- return first argument
    )


llvmMemcpyChkOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> LLVMPointerType wptr
                   ::> BVType wptr
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemcpyChkOverride =
  [llvmOvr| i8* @__memcpy_chk ( i8*, i8*, size_t, size_t ) |]
  (\memOps bak args ->
      do let args' = Empty :> (args^._1) :> (args^._2) :> (args^._3)
         volatile <- liftIO $ RegEntry knownRepr <$> bvLit (backendGetSym bak) knownNat (BV.zero knownNat)
         Ctx.uncurryAssignment (callMemcpy bak memOps)
                               (args' :> volatile)
         return $ regValue $ args^._1 -- return first argument
    )

llvmMemmoveOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> (LLVMPointerType wptr)
                   ::> (LLVMPointerType wptr)
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemmoveOverride =
  [llvmOvr| i8* @memmove( i8*, i8*, size_t ) |]
  (\memOps bak args ->
      do volatile <- liftIO (RegEntry knownRepr <$> bvLit (backendGetSym bak) knownNat (BV.zero knownNat))
         Ctx.uncurryAssignment (callMemmove bak memOps)
                               (args :> volatile)
         return $ regValue $ args^._1 -- return first argument
    )

llvmMemsetOverride :: forall p sym wptr.
     (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> BVType 32
                   ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetOverride =
  [llvmOvr| i8* @memset( i8*, i32, size_t ) |]
  (\memOps bak args ->
      do let sym = backendGetSym bak
         LeqProof <- return (leqTrans @9 @16 @wptr LeqProof LeqProof)
         let dest = args^._1
         val <- liftIO (RegEntry knownRepr <$> bvTrunc sym (knownNat @8) (regValue (args^._2)))
         let len = args^._3
         volatile <- liftIO
            (RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat))
         callMemset bak memOps dest val len volatile
         return (regValue dest)
    )

llvmMemsetChkOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym
         (EmptyCtx ::> LLVMPointerType wptr
                 ::> BVType 32
                 ::> BVType wptr
                 ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMemsetChkOverride =
  [llvmOvr| i8* @__memset_chk( i8*, i32, size_t, size_t ) |]
  (\memOps bak args ->
      do let sym = backendGetSym bak
         let dest = args^._1
         val <- liftIO
              (RegEntry knownRepr <$> bvTrunc sym knownNat (regValue (args^._2)))
         let len = args^._3
         volatile <- liftIO
            (RegEntry knownRepr <$> bvLit sym knownNat (BV.zero knownNat))
         callMemset bak memOps dest val len volatile
         return (regValue dest)
    )

------------------------------------------------------------------------
-- *** Allocation

llvmCallocOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> BVType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmCallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @calloc( size_t, size_t ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callCalloc bak memOps alignment) args)


llvmReallocOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> LLVMPointerType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmReallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @realloc( i8*, size_t ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callRealloc bak memOps alignment) args)

llvmMallocOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @malloc( size_t ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callMalloc bak memOps alignment) args)

posixMemalignOverride ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?lc :: TypeContext, ?memOpts :: MemOptions ) =>
  LLVMOverride p sym
      (EmptyCtx ::> LLVMPointerType wptr
                ::> BVType wptr
                ::> BVType wptr)
      (BVType 32)
posixMemalignOverride =
  [llvmOvr| i32 @posix_memalign( i8**, size_t, size_t ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callPosixMemalign bak memOps) args)


llvmFreeOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym
         (EmptyCtx ::> LLVMPointerType wptr)
         UnitType
llvmFreeOverride =
  [llvmOvr| void @free( i8* ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callFree bak memOps) args)

------------------------------------------------------------------------
-- *** Strings and I/O

llvmPrintfOverride
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfOverride =
  [llvmOvr| i32 @printf( i8*, ... ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callPrintf bak memOps) args)

llvmPrintfChkOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> BVType 32
                   ::> LLVMPointerType wptr
                   ::> VectorType AnyType)
         (BVType 32)
llvmPrintfChkOverride =
  [llvmOvr| i32 @__printf_chk( i32, i8*, ... ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (\_flg -> callPrintf bak memOps) args)


llvmPutCharOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym (EmptyCtx ::> BVType 32) (BVType 32)
llvmPutCharOverride =
  [llvmOvr| i32 @putchar( i32 ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callPutChar bak memOps) args)


llvmPutsOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType wptr) (BVType 32)
llvmPutsOverride =
  [llvmOvr| i32 @puts( i8* ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callPuts bak memOps) args)

llvmStrlenOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => LLVMOverride p sym (EmptyCtx ::> LLVMPointerType wptr) (BVType wptr)
llvmStrlenOverride =
  [llvmOvr| size_t @strlen( i8* ) |]
  (\memOps bak args -> Ctx.uncurryAssignment (callStrlen bak memOps) args)

------------------------------------------------------------------------
-- ** Implementations

------------------------------------------------------------------------
-- *** Allocation

callRealloc
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callRealloc bak mvar alignment (regValue -> ptr) (regValue -> sz) =
  do let sym = backendGetSym bak
     szZero  <- liftIO (notPred sym =<< bvIsNonzero sym sz)
     ptrNull <- liftIO (ptrIsNull sym PtrWidth ptr)
     loc <- liftIO (plSourceLoc <$> getCurrentProgramLoc sym)
     let displayString = "<realloc> " ++ show loc

     symbolicBranches emptyRegMap
       -- If the pointer is null, behave like malloc
       [ ( ptrNull
         , modifyGlobal mvar $ \mem -> liftIO $ doMalloc bak G.HeapAlloc G.Mutable displayString mem sz alignment
         , Nothing
         )

       -- If the size is zero, behave like malloc (of zero bytes) then free
       , (szZero
         , modifyGlobal mvar $ \mem -> liftIO $
              do (newp, mem1) <- doMalloc bak G.HeapAlloc G.Mutable displayString mem sz alignment
                 mem2 <- doFree bak mem1 ptr
                 return (newp, mem2)
         , Nothing
         )

       -- Otherwise, allocate a new region, memcopy `sz` bytes and free the old pointer
       , (truePred sym
         , modifyGlobal mvar $ \mem -> liftIO $
              do (newp, mem1) <- doMalloc bak G.HeapAlloc G.Mutable displayString mem sz alignment
                 mem2 <- uncheckedMemcpy sym mem1 newp ptr sz
                 mem3 <- doFree bak mem2 ptr
                 return (newp, mem3)
         , Nothing)
       ]


callPosixMemalign
  :: ( IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPosixMemalign bak mvar (regValue -> outPtr) (regValue -> align) (regValue -> sz) =
  let sym = backendGetSym bak in
  case asBV align of
    Nothing -> fail $ unwords ["posix_memalign: alignment value must be concrete:", show (printSymExpr align)]
    Just concrete_align ->
      case toAlignment (toBytes (BV.asUnsigned concrete_align)) of
        Nothing -> fail $ unwords ["posix_memalign: invalid alignment value:", show concrete_align]
        Just a ->
          let dl = llvmDataLayout ?lc in
          modifyGlobal mvar $ \mem -> liftIO $
             do loc <- plSourceLoc <$> getCurrentProgramLoc sym
                let displayString = "<posix_memaign> " ++ show loc
                (p, mem') <- doMalloc bak G.HeapAlloc G.Mutable displayString mem sz a
                mem'' <- storeRaw bak mem' outPtr (bitvectorType (dl^.ptrSize)) (dl^.ptrAlign) (ptrToPtrVal p)
                z <- bvLit sym knownNat (BV.zero knownNat)
                return (z, mem'')

callMalloc
  :: ( IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callMalloc bak mvar alignment (regValue -> sz) =
  modifyGlobal mvar $ \mem -> liftIO $
    do loc <- plSourceLoc <$> getCurrentProgramLoc (backendGetSym bak)
       let displayString = "<malloc> " ++ show loc
       doMalloc bak G.HeapAlloc G.Mutable displayString mem sz alignment

callCalloc
  :: ( IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callCalloc bak mvar alignment
           (regValue -> sz)
           (regValue -> num) =
  modifyGlobal mvar $ \mem -> liftIO $
    doCalloc bak mem sz num alignment

callFree
  :: (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr)
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret ()
callFree bak mvar
           (regValue -> ptr) =
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doFree bak mem ptr
       return ((), mem')

------------------------------------------------------------------------
-- *** Memory manipulation

callMemcpy
  :: ( IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret ()
callMemcpy bak mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _volatile =
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doMemcpy bak w mem True dest src len
       return ((), mem')

-- NB the only difference between memcpy and memove
-- is that memmove does not assert that the memory
-- ranges are disjoint.  The underlying operation
-- works correctly in both cases.
callMemmove
  :: ( IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret ()
callMemmove bak mvar
           (regValue -> dest)
           (regValue -> src)
           (RegEntry (BVRepr w) len)
           _volatile =
  -- FIXME? add assertions about alignment
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doMemcpy bak w mem False dest src len
       return ((), mem')

callMemset
  :: (IsSymBackend sym bak, HasLLVMAnn sym, HasPtrWidth wptr)
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType 8)
  -> RegEntry sym (BVType w)
  -> RegEntry sym (BVType 1)
  -> OverrideSim p sym ext r args ret ()
callMemset bak mvar
           (regValue -> dest)
           (regValue -> val)
           (RegEntry (BVRepr w) len)
           _volatile =
  modifyGlobal mvar $ \mem -> liftIO $
    do mem' <- doMemset bak w mem dest val len
       return ((), mem')

------------------------------------------------------------------------
-- *** Strings and I/O

callPutChar
  :: (IsSymBackend sym bak)
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (BVType 32)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPutChar _bak _mvar
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (BV.asUnsigned <$> asBV ch)
    liftIO $ hPutChar h chval
    return ch

callPuts
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPuts bak mvar
  (regValue -> strPtr) = do
    mem <- readGlobal mvar
    str <- liftIO $ loadString bak mem strPtr Nothing
    h <- printHandle <$> getContext
    liftIO $ hPutStrLn h (UTF8.toString str)
    -- return non-negative value on success
    liftIO $ bvLit (backendGetSym bak) knownNat (BV.one knownNat)

callStrlen
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType wptr))
callStrlen bak mvar (regValue -> strPtr) = do
  mem <- readGlobal mvar
  liftIO $ strLen bak mem strPtr

callAssert
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
     , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions )
  => Bool -- ^ 'True' if this is @__assert_fail()@, 'False' otherwise.
  -> GlobalVar Mem
  -> bak
  -> Ctx.Assignment (RegEntry sym)
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
  -> forall r args reg.
     OverrideSim p sym ext r args reg (RegValue sym UnitType)
callAssert assert_fail mvar bak (Empty :> _pfn :> _pfile :> _pline :> ptxt ) =
  do let sym = backendGetSym bak
     when failUponExit $
       do mem <- readGlobal mvar
          txt <- liftIO $ loadString bak mem (regValue ptxt) Nothing
          let err = AssertFailureSimError "Call to assert()" (UTF8.toString txt)
          liftIO $ addFailedAssertion bak err
     liftIO $
       do loc <- liftIO $ getCurrentProgramLoc sym
          abortExecBecause $ EarlyExit loc
  where
    failUponExit :: Bool
    failUponExit
      | assert_fail
      = abnormalExitBehavior ?intrinsicsOpts `elem` [AlwaysFail, OnlyAssertFail]
      | otherwise
      = abnormalExitBehavior ?intrinsicsOpts == AlwaysFail

callExit :: ( IsSymBackend sym bak
            , ?intrinsicsOpts :: IntrinsicsOptions )
         => bak
         -> RegEntry sym (BVType 32)
         -> OverrideSim p sym ext r args ret (RegValue sym UnitType)
callExit bak ec = liftIO $
  do let sym = backendGetSym bak
     when (abnormalExitBehavior ?intrinsicsOpts == AlwaysFail) $
       do cond <- bvEq sym (regValue ec) =<< bvLit sym knownNat (BV.zero knownNat)
          -- If the argument is non-zero, throw an assertion failure. Otherwise,
          -- simply stop the current thread of execution.
          assert bak cond "Call to exit() with non-zero argument"
     loc <- getCurrentProgramLoc sym
     abortExecBecause $ EarlyExit loc

callPrintf
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (VectorType AnyType)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPrintf bak mvar
  (regValue -> strPtr)
  (regValue -> valist) = do
    mem <- readGlobal mvar
    formatStr <- liftIO $ loadString bak mem strPtr Nothing
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
       Just (AnyValue (LLVMPointerRepr w) x) ->
         do bv <- liftIO (projectLLVM_bv bak x)
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
              liftIO $ loadString bak mem ptr numchars
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

------------------------------------------------------------------------
-- *** Math

llvmCeilOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCeilOverride =
  [llvmOvr| double @ceil( double ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callCeil sym) args)

llvmCeilfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCeilfOverride =
  [llvmOvr| float @ceilf( float ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callCeil sym) args)


llvmFloorOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmFloorOverride =
  [llvmOvr| double @floor( double ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callFloor sym) args)

llvmFloorfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmFloorfOverride =
  [llvmOvr| float @floorf( float ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callFloor sym) args)


-- math.h defines isnan() as a macro, so you might think it unusual to provide
-- a function override for it. However, if you write (isnan)(x) instead of
-- isnan(x), Clang will compile the former as a direct function call rather
-- than as a macro application. Some experimentation reveals that the isnan
-- function's argument is always a double, so we give its argument the type
-- double here to match this unstated convention.
llvmIsnanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvmIsnanOverride =
  [llvmOvr| i32 @isnan( double ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callIsnan sym) args)

-- __isnan and __isnanf are like the isnan macro, except their arguments are
-- known to be double or float, respectively. They are not mentioned in the
-- POSIX source standard, only the binary standard. See
-- http://refspecs.linux-foundation.org/LSB_4.0.0/LSB-Core-generic/LSB-Core-generic/baselib---isnan.html
llvm__isnanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (BVType 32)
llvm__isnanOverride =
  [llvmOvr| i32 @__isnan( double ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callIsnan sym) args)

llvm__isnanfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (BVType 32)
llvm__isnanfOverride =
  [llvmOvr| i32 @__isnanf( float ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callIsnan sym) args)


llvmSqrtOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSqrtOverride =
  [llvmOvr| double @sqrt( double ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callSqrt sym) args)

llvmSqrtfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSqrtfOverride =
  [llvmOvr| float @sqrtf( float ) |]
  (\_memOps sym args -> Ctx.uncurryAssignment (callSqrt sym) args)

callSpecialFunction1 ::
  forall fi p sym bak ext r args ret.
  (IsSymBackend sym bak, KnownRepr FloatInfoRepr fi) =>
  bak ->
  W4.SpecialFunction (EmptyCtx ::> W4.R) ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callSpecialFunction1 bak fn (regValue -> x) = liftIO $
  iFloatSpecialFunction1 (backendGetSym bak) (knownRepr :: FloatInfoRepr fi) fn x

callSpecialFunction2 ::
  forall fi p sym bak ext r args ret.
  (IsSymBackend sym bak, KnownRepr FloatInfoRepr fi) =>
  bak ->
  W4.SpecialFunction (EmptyCtx ::> W4.R ::> W4.R) ->
  RegEntry sym (FloatType fi) ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callSpecialFunction2 bak fn (regValue -> x) (regValue -> y) = liftIO $
  iFloatSpecialFunction2 (backendGetSym bak) (knownRepr :: FloatInfoRepr fi) fn x y

callCeil ::
  forall fi p sym bak ext r args ret.
  (IsSymBackend sym bak) =>
  bak ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callCeil bak (regValue -> x) = liftIO $ iFloatRound @_ @fi (backendGetSym bak) RTP x

callFloor ::
  forall fi p sym bak ext r args ret.
  (IsSymBackend sym bak) =>
  bak ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callFloor bak (regValue -> x) = liftIO $ iFloatRound @_ @fi (backendGetSym bak) RTN x

callIsnan ::
  forall fi p sym bak ext r args ret.
  (IsSymBackend sym bak) =>
  bak ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callIsnan bak (regValue -> x) = liftIO $ do
  let sym = backendGetSym bak
  isnan  <- iFloatIsNaN @_ @fi sym x
  let w = knownNat @32
  bvOne  <- bvLit sym w (BV.one w)
  bvZero <- bvLit sym w (BV.zero w)
  -- isnan() is allowed to return any nonzero value if the argument is NaN, and
  -- out of all the possible nonzero values, `1` is certainly one of them.
  bvIte sym isnan bvOne bvZero

callSqrt ::
  forall fi p sym bak ext r args ret.
  (IsSymBackend sym bak) =>
  bak ->
  RegEntry sym (FloatType fi) ->
  OverrideSim p sym ext r args ret (RegValue sym (FloatType fi))
callSqrt bak (regValue -> x) = liftIO $ iFloatSqrt @_ @fi (backendGetSym bak) RNE x

------------------------------------------------------------------------
-- **** Circular trigonometry functions

-- sin(f)

llvmSinOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSinOverride =
  [llvmOvr| double @sin( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Sin) args)

llvmSinfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSinfOverride =
  [llvmOvr| float @sinf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Sin) args)

-- cos(f)

llvmCosOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCosOverride =
  [llvmOvr| double @cos( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Cos) args)

llvmCosfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCosfOverride =
  [llvmOvr| float @cosf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Cos) args)

-- tan(f)

llvmTanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmTanOverride =
  [llvmOvr| double @tan( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Tan) args)

llvmTanfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmTanfOverride =
  [llvmOvr| float @tanf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Tan) args)

-- asin(f)

llvmAsinOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAsinOverride =
  [llvmOvr| double @asin( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arcsin) args)

llvmAsinfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAsinfOverride =
  [llvmOvr| float @asinf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arcsin) args)

-- acos(f)

llvmAcosOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAcosOverride =
  [llvmOvr| double @acos( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arccos) args)

llvmAcosfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAcosfOverride =
  [llvmOvr| float @acosf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arccos) args)

-- atan(f)

llvmAtanOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAtanOverride =
  [llvmOvr| double @atan( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arctan) args)

llvmAtanfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAtanfOverride =
  [llvmOvr| float @atanf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arctan) args)

------------------------------------------------------------------------
-- **** Hyperbolic trigonometry functions

-- sinh(f)

llvmSinhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmSinhOverride =
  [llvmOvr| double @sinh( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Sinh) args)

llvmSinhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmSinhfOverride =
  [llvmOvr| float @sinhf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Sinh) args)

-- cosh(f)

llvmCoshOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmCoshOverride =
  [llvmOvr| double @cosh( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Cosh) args)

llvmCoshfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmCoshfOverride =
  [llvmOvr| float @coshf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Cosh) args)

-- tanh(f)

llvmTanhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmTanhOverride =
  [llvmOvr| double @tanh( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Tanh) args)

llvmTanhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmTanhfOverride =
  [llvmOvr| float @tanhf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Tanh) args)

-- asinh(f)

llvmAsinhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAsinhOverride =
  [llvmOvr| double @asinh( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arcsinh) args)

llvmAsinhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAsinhfOverride =
  [llvmOvr| float @asinhf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arcsinh) args)

-- acosh(f)

llvmAcoshOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAcoshOverride =
  [llvmOvr| double @acosh( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arccosh) args)

llvmAcoshfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAcoshfOverride =
  [llvmOvr| float @acoshf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arccosh) args)

-- atanh(f)

llvmAtanhOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAtanhOverride =
  [llvmOvr| double @atanh( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arctanh) args)

llvmAtanhfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAtanhfOverride =
  [llvmOvr| float @atanhf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Arctanh) args)

------------------------------------------------------------------------
-- **** Rectangular to polar coordinate conversion

-- hypot(f)

llvmHypotOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmHypotOverride =
  [llvmOvr| double @hypot( double, double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction2 bak W4.Hypot) args)

llvmHypotfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmHypotfOverride =
  [llvmOvr| float @hypotf( float, float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction2 bak W4.Hypot) args)

-- atan2(f)

llvmAtan2Override ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmAtan2Override =
  [llvmOvr| double @atan2( double, double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction2 bak W4.Arctan2) args)

llvmAtan2fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmAtan2fOverride =
  [llvmOvr| float @atan2f( float, float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction2 bak W4.Arctan2) args)

------------------------------------------------------------------------
-- **** Exponential and logarithm functions

-- pow(f)

llvmPowfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmPowfOverride =
  [llvmOvr| float @powf( float, float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction2 bak W4.Pow) args)

llvmPowOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmPowOverride =
  [llvmOvr| double @pow( double, double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction2 bak W4.Pow) args)

-- exp(f)

llvmExpOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExpOverride =
  [llvmOvr| double @exp( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Exp) args)

llvmExpfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExpfOverride =
  [llvmOvr| float @expf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Exp) args)

-- log(f)

llvmLogOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLogOverride =
  [llvmOvr| double @log( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log) args)

llvmLogfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLogfOverride =
  [llvmOvr| float @logf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log) args)

-- expm1(f)

llvmExpm1Override ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExpm1Override =
  [llvmOvr| double @expm1( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Expm1) args)

llvmExpm1fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExpm1fOverride =
  [llvmOvr| float @expm1f( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Expm1) args)

-- log1p(f)

llvmLog1pOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog1pOverride =
  [llvmOvr| double @log1p( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log1p) args)

llvmLog1pfOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog1pfOverride =
  [llvmOvr| float @log1pf( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log1p) args)

------------------------------------------------------------------------
-- **** Base 2 exponential and logarithm

-- exp2(f)

llvmExp2Override ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExp2Override =
  [llvmOvr| double @exp2( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Exp2) args)

llvmExp2fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExp2fOverride =
  [llvmOvr| float @exp2f( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Exp2) args)

-- log2(f)

llvmLog2Override ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog2Override =
  [llvmOvr| double @log2( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log2) args)

llvmLog2fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog2fOverride =
  [llvmOvr| float @log2f( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log2) args)

------------------------------------------------------------------------
-- **** Base 10 exponential and logarithm

-- exp10(f)

llvmExp10Override ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmExp10Override =
  [llvmOvr| double @exp10( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Exp10) args)

llvmExp10fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmExp10fOverride =
  [llvmOvr| float @exp10f( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Exp10) args)

-- log10(f)

llvmLog10Override ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType DoubleFloat)
     (FloatType DoubleFloat)
llvmLog10Override =
  [llvmOvr| double @log10( double ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log10) args)

llvmLog10fOverride ::
  IsSymInterface sym =>
  LLVMOverride p sym
     (EmptyCtx ::> FloatType SingleFloat)
     (FloatType SingleFloat)
llvmLog10fOverride =
  [llvmOvr| float @log10f( float ) |]
  (\_memOps bak args -> Ctx.uncurryAssignment (callSpecialFunction1 bak W4.Log10) args)

------------------------------------------------------------------------
-- *** Other

-- from OSX libc
llvmAssertRtnOverride
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions )
  => LLVMOverride p sym
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
        UnitType
llvmAssertRtnOverride =
  [llvmOvr| void @__assert_rtn( i8*, i8*, i32, i8* ) |]
  (callAssert False)

-- From glibc
llvmAssertFailOverride
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions )
  => LLVMOverride p sym
        (EmptyCtx ::> LLVMPointerType wptr
                  ::> LLVMPointerType wptr
                  ::> BVType 32
                  ::> LLVMPointerType wptr)
        UnitType
llvmAssertFailOverride =
  [llvmOvr| void @__assert_fail( i8*, i8*, i32, i8* ) |]
  (callAssert True)


llvmAbortOverride
  :: ( IsSymInterface sym
     , ?intrinsicsOpts :: IntrinsicsOptions )
  => LLVMOverride p sym EmptyCtx UnitType
llvmAbortOverride =
  [llvmOvr| void @abort() |]
  (\_ bak _args -> liftIO $
     do let sym = backendGetSym bak
        when (abnormalExitBehavior ?intrinsicsOpts == AlwaysFail) $
            let err = AssertFailureSimError "Call to abort" "" in
            assert bak (falsePred sym) err
        loc <- getCurrentProgramLoc sym
        abortExecBecause $ EarlyExit loc
  )

llvmExitOverride
  :: forall sym p
   . ( IsSymInterface sym
     , ?intrinsicsOpts :: IntrinsicsOptions )
  => LLVMOverride p sym
         (EmptyCtx ::> BVType 32)
         UnitType
llvmExitOverride =
  [llvmOvr| void @exit( i32 ) |]
  (\_ bak args -> Ctx.uncurryAssignment (callExit bak) args)

llvmGetenvOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym
        (EmptyCtx ::> LLVMPointerType wptr)
        (LLVMPointerType wptr)
llvmGetenvOverride =
  [llvmOvr| i8* @getenv( i8* ) |]
  (\_ bak _args -> liftIO $ mkNullPointer (backendGetSym bak) PtrWidth)

llvmHtonlOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmHtonlOverride =
  [llvmOvr| i32 @htonl( i32 ) |]
  (\_ bak args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian bak (knownNat @4)) args)

llvmHtonsOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 16)
      (BVType 16)
llvmHtonsOverride =
  [llvmOvr| i16 @htons( i16 ) |]
  (\_ bak args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian bak (knownNat @2)) args)

llvmNtohlOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmNtohlOverride =
  [llvmOvr| i32 @ntohl( i32 ) |]
  (\_ bak args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian bak (knownNat @4)) args)

llvmNtohsOverride ::
  (IsSymInterface sym, ?lc :: TypeContext) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 16)
      (BVType 16)
llvmNtohsOverride =
  [llvmOvr| i16 @ntohs( i16 ) |]
  (\_ bak args -> Ctx.uncurryAssignment (callBSwapIfLittleEndian bak (knownNat @2)) args)

llvmAbsOverride ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmAbsOverride =
  [llvmOvr| i32 @abs( i32 ) |]
  (\mvar bak args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs bak callStack (knownNat @32)) args)

-- @labs@ uses `long` as its argument and result type, so we need two overrides
-- for @labs@. See Note [Overrides involving (unsigned) long] in
-- Lang.Crucible.LLVM.Intrinsics.
llvmLAbsOverride_32 ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmLAbsOverride_32 =
  [llvmOvr| i32 @labs( i32 ) |]
  (\mvar bak args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs bak callStack (knownNat @32)) args)

llvmLAbsOverride_64 ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 64)
      (BVType 64)
llvmLAbsOverride_64 =
  [llvmOvr| i64 @labs( i64 ) |]
  (\mvar bak args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs bak callStack (knownNat @64)) args)

llvmLLAbsOverride ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym
      (EmptyCtx ::> BVType 64)
      (BVType 64)
llvmLLAbsOverride =
  [llvmOvr| i64 @llabs( i64 ) |]
  (\mvar bak args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs bak callStack (knownNat @64)) args)

callBSwap ::
  (1 <= width, IsSymBackend sym bak) =>
  bak ->
  NatRepr width ->
  RegEntry sym (BVType (width * 8)) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType (width * 8)))
callBSwap bak widthRepr (regValue -> vec) =
  liftIO $ bvSwap (backendGetSym bak) widthRepr vec

-- | This determines under what circumstances @callAbs@ should check if its
-- argument is equal to the smallest signed integer of a particular size
-- (e.g., @INT_MIN@), and if it is equal to that value, what kind of error
-- should be reported.
data CheckAbsIntMin
  = LibcAbsIntMinUB
    -- ^ For the @abs@, @labs@, and @llabs@ functions, always check if the
    --   argument is equal to @INT_MIN@. If so, report it as undefined
    --   behavior per the C standard.
  | LLVMAbsIntMinPoison Bool
    -- ^ For the @llvm.abs.*@ family of LLVM intrinsics, check if the argument
    --   is equal to @INT_MIN@ only when the 'Bool' argument is 'True'. If it
    --   is 'True' and the argument is equal to @INT_MIN@, return poison.

-- | The workhorse for the @abs@, @labs@, and @llabs@ functions, as well as the
-- @llvm.abs.*@ family of overloaded intrinsics.
callAbs ::
  forall w p sym bak ext r args ret.
  (1 <= w, IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  CallStack ->
  CheckAbsIntMin ->
  NatRepr w ->
  RegEntry sym (BVType w) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callAbs bak callStack checkIntMin widthRepr (regValue -> src) = liftIO $ do
  let sym = backendGetSym bak
  bvIntMin    <- bvLit sym widthRepr (BV.minSigned widthRepr)
  isNotIntMin <- notPred sym =<< bvEq sym src bvIntMin

  when shouldCheckIntMin $ do
    isNotIntMinUB <- annotateUB sym callStack ub isNotIntMin
    let err = AssertFailureSimError "Undefined behavior encountered" $
              show $ UB.explain ub
    assert bak isNotIntMinUB err

  isSrcNegative <- bvIsNeg sym src
  srcNegated    <- bvNeg sym src
  bvIte sym isSrcNegative srcNegated src
  where
    shouldCheckIntMin :: Bool
    shouldCheckIntMin =
      case checkIntMin of
        LibcAbsIntMinUB                 -> True
        LLVMAbsIntMinPoison shouldCheck -> shouldCheck

    ub :: UB.UndefinedBehavior (RegValue' sym)
    ub = case checkIntMin of
           LibcAbsIntMinUB ->
             UB.AbsIntMin $ RV src
           LLVMAbsIntMinPoison{} ->
             UB.PoisonValueCreated $ Poison.LLVMAbsIntMin $ RV src

callLibcAbs ::
  (1 <= w, IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  CallStack ->
  NatRepr w ->
  RegEntry sym (BVType w) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callLibcAbs bak callStack = callAbs bak callStack LibcAbsIntMinUB

callLLVMAbs ::
  (1 <= w, IsSymBackend sym bak, HasLLVMAnn sym) =>
  bak ->
  CallStack ->
  NatRepr w ->
  RegEntry sym (BVType w) ->
  RegEntry sym (BVType 1) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callLLVMAbs bak callStack widthRepr src (regValue -> isIntMinPoison) = do
  shouldCheckIntMin <- liftIO $
    -- Per https://releases.llvm.org/12.0.0/docs/LangRef.html#id451, the second
    -- argument must be a constant.
    case asBV isIntMinPoison of
      Just bv -> pure (bv /= BV.zero (knownNat @1))
      Nothing -> malformedLLVMModule
                   "Call to llvm.abs.* with non-constant second argument"
                   [printSymExpr isIntMinPoison]
  callAbs bak callStack (LLVMAbsIntMinPoison shouldCheckIntMin) widthRepr src

-- | If the data layout is little-endian, run 'callBSwap' on the input.
-- Otherwise, return the input unchanged. This is the workhorse for the
-- @hton{s,l}@ and @ntoh{s,l}@ overrides.
callBSwapIfLittleEndian ::
  (1 <= width, IsSymBackend sym bak, ?lc :: TypeContext) =>
  bak ->
  NatRepr width ->
  RegEntry sym (BVType (width * 8)) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType (width * 8)))
callBSwapIfLittleEndian bak widthRepr vec =
  case (llvmDataLayout ?lc)^.intLayout of
    BigEndian    -> pure (regValue vec)
    LittleEndian -> callBSwap bak widthRepr vec

----------------------------------------------------------------------------
-- atexit stuff

cxa_atexitOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym
        (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr ::> LLVMPointerType wptr)
        (BVType 32)
cxa_atexitOverride =
  [llvmOvr| i32 @__cxa_atexit( void (i8*)*, i8*, i8* ) |]
  (\_ bak _args -> liftIO $ bvLit (backendGetSym bak) knownNat (BV.zero knownNat))
