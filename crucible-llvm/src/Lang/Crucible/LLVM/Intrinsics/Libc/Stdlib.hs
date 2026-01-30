-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Libc.Stdlib
-- Description      : Override definitions for C @stdlib.h@ functions
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

module Lang.Crucible.LLVM.Intrinsics.Libc.Stdlib
  ( -- * stdlib.h overrides
    stdlibOverrides
    -- * Override declarations
  , llvmMallocOverride
  , llvmCallocOverride
  , llvmFreeOverride
  , llvmReallocOverride
  , posixMemalignOverride
  , llvmAbortOverride
  , llvmExitOverride
  , llvmGetenvOverride
  , llvmAbsOverride
  , llvmLAbsOverride_32
  , llvmLAbsOverride_64
  , llvmLLAbsOverride
  , cxa_atexitOverride
    -- * Implementation functions
  , callMalloc
  , callCalloc
  , callFree
  , callRealloc
  , callPosixMemalign
  , callExit
  , callLibcAbs
  , callLLVMAbs
  , callAbs
  , CheckAbsIntMin(..)
  ) where

import           Control.Lens ((^.))
import           Control.Monad (when)
import           Control.Monad.IO.Class (liftIO)

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.Context as Ctx

import           What4.Interface
import           What4.ProgramLoc (plSourceLoc)

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.Bytes (toBytes)
import           Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.Errors.Poison as Poison
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MalformedLLVMModule
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack)
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Partial (annotateUB)
import           Lang.Crucible.LLVM.QQ( llvmOvr )
import           Lang.Crucible.LLVM.TypeContext

import           Lang.Crucible.LLVM.Intrinsics.Common
import           Lang.Crucible.LLVM.Intrinsics.Options

-- | All stdlib.h overrides
stdlibOverrides ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?lc :: TypeContext, ?intrinsicsOpts :: IntrinsicsOptions, ?memOpts :: MemOptions ) =>
  [SomeLLVMOverride p sym ext]
stdlibOverrides =
  [ SomeLLVMOverride llvmMallocOverride
  , SomeLLVMOverride llvmCallocOverride
  , SomeLLVMOverride llvmFreeOverride
  , SomeLLVMOverride llvmReallocOverride
  , SomeLLVMOverride posixMemalignOverride
  , SomeLLVMOverride llvmAbortOverride
  , SomeLLVMOverride llvmExitOverride
  , SomeLLVMOverride llvmGetenvOverride
  , SomeLLVMOverride llvmAbsOverride
  , SomeLLVMOverride llvmLAbsOverride_32
  , SomeLLVMOverride llvmLAbsOverride_64
  , SomeLLVMOverride llvmLLAbsOverride
  , SomeLLVMOverride cxa_atexitOverride
  ]

------------------------------------------------------------------------
-- ** Declarations

------------------------------------------------------------------------
-- *** Allocation

llvmCallocOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> BVType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmCallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @calloc( size_t, size_t ) |]
  (\memOps args -> Ctx.uncurryAssignment (callCalloc memOps alignment) args)


llvmReallocOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr ::> BVType wptr)
         (LLVMPointerType wptr)
llvmReallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @realloc( i8*, size_t ) |]
  (\memOps args -> Ctx.uncurryAssignment (callRealloc memOps alignment) args)

llvmMallocOverride
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> BVType wptr)
         (LLVMPointerType wptr)
llvmMallocOverride =
  let alignment = maxAlignment (llvmDataLayout ?lc) in
  [llvmOvr| i8* @malloc( size_t ) |]
  (\memOps args -> Ctx.uncurryAssignment (callMalloc memOps alignment) args)

posixMemalignOverride ::
  ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
  , ?lc :: TypeContext, ?memOpts :: MemOptions ) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> LLVMPointerType wptr
                ::> BVType wptr
                ::> BVType wptr)
      (BVType 32)
posixMemalignOverride =
  [llvmOvr| i32 @posix_memalign( i8**, size_t, size_t ) |]
  (\memOps args -> Ctx.uncurryAssignment (callPosixMemalign memOps) args)


llvmFreeOverride
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
         (EmptyCtx ::> LLVMPointerType wptr)
         UnitType
llvmFreeOverride =
  [llvmOvr| void @free( i8* ) |]
  (\memOps args -> Ctx.uncurryAssignment (callFree memOps) args)

------------------------------------------------------------------------
-- *** Process control

llvmAbortOverride
  :: ( IsSymInterface sym
     , ?intrinsicsOpts :: IntrinsicsOptions )
  => LLVMOverride p sym ext EmptyCtx UnitType
llvmAbortOverride =
  [llvmOvr| void @abort() |]
  (\_ _args ->
     ovrWithBackend $ \bak -> liftIO $ do
       let sym = backendGetSym bak
       when (abnormalExitBehavior ?intrinsicsOpts == AlwaysFail) $
           let err = AssertFailureSimError "Call to abort" "" in
           assert bak (falsePred sym) err
       loc <- getCurrentProgramLoc sym
       abortExecBecause $ EarlyExit loc
  )

llvmExitOverride
  :: forall sym p ext
   . ( IsSymInterface sym
     , ?intrinsicsOpts :: IntrinsicsOptions )
  => LLVMOverride p sym ext
         (EmptyCtx ::> BVType 32)
         UnitType
llvmExitOverride =
  [llvmOvr| void @exit( i32 ) |]
  (\_ args -> Ctx.uncurryAssignment callExit args)

llvmGetenvOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
        (EmptyCtx ::> LLVMPointerType wptr)
        (LLVMPointerType wptr)
llvmGetenvOverride =
  [llvmOvr| i8* @getenv( i8* ) |]
  (\_ _args -> do
    sym <- getSymInterface
    liftIO $ mkNullPointer sym PtrWidth)

------------------------------------------------------------------------
-- *** Integer functions

llvmAbsOverride ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmAbsOverride =
  [llvmOvr| i32 @abs( i32 ) |]
  (\mvar args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs callStack (knownNat @32)) args)

-- @labs@ uses `long` as its argument and result type, so we need two overrides
-- for @labs@. See Note [Overrides involving (unsigned) long] in
-- Lang.Crucible.LLVM.Intrinsics.
llvmLAbsOverride_32 ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 32)
      (BVType 32)
llvmLAbsOverride_32 =
  [llvmOvr| i32 @labs( i32 ) |]
  (\mvar args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs callStack (knownNat @32)) args)

llvmLAbsOverride_64 ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 64)
      (BVType 64)
llvmLAbsOverride_64 =
  [llvmOvr| i64 @labs( i64 ) |]
  (\mvar args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs callStack (knownNat @64)) args)

llvmLLAbsOverride ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  LLVMOverride p sym ext
      (EmptyCtx ::> BVType 64)
      (BVType 64)
llvmLLAbsOverride =
  [llvmOvr| i64 @llabs( i64 ) |]
  (\mvar args ->
     do callStack <- callStackFromMemVar' mvar
        Ctx.uncurryAssignment (callLibcAbs callStack (knownNat @64)) args)

------------------------------------------------------------------------
-- *** atexit

cxa_atexitOverride
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => LLVMOverride p sym ext
        (EmptyCtx ::> LLVMPointerType wptr ::> LLVMPointerType wptr ::> LLVMPointerType wptr)
        (BVType 32)
cxa_atexitOverride =
  [llvmOvr| i32 @__cxa_atexit( void (i8*)*, i8*, i8* ) |]
  (\_ _args -> do
    sym <- getSymInterface
    liftIO $ bvZero sym knownNat)

------------------------------------------------------------------------
-- ** Implementations

------------------------------------------------------------------------
-- *** Allocation

callRealloc
  :: ( IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> Alignment
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callRealloc mvar alignment (regValue -> ptr) (regValue -> sz) =
  ovrWithBackend $ \bak -> do
    let sym = backendGetSym bak
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
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?lc :: TypeContext, ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (BVType 32))
callPosixMemalign mvar (regValue -> outPtr) (regValue -> align) (regValue -> sz) =
  ovrWithBackend $ \bak ->
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
                  z <- bvZero sym knownNat
                  return (z, mem'')

callMalloc
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callMalloc mvar alignment (regValue -> sz) =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $
      do loc <- plSourceLoc <$> getCurrentProgramLoc (backendGetSym bak)
         let displayString = "<malloc> " ++ show loc
         doMalloc bak G.HeapAlloc G.Mutable displayString mem sz alignment

callCalloc
  :: ( IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr
     , ?memOpts :: MemOptions )
  => GlobalVar Mem
  -> Alignment
  -> RegEntry sym (BVType wptr)
  -> RegEntry sym (BVType wptr)
  -> OverrideSim p sym ext r args ret (RegValue sym (LLVMPointerType wptr))
callCalloc mvar alignment
           (regValue -> sz)
           (regValue -> num) =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $
      doCalloc bak mem sz num alignment

callFree
  :: (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr)
  => GlobalVar Mem
  -> RegEntry sym (LLVMPointerType wptr)
  -> OverrideSim p sym ext r args ret ()
callFree mvar
           (regValue -> ptr) =
  ovrWithBackend $ \bak ->
    modifyGlobal mvar $ \mem -> liftIO $
      do mem' <- doFree bak mem ptr
         return ((), mem')

------------------------------------------------------------------------
-- *** Process control

callExit :: ( IsSymInterface sym
            , ?intrinsicsOpts :: IntrinsicsOptions )
         => RegEntry sym (BVType 32)
         -> OverrideSim p sym ext r args ret (RegValue sym UnitType)
callExit ec =
  ovrWithBackend $ \bak -> liftIO $ do
    let sym = backendGetSym bak
    when (abnormalExitBehavior ?intrinsicsOpts == AlwaysFail) $
      do cond <- bvEq sym (regValue ec) =<< bvZero sym knownNat
         -- If the argument is non-zero, throw an assertion failure. Otherwise,
         -- simply stop the current thread of execution.
         assert bak cond "Call to exit() with non-zero argument"
    loc <- getCurrentProgramLoc sym
    abortExecBecause $ EarlyExit loc

------------------------------------------------------------------------
-- *** Integer functions

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
  forall w p sym ext r args ret.
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  CallStack ->
  CheckAbsIntMin ->
  NatRepr w ->
  RegEntry sym (BVType w) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callAbs callStack checkIntMin widthRepr (regValue -> src) = do
  sym <- getSymInterface
  ovrWithBackend $ \bak -> liftIO $ do
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
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  CallStack ->
  NatRepr w ->
  RegEntry sym (BVType w) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callLibcAbs callStack = callAbs callStack LibcAbsIntMinUB

callLLVMAbs ::
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  CallStack ->
  NatRepr w ->
  RegEntry sym (BVType w) ->
  RegEntry sym (BVType 1) ->
  OverrideSim p sym ext r args ret (RegValue sym (BVType w))
callLLVMAbs callStack widthRepr src (regValue -> isIntMinPoison) = do
  shouldCheckIntMin <- liftIO $
    -- Per https://releases.llvm.org/12.0.0/docs/LangRef.html#id451, the second
    -- argument must be a constant.
    case asBV isIntMinPoison of
      Just bv -> pure (bv /= BV.zero (knownNat @1))
      Nothing -> malformedLLVMModule
                   "Call to llvm.abs.* with non-constant second argument"
                   [printSymExpr isIntMinPoison]
  callAbs callStack (LLVMAbsIntMinPoison shouldCheckIntMin) widthRepr src
