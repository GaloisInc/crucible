--------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel
  ( -- * Memories
    Mem
  , memRepr
  , mkMemVar
  , MemImpl(..)
  , SomePointer(..)
  , GlobalMap
  , emptyMem
  , memEndian
  , memAllocCount
  , memWriteCount
  , G.ppMem
  , doDumpMem
  , BlockSource(..)
  , nextBlock
  , MemOptions(..)
  , IndeterminateLoadBehavior(..)
  , defaultMemOptions
  , laxPointerMemOptions

  -- * Pointers
  , LLVMPointerType
  , pattern LLVMPointerRepr
  , pattern PtrRepr
  , pattern SizeT
  , LLVMPtr
  , pattern LLVMPointer
  , llvmPointerView
  , ptrWidth
  , G.ppPtr
  , G.ppTermExpr
  , llvmPointer_bv
  , Partial.ptrToBv
  , Partial.projectLLVM_bv

    -- * Memory operations
  , doMalloc
  , doMallocUnbounded
  , G.AllocType(..)
  , G.Mutability(..)
  , ME.FuncLookupError(..)
  , ME.ppFuncLookupError
  , doLookupHandle
  , doInstallHandle
  , doMemcpy
  , doMemset
  , doInvalidate
  , doCalloc
  , doFree
  , doAlloca
  , doLoad
  , doStore
  , doArrayStore
  , doArrayStoreUnbounded
  , doArrayConstStore
  , doArrayConstStoreUnbounded
  -- TODO(#1308): When GHC 9.6 support is dropped, deprecate these imports
  -- TOOD(#1406): After they have been deprecated for a while, move the
  -- implementations to `Strings` and remove these exports.
  , -- {-# DEPRECATED "Exported from Crucible.LLVM.MemModel.Strings instead" #-}
    loadString
  , -- {-# DEPRECATED "Exported from Crucible.LLVM.MemModel.Strings instead" #-}
    loadMaybeString
  , -- {-# DEPRECATED "Exported from Crucible.LLVM.MemModel.Strings instead" #-}
    strLen
  , uncheckedMemcpy

    -- * \"Raw\" operations with LLVMVal
  , LLVMVal(..)
  , ppLLVMValWithGlobals
  , FloatSize(..)
  , unpackMemValue
  , packMemValue
  , loadRaw
  , loadArrayConcreteSizeRaw
  , storeRaw
  , condStoreRaw
  , storeConstRaw
  , mallocRaw
  , mallocConstRaw
  , constToLLVMVal
  , constToLLVMValP
  , ptrMessage
  , Partial.PartLLVMVal(..)
  , Partial.assertSafe
  , explodeStringValue

    -- Re-exports from MemModel.Value
  , isZero
  , testEqual
  , llvmValStorableType

    -- * Storage types
  , StorageType
  , storageTypeF
  , StorageTypeF(..)
  , Field
  , storageTypeSize
  , fieldVal
  , fieldPad
  , fieldOffset
  , bitvectorType
  , arrayType
  , mkStructType
  , floatType
  , doubleType
  , x86_fp80Type
  , toStorableType

    -- * Pointer operations
  , ptrToPtrVal
  , mkNullPointer
  , ptrIsNull
  , ptrEq
  , ptrAdd
  , ptrSub
  , ptrDiff
  , doPtrAddOffset
  , doPtrSubtract
  , isValidPointer
  , isAllocatedAlignedPointer
  , muxLLVMPtr
  , G.isAligned

    -- * Disjointness
  , assertDisjointRegions
  , buildDisjointRegionsAssertion
  , buildDisjointRegionsAssertionWithSub

    -- * Globals
  , GlobalSymbol(..)
  , doResolveGlobal
  , registerGlobal
  , allocGlobals
  , allocGlobal
  , isGlobalPointer

    -- * Misc
  , llvmStatementExec
  , G.pushStackFrameMem
  , G.popStackFrameMem
  , G.asMemAllocationArrayStore
  , G.asMemMatchingArrayStore
  , SomeFnHandle(..)
  , G.SomeAlloc(..)
  , G.possibleAllocs
  , G.ppSomeAlloc
  , doConditionalWriteOperation
  , mergeWriteOperations
  , Partial.HasLLVMAnn
  , Partial.LLVMAnnMap
  , Partial.CexExplanation(..)
  , Partial.explainCex

    -- * PtrWidth (re-exports)
  , HasPtrWidth
  , pattern PtrWidth
  , withPtrWidth

    -- * Concretization
  , ML.concPtr
  , ML.concLLVMVal
  , ML.concMem
  , concMemImpl
  ) where

import           Prelude hiding (seq)

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.State
import           Data.Dynamic
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Text (Text)
import           Data.Word
import qualified GHC.Stack as GHC
import           Numeric.Natural (Natural)
import           System.IO (Handle, hPutStrLn)

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import           What4.Interface
import           What4.Expr( GroundValue )
import qualified What4.Expr.ArrayUpdateMap as AUM
import           What4.InterpretedFloatingPoint
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.Errors.MemoryError
   (MemErrContext, MemoryErrorReason(..), MemoryOp(..), ppMemoryErrorReason)
import qualified Lang.Crucible.LLVM.Errors.MemoryError as ME
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack, getCallStack)
import qualified Lang.Crucible.LLVM.MemModel.MemLog as ML
import           Lang.Crucible.LLVM.MemModel.Type
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Options
import           Lang.Crucible.LLVM.MemModel.Value
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.Utils
import           Lang.Crucible.Panic (panic)


import           GHC.Stack (HasCallStack)

----------------------------------------------------------------------
-- The MemImpl type

newtype BlockSource = BlockSource (IORef Natural)
type GlobalMap sym = Map L.Symbol (SomePointer sym)

nextBlock :: BlockSource -> IO Natural
nextBlock (BlockSource ref) =
  atomicModifyIORef' ref (\n -> (n+1, n))

-- | The implementation of an LLVM memory, containing an
-- allocation-block source, global map, handle map, and heap.
data MemImpl sym =
  MemImpl
  { memImplBlockSource :: BlockSource
  , memImplGlobalMap   :: GlobalMap sym
  , memImplSymbolMap   :: Map Natural L.Symbol -- inverse mapping to 'memImplGlobalMap'
  , memImplHandleMap   :: Map Natural Dynamic
  , memImplHeap        :: G.Mem sym
  }

memEndian :: MemImpl sym -> EndianForm
memEndian = G.memEndian . memImplHeap

memAllocCount :: MemImpl sym -> Int
memAllocCount = G.memAllocCount . memImplHeap

memWriteCount :: MemImpl sym -> Int
memWriteCount = G.memWriteCount . memImplHeap

-- | Produce a fresh empty memory.
--   NB, we start counting allocation blocks at '1'.
--   Block number 0 is reserved for representing raw bitvectors.
emptyMem :: EndianForm -> IO (MemImpl sym)
emptyMem endianness = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty Map.empty (G.emptyMem endianness)

-- | Pretty print a memory state to the given handle.
doDumpMem :: IsExprBuilder sym => Handle -> MemImpl sym -> IO ()
doDumpMem h mem = do
  hPutStrLn h (show (G.ppMem (memImplHeap mem)))

----------------------------------------------------------------------
-- Memory operations
--


-- | Assert that some undefined behavior doesn't occur when performing memory
-- model operations
assertUndefined ::
  (IsSymBackend sym bak, Partial.HasLLVMAnn sym) =>
  bak ->
  CallStack ->
  Pred sym ->
  (UB.UndefinedBehavior (RegValue' sym)) {- ^ The undesirable behavior -} ->
  IO ()
assertUndefined bak callStack p ub =
  do let sym = backendGetSym bak
     p' <- Partial.annotateUB sym callStack ub p
     assert bak p' $ AssertFailureSimError "Undefined behavior encountered" (show (UB.explain ub))


assertStoreError ::
  (IsSymBackend sym bak, Partial.HasLLVMAnn sym, 1 <= wptr) =>
  bak ->
  MemErrContext sym wptr ->
  MemoryErrorReason ->
  Pred sym ->
  IO ()
assertStoreError bak errCtx rsn p =
  do let sym = backendGetSym bak
     p' <- Partial.annotateME sym errCtx rsn p
     assert bak p' $ AssertFailureSimError "Memory store failed" (show (ppMemoryErrorReason rsn))

instance IsSymInterface sym => IntrinsicClass sym "LLVM_memory" where
  type Intrinsic sym "LLVM_memory" ctx = MemImpl sym

  -- NB: Here we are assuming the global maps of both memories are identical.
  -- This should be the case as memories are only supposed to allocate globals at
  -- startup, not during program execution.  We could check that the maps match,
  -- but that would be expensive...
  muxIntrinsic _sym _iTypes _nm _ p mem1 mem2 =
     do let MemImpl blockSource gMap1 sMap1 hMap1 m1 = mem1
        let MemImpl _blockSource _gMap2 _sMap2 hMap2 m2 = mem2
        --putStrLn "MEM MERGE"
        return $ MemImpl blockSource gMap1 sMap1
                   (Map.union hMap1 hMap2)
                   (G.mergeMem p m1 m2)

  pushBranchIntrinsic _sym _iTypes _nm _ctx mem =
     do let MemImpl nxt gMap sMap hMap m = mem
        --putStrLn "MEM PUSH BRANCH"
        return $ MemImpl nxt gMap sMap hMap $ G.branchMem m

  abortBranchIntrinsic _sym _iTypes _nm _ctx mem =
     do let MemImpl nxt gMap sMap hMap m = mem
        --putStrLn "MEM ABORT BRANCH"
        return $ MemImpl nxt gMap sMap hMap $ G.branchAbortMem m

-- | Top-level evaluation function for LLVM extension statements.
--   LLVM extension statements are used to implement the memory model operations.
llvmStatementExec ::
  (Partial.HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  EvalStmtFunc p sym LLVM
llvmStatementExec stmt cst =
  let simCtx = cst^.stateContext
   in withBackend simCtx $ \bak ->
        runStateT (evalStmt bak stmt) cst

type EvalM p sym ext rtp blocks ret args a =
  StateT (CrucibleState p sym ext rtp blocks ret args) IO a

-- | Actual workhorse function for evaluating LLVM extension statements.
--   The semantics are explicitly organized as a state transformer monad
--   that modifies the global state of the simulator; this captures the
--   memory accessing effects of these statements.
evalStmt :: forall p sym bak ext rtp blocks ret args tp.
  (IsSymBackend sym bak, Partial.HasLLVMAnn sym, GHC.HasCallStack, ?memOpts :: MemOptions) =>
  bak ->
  LLVMStmt (RegEntry sym) tp ->
  EvalM p sym ext rtp blocks ret args (RegValue sym tp)
evalStmt bak = eval
 where
  sym = backendGetSym bak

  getMem :: GlobalVar Mem ->
            EvalM p sym ext rtp blocks ret args (MemImpl sym)
  getMem mvar =
    do gs <- use (stateTree.actFrame.gpGlobals)
       case lookupGlobal mvar gs of
         Just mem -> return mem
         Nothing  ->
           panic "MemModel.evalStmt.getMem"
             [ "Global heap value not initialized."
             , "*** Global heap variable: " ++ show mvar
             ]

  setMem :: GlobalVar Mem ->
            MemImpl sym ->
            EvalM p sym ext rtp blocks ret args ()
  setMem mvar mem = stateTree.actFrame.gpGlobals %= insertGlobal mvar mem

  failedAssert :: String -> String -> EvalM p sym ext rtp blocks ret args a
  failedAssert msg details =
    lift $ addFailedAssertion bak $ AssertFailureSimError msg details

  eval :: LLVMStmt (RegEntry sym) tp ->
          EvalM p sym ext rtp blocks ret args (RegValue sym tp)
  eval (LLVM_PushFrame nm mvar) =
     do mem <- getMem mvar
        let heap' = G.pushStackFrameMem nm (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_PopFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.popStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_Alloca _w mvar (regValue -> sz) alignment loc) =
     do mem <- getMem mvar
        (ptr, mem') <- liftIO $ doAlloca bak mem sz alignment loc
        setMem mvar mem'
        return ptr

  eval (LLVM_Load mvar (regValue -> ptr) tpr valType alignment) =
     do mem <- getMem mvar
        liftIO $ doLoad bak mem ptr valType tpr alignment

  eval (LLVM_MemClear mvar (regValue -> ptr) bytes) =
    do mem <- getMem mvar
       z   <- liftIO $ bvZero sym knownNat
       len <- liftIO $ bvLit sym PtrWidth (bytesToBV PtrWidth bytes)
       mem' <- liftIO $ doMemset bak PtrWidth mem ptr z len
       setMem mvar mem'

  eval (LLVM_Store mvar (regValue -> ptr) tpr valType alignment (regValue -> val)) =
     do mem <- getMem mvar
        mem' <- liftIO $ doStore bak mem ptr tpr valType alignment val
        setMem mvar mem'

  eval (LLVM_LoadHandle mvar ltp (regValue -> ptr) args ret) =
     do mem <- getMem mvar
        let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
        mhandle <- liftIO $ doLookupHandle sym mem ptr
        let mop = MemLoadHandleOp ltp gsym ptr (memImplHeap mem)
        let expectedTp = FunctionHandleRepr args ret
        case mhandle of
           Left lookupErr -> lift $
             do p <- Partial.annotateME sym mop (BadFunctionPointer lookupErr) (falsePred sym)
                loc <- getCurrentProgramLoc sym
                let err = SimError loc (AssertFailureSimError "Failed to load function handle" (show (ME.ppFuncLookupError lookupErr)))
                addProofObligation bak (LabeledPred p err)
                abortExecBecause (AssertionFailure err)

           Right (VarargsFnHandle h) ->
             let err = failedAssert "Failed to load function handle"
                  (unlines
                   ["Expected function handle of type " <> show expectedTp
                   ,"for call to function " <> show (handleName h)
                   ,"but found varargs handle of non-matching type " ++ show (handleType h)
                   ]) in
             case handleArgTypes h of
               prefix Ctx.:> VectorRepr AnyRepr
                 | Just Refl <- testEquality ret (handleReturnType h)
                 -> Ctx.dropPrefix args prefix err (return . VarargsFnVal h)

               _ -> err

           Right (SomeFnHandle h)
             | Just Refl <- testEquality (handleType h) expectedTp -> return (HandleFnVal h)
             | otherwise -> failedAssert
                 "Failed to load function handle"
                 (unlines ["Expected function handle of type " <> show expectedTp
                          , "for call to function " <> show (handleName h)
                          , "but found calling handle of type " ++ show (handleType h)])

  eval (LLVM_ResolveGlobal _w mvar (GlobalSymbol symbol)) =
     do mem <- getMem mvar
        liftIO $ doResolveGlobal bak mem symbol

  eval (LLVM_PtrEq mvar (regValue -> x) (regValue -> y)) = do
     mem <- getMem mvar
     liftIO $ do
        v1 <- isValidPointer sym x mem
        v2 <- isValidPointer sym y mem
        v3 <- G.notAliasable sym x y (memImplHeap mem)

        let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
        assertUndefined bak callStack v1 $
          UB.CompareInvalidPointer UB.Eq (RV x) (RV y)
        assertUndefined bak callStack v2 $
          UB.CompareInvalidPointer UB.Eq (RV x) (RV y)

        unless (laxConstantEquality ?memOpts) $
          do let allocs_doc = G.ppAllocs (G.memAllocs (memImplHeap mem))
             let x_doc = G.ppPtr x
             let y_doc = G.ppPtr y
             -- TODO: Is this undefined behavior? If so, add to the UB module
             assert bak v3 $
               AssertFailureSimError
               "Const pointers compared for equality"
               (unlines [ show x_doc
                        , show y_doc
                        , show allocs_doc
                        ])
        ptrEq sym PtrWidth x y

  eval (LLVM_PtrLe mvar (regValue -> x) (regValue -> y)) = do
    mem <- getMem mvar
    liftIO $ do
       v1 <- isValidPointer sym x mem
       v2 <- isValidPointer sym y mem

       let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
       assertUndefined bak callStack v1
        (UB.CompareInvalidPointer UB.Leq (RV x) (RV y))
       assertUndefined bak callStack v2
        (UB.CompareInvalidPointer UB.Leq (RV x) (RV y))

       (le, valid) <- ptrLe sym PtrWidth x y
       assertUndefined bak callStack valid
         (UB.CompareDifferentAllocs (RV x) (RV y))

       pure le

  eval (LLVM_PtrAddOffset _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrAddOffset bak mem x y

  eval (LLVM_PtrSubtract _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrSubtract bak mem x y

  eval LLVM_Debug{} = pure ()


mkMemVar :: Text
         -> HandleAllocator
         -> IO (GlobalVar Mem)
mkMemVar memName halloc = freshGlobalVar halloc memName knownRepr


-- | For now, the core message should be on the first line, with details
-- on further lines. Later we should make it more structured.
ptrMessage ::
  (IsSymInterface sym) =>
  String ->
  LLVMPtr sym wptr {- ^ pointer involved in message -} ->
  StorageType      {- ^ type of value pointed to    -} ->
  String
ptrMessage msg ptr ty =
  unlines [ msg
          , "  address " ++ show (G.ppPtr ptr)
          , "  at type " ++ show (G.ppType ty)
          ]

-- | Allocate memory on the stack frame of the currently executing function.
doAlloca ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  SymBV sym wptr {- ^ allocation size -} ->
  Alignment      {- ^ pointer alignment -} ->
  String         {- ^ source location for use in error messages -} ->
  IO (LLVMPtr sym wptr, MemImpl sym)
doAlloca bak mem sz alignment loc = do
  let sym = backendGetSym bak
  blkNum <- liftIO $ nextBlock (memImplBlockSource mem)
  blk <- liftIO $ natLit sym blkNum
  z <- liftIO $ bvZero sym PtrWidth

  let heap' = G.allocMem G.StackAlloc blkNum (Just sz) alignment G.Mutable loc (memImplHeap mem)
  let ptr   = LLVMPointer blk z
  let mem'  = mem{ memImplHeap = heap' }
  mem'' <- if laxLoadsAndStores ?memOpts
                && indeterminateLoadBehavior ?memOpts == StableSymbolic
           then doConstStoreStableSymbolic bak mem' ptr (Just sz) alignment
           else pure mem'
  pure (ptr, mem'')

-- | Load a 'RegValue' from memory. Both the 'StorageType' and 'TypeRepr'
-- arguments should be computed from a single 'MemType' using
-- 'toStorableType' and 'Lang.Crucible.LLVM.Translation.Types.llvmTypeAsRepr'
-- respectively.
--
-- Precondition: the pointer is valid and aligned, and the loaded value is defined.
doLoad ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ pointer to load from      -} ->
  StorageType      {- ^ type of value to load     -} ->
  TypeRepr tp      {- ^ crucible type of the result -} ->
  Alignment        {- ^ assumed pointer alignment -} ->
  IO (RegValue sym tp)
doLoad bak mem ptr valType tpr alignment = do
  let sym = backendGetSym bak
  unpackMemValue sym tpr =<<
    Partial.assertSafe bak =<<
      loadRaw sym mem ptr valType alignment

-- | Store a 'RegValue' in memory. Both the 'StorageType' and 'TypeRepr'
-- arguments should be computed from a single 'MemType' using
-- 'toStorableType' and 'Lang.Crucible.LLVM.Translation.Types.llvmTypeAsRepr'
-- respectively.
--
-- Precondition: the pointer is valid and points to a mutable memory region.
doStore ::
  ( IsSymBackend sym bak
  , HasPtrWidth wptr
  , Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ pointer to store into  -} ->
  TypeRepr tp ->
  StorageType      {- ^ type of value to store -} ->
  Alignment ->
  RegValue sym tp  {- ^ value to store         -} ->
  IO (MemImpl sym)
doStore bak mem ptr tpr valType alignment val = do
    --putStrLn "MEM STORE"
    let sym = backendGetSym bak
    val' <- packMemValue sym valType tpr val
    storeRaw bak mem ptr valType alignment val'

data SomeFnHandle where
  SomeFnHandle    :: FnHandle args ret -> SomeFnHandle
  VarargsFnHandle :: FnHandle (args ::> VectorType AnyType) ret -> SomeFnHandle

-- | Allocate and zero a memory region with /size * number/ bytes.
--
-- Precondition: the multiplication /size * number/ does not overflow.
doCalloc ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  SymBV sym wptr {- ^ size   -} ->
  SymBV sym wptr {- ^ number -} ->
  Alignment {- ^ Minimum alignment of the resulting allocation -} ->
  IO (LLVMPtr sym wptr, MemImpl sym)
doCalloc bak mem sz num alignment = do
  let sym = backendGetSym bak
  (ov, sz') <- unsignedWideMultiplyBV sym sz num
  ov_iszero <- notPred sym =<< bvIsNonzero sym ov
  -- TODO, this probably shouldn't be UB
  assert bak ov_iszero
     (AssertFailureSimError "Multiplication overflow in calloc()" "")

  loc <- plSourceLoc <$> getCurrentProgramLoc sym
  let displayString = "<calloc> " ++ show loc
  z <- bvZero sym knownNat
  (ptr, mem') <- doMalloc bak G.HeapAlloc G.Mutable displayString mem sz' alignment
  mem'' <- doMemset bak PtrWidth mem' ptr z sz'
  return (ptr, mem'')

-- | Allocate a memory region.
doMalloc
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> SymBV sym wptr {- ^ allocation size -}
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMalloc bak allocType mut loc mem sz alignment = doMallocSize (Just sz) bak allocType mut loc mem alignment

-- | Allocate a memory region of unbounded size.
doMallocUnbounded
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMallocUnbounded = doMallocSize Nothing

doMallocSize
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => Maybe (SymBV sym wptr) {- ^ allocation size -}
  -> bak
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMallocSize sz bak allocType mut loc mem alignment = do
  let sym = backendGetSym bak
  blkNum <- nextBlock (memImplBlockSource mem)
  blk    <- natLit sym blkNum
  z      <- bvZero sym PtrWidth
  let heap' = G.allocMem allocType blkNum sz alignment mut loc (memImplHeap mem)
  let ptr   = LLVMPointer blk z
  let mem'  = mem{ memImplHeap = heap' }
  mem'' <- if laxLoadsAndStores ?memOpts
                && allocType == G.HeapAlloc
                && indeterminateLoadBehavior ?memOpts == StableSymbolic
           then doConstStoreStableSymbolic bak mem' ptr sz alignment
           else pure mem'
  return (ptr, mem'')

-- | Associate a function handle with an existing allocation.
--
-- This can overwrite existing allocation/handle associations, and is used to do
-- so when registering lazily-translated CFGs.
--
-- See also "Lang.Crucible.LLVM.Functions".
doInstallHandle
  :: (Typeable a, IsSymBackend sym bak)
  => bak
  -> LLVMPtr sym wptr
  -> a {- ^ handle -}
  -> MemImpl sym
  -> IO (MemImpl sym)
doInstallHandle _bak ptr x mem =
  case asNat (llvmPointerBlock ptr) of
    Just blkNum ->
      do let hMap' = Map.insert blkNum (toDyn x) (memImplHandleMap mem)
         return mem{ memImplHandleMap = hMap' }
    Nothing ->
      panic "MemModel.doInstallHandle"
        [ "Attempted to install handle for symbolic pointer"
        , "  " ++ show (ppPtr ptr)
        ]

-- | Look up the handle associated with the given pointer, if any.
doLookupHandle
  :: (Typeable a, IsSymInterface sym)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (Either ME.FuncLookupError a)
doLookupHandle _sym mem ptr = do
  let LLVMPointer blk _ = ptr
  case asNat blk of
    Nothing -> return (Left ME.SymbolicPointer)
    Just i
      | i == 0 -> return (Left ME.RawBitvector)
      | otherwise ->
          case Map.lookup i (memImplHandleMap mem) of
            Nothing -> return (Left ME.NoOverride)
            Just x ->
              case fromDynamic x of
                Nothing -> return (Left (ME.Uncallable (dynTypeRep x)))
                Just a  -> return (Right a)

-- | Free the memory region pointed to by the given pointer.
--
-- Precondition: the pointer either points to the beginning of an allocated
-- region, or is null. Freeing a null pointer has no effect.
doFree
  :: (IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym)
  => bak
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (MemImpl sym)
doFree bak mem ptr = do
  let sym = backendGetSym bak
  let LLVMPointer blk _off = ptr
  loc <- show . plSourceLoc <$> getCurrentProgramLoc sym
  (heap', p1, p2, notFreed) <- G.freeMem sym PtrWidth ptr (memImplHeap mem) loc

  -- If this pointer is a handle pointer, remove the associated data
  let hMap' =
       case asNat blk of
         Just i  -> Map.delete i (memImplHandleMap mem)
         Nothing -> memImplHandleMap mem

  -- NB: free is defined and has no effect if passed a null pointer
  isNull    <- ptrIsNull sym PtrWidth ptr
  p1'       <- orPred sym p1 isNull
  p2'       <- orPred sym p2 isNull
  notFreed' <- orPred sym notFreed isNull
  let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
  assertUndefined bak callStack p1' (UB.FreeBadOffset (RV ptr))
  assertUndefined bak callStack p2' (UB.FreeUnallocated (RV ptr))
  assertUndefined bak callStack notFreed' (UB.DoubleFree (RV ptr))

  return mem{ memImplHeap = heap', memImplHandleMap = hMap' }

-- | Fill a memory range with copies of the specified byte.
--
-- Precondition: the memory range falls within a valid allocated region.
doMemset ::
  (1 <= w, IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym) =>
  bak ->
  NatRepr w ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  SymBV sym 8      {- ^ fill byte   -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doMemset bak w mem dest val len = do
  let sym = backendGetSym bak
  len' <- sextendBVTo sym w PtrWidth len

  (heap', p) <- G.setMem sym PtrWidth dest val len' (memImplHeap mem)

  let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
  assertUndefined bak callStack p $
    UB.MemsetInvalidRegion (RV dest) (RV val) (RV len)

  return mem{ memImplHeap = heap' }

doInvalidate ::
  ( 1 <= w, IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  NatRepr w ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  Text             {- ^ message     -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doInvalidate bak w mem dest msg len = do
  let sym = backendGetSym bak
  len' <- sextendBVTo sym w PtrWidth len

  (heap', p) <- if laxLoadsAndStores ?memOpts &&
                   indeterminateLoadBehavior ?memOpts == StableSymbolic
                then do p <- G.isAllocatedMutable sym PtrWidth noAlignment dest (Just len') (memImplHeap mem)
                        mem' <- doStoreStableSymbolic bak mem dest (Just len') noAlignment
                        pure (memImplHeap mem', p)
                else G.invalidateMem sym PtrWidth dest msg len' (memImplHeap mem)

  let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) dest
  let mop = MemInvalidateOp msg gsym dest len (memImplHeap mem)
  p' <- Partial.annotateME sym mop UnwritableRegion p
  assert bak p' $ AssertFailureSimError "Invalidation of unallocated or readonly region" ""

  return mem{ memImplHeap = heap' }

-- | Store an array in memory.
--
-- Precondition: the pointer is valid and points to a mutable memory region.
doArrayStore
  :: (IsSymBackend sym bak, HasPtrWidth w, Partial.HasLLVMAnn sym)
  => bak
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> SymBV sym w {- ^ array length -}
  -> IO (MemImpl sym)
doArrayStore bak mem ptr alignment arr len = doArrayStoreSize (Just len) bak mem ptr alignment arr

-- | Store an array of unbounded length in memory.
--
-- Precondition: the pointer is valid and points to a mutable memory region.
doArrayStoreUnbounded
  :: (IsSymBackend sym bak, HasPtrWidth w, Partial.HasLLVMAnn sym)
  => bak
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> IO (MemImpl sym)
doArrayStoreUnbounded = doArrayStoreSize Nothing


doArrayStoreSize
  :: (IsSymBackend sym bak, HasPtrWidth w, Partial.HasLLVMAnn sym)
  => Maybe (SymBV sym w) {- ^ possibly-unbounded array length -}
  -> bak
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> IO (MemImpl sym)
doArrayStoreSize len bak mem ptr alignment arr = do
  let sym = backendGetSym bak
  (heap', p1, p2) <-
    G.writeArrayMem sym PtrWidth ptr alignment arr len (memImplHeap mem)

  let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
  let mop = MemStoreBytesOp gsym ptr len (memImplHeap mem)

  assertStoreError bak mop UnwritableRegion p1
  let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
  assertUndefined bak callStack p2 (UB.WriteBadAlignment (RV ptr) alignment)

  return mem { memImplHeap = heap' }

-- | Store an array in memory.
--
-- Precondition: the pointer is valid and points to a mutable or immutable memory region.
-- Therefore it can be used to initialize read-only memory regions.
doArrayConstStore
  :: (IsSymBackend sym bak, HasPtrWidth w, Partial.HasLLVMAnn sym)
  => bak
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> SymBV sym w {- ^ array length -}
  -> IO (MemImpl sym)
doArrayConstStore bak mem ptr alignment arr len =
  doArrayConstStoreSize (Just len) bak mem ptr alignment arr

-- | Store an array of unbounded length in memory.
--
-- Precondition: the pointer is valid and points to a mutable or immutable memory region.
-- Therefore it can be used to initialize read-only memory regions.
doArrayConstStoreUnbounded
  :: (IsSymBackend sym bak, HasPtrWidth w, Partial.HasLLVMAnn sym)
  => bak
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> IO (MemImpl sym)
doArrayConstStoreUnbounded = doArrayConstStoreSize Nothing

-- | The workhorse for 'doArrayConstStore' (if the first argument is
-- @'Just' len@) or 'doArrayConstStoreUnbounded' (if the first argument is
-- 'Nothing').
doArrayConstStoreSize
  :: (IsSymBackend sym bak, HasPtrWidth w, Partial.HasLLVMAnn sym)
  => Maybe (SymBV sym w) {- ^ possibly-unbounded array length -}
  -> bak
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> IO (MemImpl sym)
doArrayConstStoreSize len bak mem ptr alignment arr = do
  let sym = backendGetSym bak
  (heap', p1, p2) <-
    G.writeArrayConstMem sym PtrWidth ptr alignment arr len (memImplHeap mem)

  let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
  let mop = MemStoreBytesOp gsym ptr len (memImplHeap mem)

  assertStoreError bak mop UnwritableRegion p1
  let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
  assertUndefined bak callStack p2 (UB.WriteBadAlignment (RV ptr) alignment)

  return mem { memImplHeap = heap' }

-- | Copy memory from source to destination.
--
-- Precondition: the source and destination pointers fall within valid allocated
-- regions.
doMemcpy ::
  ( 1 <= w, IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  NatRepr w ->
  MemImpl sym ->
  Bool {- ^ if true, require disjoint memory regions -} ->
  LLVMPtr sym wptr {- ^ destination -} ->
  LLVMPtr sym wptr {- ^ source      -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doMemcpy bak w mem mustBeDisjoint dest src len = do
  let sym = backendGetSym bak
  len' <- sextendBVTo sym w PtrWidth len

  (heap', p1, p2) <- G.copyMem sym PtrWidth dest src len' (memImplHeap mem)

  let gsym_dest = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) dest
  let gsym_src = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) src

  let mop = MemCopyOp (gsym_dest, dest) (gsym_src, src) len (memImplHeap mem)

  p1' <- applyUnless (laxLoadsAndStores ?memOpts)
                     (Partial.annotateME sym mop UnreadableRegion) p1
  p2' <- Partial.annotateME sym mop UnwritableRegion p2

  assert bak p1' $ AssertFailureSimError "Mem copy failed" "Invalid copy source"
  assert bak p2' $ AssertFailureSimError "Mem copy failed" "Invalid copy destination"

  when mustBeDisjoint (assertDisjointRegions bak mop (bvWidth len) dest len src len)

  return mem{ memImplHeap = heap' }

unsymbol :: L.Symbol -> String
unsymbol (L.Symbol s) = s

-- | Copy memory from source to destination.  This version does
--   no checks to verify that the source and destination allocations
--   are allocated and appropriately sized.
uncheckedMemcpy ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  LLVMPtr sym wptr {- ^ source      -} ->
  SymBV sym wptr   {- ^ length      -} ->
  IO (MemImpl sym)
uncheckedMemcpy sym mem dest src len = do
  (heap', _p1, _p2) <- G.copyMem sym PtrWidth dest src len (memImplHeap mem)
  return mem{ memImplHeap = heap' }

doPtrSubtract ::
  (IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym) =>
  bak ->
  MemImpl sym ->
  LLVMPtr sym wptr ->
  LLVMPtr sym wptr ->
  IO (SymBV sym wptr)
doPtrSubtract bak mem x y = do
  let sym = backendGetSym bak
  (diff, valid) <- ptrDiff sym PtrWidth x y
  let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
  assertUndefined bak callStack valid $
    UB.PtrSubDifferentAllocs (RV x) (RV y)
  pure diff

-- | Add an offset to a pointer and asserts that the result is a valid pointer.
doPtrAddOffset ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ base pointer -} ->
  SymBV sym wptr   {- ^ offset       -} ->
  IO (LLVMPtr sym wptr)
doPtrAddOffset bak m x off = do
  let sym = backendGetSym bak
  isBV <- ptrIsBv sym x
  x' <- ptrAdd sym PtrWidth x off
  v <- case asConstantPred isBV of
         Just True  -> return isBV
         _ -> orPred sym isBV =<< G.isValidPointer sym PtrWidth x' (memImplHeap m)
  unless (laxLoadsAndStores ?memOpts) $
    let callStack = getCallStack (m ^. to memImplHeap . ML.memState)
    in assertUndefined bak callStack v (UB.PtrAddOffsetOutOfBounds (RV x) (RV off))
  return x'

-- | Store a fresh symbolic value of the appropriate size in the supplied
-- pointer. This is used in various spots whenever 'laxLoadsAndStores' is
-- enabled and 'indeterminateLoadBehavior' is set to 'StableSymbolic'.
doStoreStableSymbolic ::
  (IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym) =>
  bak ->
  MemImpl sym ->
  LLVMPtr sym wptr       {- ^ destination       -} ->
  Maybe (SymBV sym wptr) {- ^ allocation size   -} ->
  Alignment              {- ^ pointer alignment -} ->
  IO (MemImpl sym)
doStoreStableSymbolic bak mem ptr mbSz alignment = do
  let sym = backendGetSym bak
  bytes <- freshConstant sym emptySymbol
             (BaseArrayRepr (Ctx.singleton (BaseBVRepr ?ptrWidth))
                            (BaseBVRepr (knownNat @8)))
  case mbSz of
    Just sz -> doArrayStore bak mem ptr alignment bytes sz
    Nothing -> doArrayStoreUnbounded bak mem ptr alignment bytes

-- | Store a fresh symbolic value of the appropriate size in the supplied
-- pointer. This is used in various spots whenever 'laxLoadsAndStores' is
-- enabled and 'indeterminateLoadBehavior' is set to 'StableSymbolic'.
--
-- Precondition: the pointer is valid and points to a mutable or immutable
-- memory region. Therefore it can be used to initialize read-only memory
-- regions.
doConstStoreStableSymbolic ::
  (IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym) =>
  bak ->
  MemImpl sym ->
  LLVMPtr sym wptr       {- ^ destination       -} ->
  Maybe (SymBV sym wptr) {- ^ allocation size   -} ->
  Alignment              {- ^ pointer alignment -} ->
  IO (MemImpl sym)
doConstStoreStableSymbolic bak mem ptr mbSz alignment = do
  let sym = backendGetSym bak
  bytes <- freshConstant sym emptySymbol
             (BaseArrayRepr (Ctx.singleton (BaseBVRepr ?ptrWidth))
                            (BaseBVRepr (knownNat @8)))
  case mbSz of
    Just sz -> doArrayConstStore bak mem ptr alignment bytes sz
    Nothing -> doArrayConstStoreUnbounded bak mem ptr alignment bytes

-- | This predicate tests if the pointer is a valid, live pointer
--   into the heap, OR is the distinguished NULL pointer.
isValidPointer ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  LLVMPtr sym wptr ->
  MemImpl sym ->
  IO (Pred sym)
isValidPointer sym p mem =
   do np <- ptrIsNull sym PtrWidth p
      case asConstantPred np of
        Just True  -> return np
        Just False -> G.isValidPointer sym PtrWidth p (memImplHeap mem)
        _ -> orPred sym np =<< G.isValidPointer sym PtrWidth p (memImplHeap mem)

-- | Return the condition required to prove that the pointer points to
-- a range of 'size' bytes that falls within an allocated region of
-- the appropriate mutability, and also that the pointer is
-- sufficiently aligned.
isAllocatedAlignedPointer ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  Alignment           {- ^ minimum required pointer alignment                 -} ->
  G.Mutability        {- ^ 'Mutable' means pointed-to region must be writable -} ->
  LLVMPtr sym w       {- ^ pointer                                            -} ->
  Maybe (SymBV sym w) {- ^ size (@Nothing@ means entire address space)        -} ->
  MemImpl sym         {- ^ memory                                             -} ->
  IO (Pred sym)
isAllocatedAlignedPointer sym w alignment mutability ptr size mem =
  G.isAllocatedAlignedPointer sym w alignment mutability ptr size (memImplHeap mem)

-- | Compute the length of a null-terminated string.
--
--   The pointer to read from must be concrete and nonnull.  The contents
--   of the string may be symbolic; HOWEVER, this function will not terminate
--   until it eventually reaches a concete null-terminator or a load error.
strLen ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  IO (SymBV sym wptr)
strLen bak mem = go (BV.zero PtrWidth) (truePred sym)
  where
  sym = backendGetSym bak

  go !n cond p =
    loadRaw sym mem p (bitvectorType 1) noAlignment >>= \case
      Partial.Err pe ->
        do ast <- impliesPred sym cond pe
           assert bak ast $ AssertFailureSimError "Error during memory load: strlen" ""
           bvZero sym PtrWidth -- bogus value, but have to return something...
      Partial.NoErr loadok llvmval ->
        do ast <- impliesPred sym cond loadok
           assert bak ast $ AssertFailureSimError "Error during memory load: strlen" ""
           v <- unpackMemValue sym (LLVMPointerRepr (knownNat @8)) llvmval
           let err = AssertFailureSimError "Found pointer instead of byte in string passed to `strlen`" ""
           test <- bvIsNonzero sym =<< Partial.ptrToBv bak err v
           iteM bvIte sym
             test
             (do cond' <- andPred sym cond test
                 p'    <- doPtrAddOffset bak mem p =<< bvOne sym PtrWidth
                 case BV.succUnsigned PtrWidth n of
                   Just n_1 -> go n_1 cond' p'
                   Nothing -> panic "Lang.Crucible.LLVM.MemModel.strLen" ["string length exceeds pointer width"])
             (bvLit sym PtrWidth n)


-- | Load a null-terminated string from the memory.
--
-- The pointer to read from must be concrete and nonnull.  Moreover,
-- we require all the characters in the string to be concrete.
-- Otherwise it is very difficult to tell when the string has
-- terminated.  If a maximum number of characters is provided, no more
-- than that number of charcters will be read.  In either case,
-- `loadString` will stop reading if it encounters a null-terminator.
loadString :: forall sym bak wptr.
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions, GHC.HasCallStack ) =>
  bak ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  Maybe Int        {- ^ maximum characters to read -} ->
  IO [Word8]
loadString bak mem = go id
 where
  sym = backendGetSym bak

  go :: ([Word8] -> [Word8]) -> LLVMPtr sym wptr -> Maybe Int -> IO [Word8]
  go f _ (Just 0) = return $ f []
  go f p maxChars = do
     v <- doLoad bak mem p (bitvectorType 1) (LLVMPointerRepr (knownNat :: NatRepr 8)) noAlignment
     let err = AssertFailureSimError "Found pointer instead of byte when loading string" ""
     x <- Partial.ptrToBv bak err v
     case BV.asUnsigned <$> asBV x of
       Just 0 -> return $ f []
       Just c -> do
           let c' :: Word8 = toEnum $ fromInteger c
           p' <- doPtrAddOffset bak mem p =<< bvOne sym PtrWidth
           go (f . (c':)) p' (fmap (\n -> n - 1) maxChars)
       Nothing ->
         addFailedAssertion bak
            $ Unsupported GHC.callStack "Symbolic value encountered when loading a string"

-- | Like 'loadString', except the pointer to load may be null.  If
--   the pointer is null, we return Nothing.  Otherwise we load
--   the string as with 'loadString' and return it.
loadMaybeString ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions, GHC.HasCallStack ) =>
  bak ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  Maybe Int        {- ^ maximum characters to read -} ->
  IO (Maybe [Word8])
loadMaybeString bak mem ptr n = do
  let sym = backendGetSym bak
  isnull <- ptrIsNull sym PtrWidth ptr
  case asConstantPred isnull of
    Nothing    -> addFailedAssertion bak
                    $ Unsupported GHC.callStack "Symbolic pointer encountered when loading a string"
    Just True  -> return Nothing
    Just False -> Just <$> loadString bak mem ptr n


toStorableType :: (MonadFail m, HasPtrWidth wptr)
               => MemType
               -> m StorageType
toStorableType mt =
  case mt of
    IntType n -> return $ bitvectorType (bitsToBytes n)
    PtrType _ -> return $ bitvectorType (bitsToBytes (natValue PtrWidth))
    PtrOpaqueType -> return $ bitvectorType (bitsToBytes (natValue PtrWidth))
    FloatType -> return $ floatType
    DoubleType -> return $ doubleType
    X86_FP80Type -> return $ x86_fp80Type
    ArrayType n x -> arrayType (fromIntegral n) <$> toStorableType x
    VecType n x -> arrayType (fromIntegral n) <$> toStorableType x
    MetadataType -> fail "toStorableType: Cannot store metadata values"
    StructType si -> mkStructType <$> traverse transField (siFields si)
      where transField :: MonadFail m => FieldInfo -> m (StorageType, Bytes)
            transField fi = do
               t <- toStorableType $ fiType fi
               return (t, fiPadding fi)

----------------------------------------------------------------------
-- "Raw" operations
--

-- | Load an LLVM value from memory. Asserts that the pointer is valid and the
-- result value is not undefined.
loadRaw :: ( IsSymInterface sym, HasPtrWidth wptr, Partial.HasLLVMAnn sym
           , ?memOpts :: MemOptions )
        => sym
        -> MemImpl sym
        -> LLVMPtr sym wptr
        -> StorageType
        -> Alignment
        -> IO (Partial.PartLLVMVal sym)
loadRaw sym mem ptr valType alignment = do
  let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
  G.readMem sym PtrWidth gsym ptr valType alignment (memImplHeap mem)

-- | Load an array with concrete size from memory.
loadArrayConcreteSizeRaw ::
  forall sym wptr .
  (IsSymInterface sym, HasPtrWidth wptr, Partial.HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr ->
  Natural ->
  Alignment ->
  IO (Either (Pred sym) (Pred sym, SymArray sym (SingleCtx (BaseBVType wptr)) (BaseBVType 8)))
loadArrayConcreteSizeRaw sym mem ptr sz alignment
  | sz == 0 = do
    zero_bv <- bvZero sym knownNat
    zero_arr <- constantArray sym (Ctx.singleton $ BaseBVRepr PtrWidth) zero_bv
    return $ Right (truePred sym, zero_arr)
  | otherwise = do
    let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
    res <- G.readMem sym PtrWidth gsym ptr (arrayType sz $ bitvectorType 1) alignment (memImplHeap mem)
    case res of
      Partial.NoErr ok llvm_val_arr -> do
        case llvm_val_arr of
          LLVMValArray _ llvm_vals -> do
            let aum = AUM.fromAscList knownRepr $ V.toList $ V.imap
                  (\i -> \case
                    LLVMValInt _ byte | Just Refl <- testEquality (knownNat @8) (bvWidth byte) ->
                      (Ctx.singleton $ BVIndexLit PtrWidth $ BV.mkBV PtrWidth $ fromIntegral i, byte)
                    _ -> panic "MemModel.loadArrayRaw" ["expected LLVMValInt"])
                  llvm_vals
            zero_bv <- bvZero sym knownNat
            arr <- arrayFromMap sym (Ctx.singleton $ BaseBVRepr PtrWidth) aum zero_bv
            return $ Right (ok, arr)
          _ -> panic "MemModel.loadArrayRaw" ["expected LLVMValArray"]
      Partial.Err err -> return $ Left err

-- | Store an LLVM value in memory. Asserts that the pointer is valid and points
-- to a mutable memory region.
storeRaw ::
     ( IsSymBackend sym bak
     , HasPtrWidth wptr
     , Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> StorageType      {- ^ type of value to store -}
  -> Alignment
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeRaw bak mem ptr valType alignment val = do
    let sym = backendGetSym bak
    let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
    (heap', p1, p2) <- G.writeMem sym PtrWidth gsym ptr valType alignment val (memImplHeap mem)

    let mop = MemStoreOp valType gsym ptr (memImplHeap mem)

    assertStoreError bak mop UnwritableRegion p1
    let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
    assertUndefined bak callStack p2 (UB.WriteBadAlignment (RV ptr) alignment)

    return mem{ memImplHeap = heap' }

-- | Perform a memory write operation if the condition is true,
-- do not change the memory otherwise.
--
-- Asserts that the write operation is valid when cond is true.
doConditionalWriteOperation
  :: (IsSymBackend sym bak)
  => bak
  -> MemImpl sym
  -> Pred sym {- ^ write condition -}
  -> (MemImpl sym -> IO (MemImpl sym)) {- ^ memory write operation -}
  -> IO (MemImpl sym)
doConditionalWriteOperation bak mem cond write_op =
  mergeWriteOperations bak mem cond write_op return

-- | Merge memory write operations on condition: if the condition is true,
-- perform the true branch write operation, otherwise perform the false branch
-- write operation.
--
-- Asserts that the true branch write operation is valid when cond is true, and
-- that the false branch write operation is valid when cond is not true.
mergeWriteOperations
  :: (IsSymBackend sym bak)
  => bak
  -> MemImpl sym
  -> Pred sym {- ^ merge condition -}
  -> (MemImpl sym -> IO (MemImpl sym)) {- ^ true branch memory write operation -}
  -> (MemImpl sym -> IO (MemImpl sym)) {- ^ false branch memory write operation -}
  -> IO (MemImpl sym)
mergeWriteOperations bak mem cond true_write_op false_write_op = do
  let sym = backendGetSym bak
  let branched_mem = mem { memImplHeap = G.branchMem $ memImplHeap mem }
  loc <- getCurrentProgramLoc sym

  true_frame_id <- pushAssumptionFrame bak
  addAssumption bak (GenericAssumption loc "conditional memory write predicate" cond)
  true_mutated_heap <- memImplHeap <$> true_write_op branched_mem
  _ <- popAssumptionFrame bak true_frame_id

  false_frame_id <- pushAssumptionFrame bak
  not_cond <- notPred sym cond
  addAssumption bak (GenericAssumption loc "conditional memory write predicate" not_cond)
  false_mutated_heap <- memImplHeap <$> false_write_op branched_mem
  _ <- popAssumptionFrame bak false_frame_id

  return $!
    mem { memImplHeap = G.mergeMem cond true_mutated_heap false_mutated_heap }

-- | Store an LLVM value in memory if the condition is true, and
-- otherwise leaves memory unchanged.
--
-- Asserts that the pointer is valid and points to a mutable memory
-- region when cond is true.
condStoreRaw ::
     ( IsSymBackend sym bak
     , HasPtrWidth wptr
     , Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions
     )
  => bak
  -> MemImpl sym
  -> Pred sym {- ^ Predicate that determines if we actually write. -}
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> StorageType      {- ^ type of value to store -}
  -> Alignment
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
condStoreRaw bak mem cond ptr valType alignment val = do
  let sym = backendGetSym bak
  let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
  -- Get current heap
  let preBranchHeap = memImplHeap mem
  -- Push a branch to the heap
  let postBranchHeap = G.branchMem preBranchHeap

  let mop = MemStoreOp valType gsym ptr preBranchHeap

  -- Write to the heap
  (postWriteHeap, isAllocated, isAligned) <- G.writeMem sym PtrWidth gsym ptr valType alignment val (memImplHeap mem)
  -- Assert is allocated if write executes
  do condIsAllocated <- impliesPred sym cond isAllocated
     assertStoreError bak mop UnwritableRegion condIsAllocated
  -- Assert is aligned if write executes
  do condIsAligned <- impliesPred sym cond isAligned
     let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
     assertUndefined bak callStack condIsAligned (UB.WriteBadAlignment (RV ptr) alignment)
  -- Merge the write heap and non-write heap
  let mergedHeap = G.mergeMem cond postWriteHeap postBranchHeap
  -- Return new memory
  return $! mem{ memImplHeap = mergedHeap }

-- | Store an LLVM value in memory. The pointed-to memory region may
-- be either mutable or immutable; thus 'storeConstRaw' can be used to
-- initialize read-only memory regions.
storeConstRaw ::
     ( IsSymBackend sym bak
     , HasPtrWidth wptr
     , Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> StorageType      {- ^ type of value to store -}
  -> Alignment
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeConstRaw bak mem ptr valType alignment val = do
    let sym = backendGetSym bak
    let gsym = unsymbol <$> isGlobalPointer (memImplSymbolMap mem) ptr
    (heap', p1, p2) <- G.writeConstMem sym PtrWidth gsym ptr valType alignment val (memImplHeap mem)

    let mop = MemStoreOp valType gsym ptr (memImplHeap mem)

    assertStoreError bak mop UnwritableRegion p1
    let callStack = getCallStack (mem ^. to memImplHeap . ML.memState)
    assertUndefined bak callStack p2 (UB.WriteBadAlignment (RV ptr) alignment)

    return mem{ memImplHeap = heap' }

-- | Allocate a memory region on the heap, with no source location info.
mallocRaw
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> MemImpl sym
  -> SymBV sym wptr {- ^ size in bytes -}
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocRaw bak mem sz alignment =
  doMalloc bak G.HeapAlloc G.Mutable "<malloc>" mem sz alignment

-- | Allocate a read-only memory region on the heap, with no source location info.
mallocConstRaw
  :: ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
     , ?memOpts :: MemOptions )
  => bak
  -> MemImpl sym
  -> SymBV sym wptr
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocConstRaw bak mem sz alignment =
  doMalloc bak G.HeapAlloc G.Immutable "<malloc>" mem sz alignment

----------------------------------------------------------------------
-- Packing and unpacking
--

unpackZero ::
  (HasCallStack, IsSymInterface sym) =>
  sym ->
  StorageType ->
  TypeRepr tp {- ^ Crucible type     -} ->
  IO (RegValue sym tp)
unpackZero sym tp tpr =
 let mismatch = storageTypeMismatch "MemModel.unpackZero" tp tpr in
 case storageTypeF tp of
  Bitvector bytes ->
    zeroInt sym bytes $ \case
      Nothing -> fail ("Improper storable type: " ++ show tp)
      Just (blk, bv) ->
        case tpr of
          LLVMPointerRepr w | Just Refl <- testEquality (bvWidth bv) w -> return (LLVMPointer blk bv)
          _ -> mismatch

  Float  ->
    case tpr of
      FloatRepr SingleFloatRepr -> iFloatLitRational sym SingleFloatRepr 0
      _ -> mismatch

  Double ->
    case tpr of
      FloatRepr DoubleFloatRepr -> iFloatLitRational sym DoubleFloatRepr 0
      _ -> mismatch

  X86_FP80 ->
    case tpr of
      FloatRepr X86_80FloatRepr -> iFloatLitRational sym X86_80FloatRepr 0
      _ -> mismatch

  Array n tp' ->
    case tpr of
      VectorRepr tpr' ->
        do v <- unpackZero sym tp' tpr'
           return $ V.replicate (fromIntegral n) v
      _ -> mismatch

  Struct flds ->
    case tpr of
      StructRepr fldCtx | V.length flds == Ctx.sizeInt (Ctx.size fldCtx) ->
        Ctx.traverseWithIndex
          (\i tpr' -> RV <$> unpackZero sym (flds V.! (Ctx.indexVal i) ^. fieldVal) tpr')
          fldCtx

      _ -> mismatch


storageTypeMismatch ::
  String ->
  StorageType ->
  TypeRepr tp ->
  IO a
storageTypeMismatch nm tp tpr =
  panic nm
  [ "Storage type mismatch in " ++ nm
  , "  Storage type: " ++ show tp
  , "  Crucible type: " ++ show tpr
  ]

-- | Unpack an 'LLVMVal' to produce a 'RegValue'.
unpackMemValue ::
  (HasCallStack, IsSymInterface sym) =>
  sym ->
  TypeRepr tp ->
  LLVMVal sym ->
  IO (RegValue sym tp)

unpackMemValue sym tpr (LLVMValZero tp)  = unpackZero sym tp tpr

unpackMemValue _sym (LLVMPointerRepr w) (LLVMValInt blk bv)
  | Just Refl <- testEquality (bvWidth bv) w
  = return $ LLVMPointer blk bv

unpackMemValue _ (FloatRepr SingleFloatRepr) (LLVMValFloat SingleSize x) = return x
unpackMemValue _ (FloatRepr DoubleFloatRepr) (LLVMValFloat DoubleSize x) = return x
unpackMemValue _ (FloatRepr X86_80FloatRepr) (LLVMValFloat X86_FP80Size x) = return x

unpackMemValue sym (StructRepr ctx) (LLVMValStruct xs)
  | V.length xs == Ctx.sizeInt (Ctx.size ctx)
  = Ctx.traverseWithIndex
       (\i tpr -> RV <$> unpackMemValue sym tpr (xs V.! Ctx.indexVal i ^. _2))
       ctx

unpackMemValue sym (VectorRepr tpr) (LLVMValArray _tp xs)
  = traverse (unpackMemValue sym tpr) xs

-- LLVM string literals are syntactic shorthand for [<N> x i8] arrays, so we
-- defer to the LLVMValArray case above.
unpackMemValue sym tpr@(VectorRepr _) (LLVMValString str)
  = do explodedVal <- explodeStringValue sym str
       unpackMemValue sym tpr explodedVal

unpackMemValue _sym ctp@(BVRepr _) lval@(LLVMValInt _ _) =
    panic "MemModel.unpackMemValue"
      [ "Cannot unpack an integer LLVM value to a crucible bitvector type"
      , "*** Crucible type: " ++ show ctp
      , "*** LLVM value: " ++ show lval
      ]

unpackMemValue _ tpr v@(LLVMValUndef _) =
  panic "MemModel.unpackMemValue"
    [ "Cannot unpack an `undef` value"
    , "*** Crucible type: " ++ show tpr
    , "*** Undef value: " ++ show v
    ]

unpackMemValue _ tpr v =
  panic "MemModel.unpackMemValue"
    [ "Crucible type mismatch when unpacking LLVM value"
    , "*** Crucible type: " ++ show tpr
    , "*** LLVM value: " ++ show v
    ]


-- | Pack a 'RegValue' into an 'LLVMVal'. The LLVM storage type and
-- the Crucible type must be compatible.
packMemValue ::
  IsSymInterface sym =>
  sym ->
  StorageType {- ^ LLVM storage type -} ->
  TypeRepr tp {- ^ Crucible type     -} ->
  RegValue sym tp ->
  IO (LLVMVal sym)

packMemValue _ (StorageType Float _) (FloatRepr SingleFloatRepr) x =
       return $ LLVMValFloat SingleSize x

packMemValue _ (StorageType Double _) (FloatRepr DoubleFloatRepr) x =
       return $ LLVMValFloat DoubleSize x

packMemValue _ (StorageType X86_FP80 _) (FloatRepr X86_80FloatRepr) x =
       return $ LLVMValFloat X86_FP80Size x

packMemValue sym (StorageType (Bitvector bytes) _) (BVRepr w) bv
  | bitsToBytes (natValue w) == bytes =
      do blk0 <- natLit sym 0
         return $ LLVMValInt blk0 bv

packMemValue _sym (StorageType (Bitvector bytes) _) (LLVMPointerRepr w) (LLVMPointer blk off)
  | bitsToBytes (natValue w) == bytes =
       return $ LLVMValInt blk off

packMemValue sym (StorageType (Array sz tp) _) (VectorRepr tpr) vec
  | V.length vec == fromIntegral sz = do
       vec' <- traverse (packMemValue sym tp tpr) vec
       return $ LLVMValArray tp vec'

packMemValue sym (StorageType (Struct fls) _) (StructRepr ctx) xs = do
  fls' <- V.generateM (V.length fls) $ \i -> do
              let fl = fls V.! i
              case Ctx.intIndex i (Ctx.size ctx) of
                Just (Some idx) -> do
                  let tpr = ctx Ctx.! idx
                  let RV val = xs Ctx.! idx
                  val' <- packMemValue sym (fl^.fieldVal) tpr val
                  return (fl, val')
                _ -> panic "MemModel.packMemValue"
                      [ "Mismatch between LLVM and Crucible types"
                      , "*** Filed out of bounds: " ++ show i
                      ]
  return $ LLVMValStruct fls'

packMemValue _ stTy crTy _ =
  panic "MemModel.packMemValue"
    [ "Type mismatch when storing value."
    , "*** Expected storable type: " ++ show stTy
    , "*** Given crucible type: " ++ show crTy
    ]


----------------------------------------------------------------------
-- Disjointness
--

-- | Assert that two memory regions are disjoint.
-- Two memory regions are disjoint if any of the following are true:
--
--   1. Their block pointers are different
--   2. Their blocks are the same, but /dest+dlen/ <= /src/
--   3. Their blocks are the same, but /src+slen/ <= /dest/
assertDisjointRegions ::
  (1 <= w, HasPtrWidth wptr, IsSymBackend sym bak, Partial.HasLLVMAnn sym) =>
  bak ->
  MemoryOp sym wptr ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1 -} ->
  SymBV sym w      {- ^ length of region 1  -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2 -} ->
  SymBV sym w      {- ^ length of region 2  -} ->
  IO ()
assertDisjointRegions bak mop w dest dlen src slen = do
  let sym = backendGetSym bak
  c <- buildDisjointRegionsAssertion sym w dest dlen src slen
  c' <- Partial.annotateME sym mop OverlappingRegions c
  assert bak c' (AssertFailureSimError "Memory regions not disjoint" "")

buildDisjointRegionsAssertion ::
  (1 <= w, HasPtrWidth wptr, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1 -} ->
  SymBV sym w      {- ^ length of region 1  -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2 -} ->
  SymBV sym w      {- ^ length of region 2  -} ->
  IO (Pred sym)
buildDisjointRegionsAssertion sym w dest dlen src slen = do
  let LLVMPointer _dblk doff = dest
  let LLVMPointer _sblk soff = src

  dend <- bvAdd sym doff =<< sextendBVTo sym w PtrWidth dlen
  send <- bvAdd sym soff =<< sextendBVTo sym w PtrWidth slen

  diffBlk   <- notPred sym =<< ptrSameAlloc sym dest src
  destfirst <- bvSle sym dend soff
  srcfirst  <- bvSle sym send doff

  orPred sym diffBlk =<< orPred sym destfirst srcfirst

-- | Build the condition that two memory regions are disjoint, using
-- subtraction and comparison to zero instead of direct comparison (that is,
-- 0 <= y - x instead of x <= y). This enables semiring and abstract domain
-- simplifications. The result if false if any offset is not positive when
-- interpreted as signed bitvector.
buildDisjointRegionsAssertionWithSub ::
  (HasPtrWidth wptr, IsSymInterface sym) =>
  sym ->
  LLVMPtr sym wptr {- ^ pointer to region 1 -} ->
  SymBV sym wptr   {- ^ length of region 1  -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2 -} ->
  SymBV sym wptr   {- ^ length of region 2  -} ->
  IO (Pred sym)
buildDisjointRegionsAssertionWithSub sym dest dlen src slen = do
  let LLVMPointer _dblk doff = dest
  let LLVMPointer _sblk soff = src

  dend <- bvAdd sym doff dlen
  send <- bvAdd sym soff slen

  zero_bv <- bvZero sym PtrWidth

  diffBlk <- notPred sym =<< ptrSameAlloc sym dest src

  allPos <- andAllOf sym folded =<< mapM (bvSle sym zero_bv) [doff, dend, soff, send]
  destfirst <- bvSle sym zero_bv =<< bvSub sym soff dend
  srcfirst <- bvSle sym zero_bv =<< bvSub sym doff send

  orPred sym diffBlk =<< andPred sym allPos =<< orPred sym destfirst srcfirst

----------------------------------------------------------------------
-- constToLLVMVal
--

-- | This is used (by saw-script) to initialize globals.
--
-- In this translation, we lose the distinction between pointers and ints.
--
-- This is parameterized (hence, \"P\") over a function for looking up the
-- pointer values of global symbols. This parameter is used by @populateGlobal@
-- to recursively populate globals that may reference one another.
constToLLVMValP :: forall wptr sym io.
  ( MonadIO io
  , MonadFail io
  , HasPtrWidth wptr
  , IsSymInterface sym
  , HasCallStack
  ) => sym                                 -- ^ The symbolic backend
    -> (L.Symbol -> io (LLVMPtr sym wptr)) -- ^ How to look up global symbols
    -> LLVMConst                           -- ^ Constant expression to translate
    -> io (LLVMVal sym)

-- See comment on @LLVMVal@ on why we use a literal 0.
constToLLVMValP sym _ (IntConst w i) = liftIO $
  LLVMValInt <$> natLit sym 0 <*> bvLit sym w i

constToLLVMValP sym _ (FloatConst f) = liftIO $
  LLVMValFloat SingleSize <$> iFloatLitSingle sym f

constToLLVMValP sym _ (DoubleConst d) = liftIO $
  LLVMValFloat DoubleSize <$> iFloatLitDouble sym d

constToLLVMValP sym _ (LongDoubleConst (L.FP80_LongDouble e s)) = liftIO $
  LLVMValFloat X86_FP80Size <$> iFloatLitLongDouble sym (X86_80Val e s)

constToLLVMValP _ _ (StringConst bs) =
  pure (LLVMValString bs)

constToLLVMValP sym look (ArrayConst memty xs) =
  LLVMValArray <$> liftIO (toStorableType memty)
               <*> (V.fromList <$> traverse (constToLLVMValP sym look) xs)

-- Same as the array case
constToLLVMValP sym look (VectorConst memty xs) =
  LLVMValArray <$> liftIO (toStorableType memty)
               <*> (V.fromList <$> traverse (constToLLVMValP sym look) xs)

constToLLVMValP sym look (StructConst sInfo xs) =
  LLVMValStruct <$>
    V.zipWithM (\x y -> (,) <$> liftIO (fiToFT x) <*> constToLLVMValP sym look y)
               (siFields sInfo)
               (V.fromList xs)

-- SymbolConsts are offsets from global pointers. We translate them into the
-- pointer they represent.
constToLLVMValP sym look (SymbolConst symb i) = do
  -- Pointer to the global "symb"
  ptr <- look symb
  -- Offset to be added, as a bitvector
  ibv <- liftIO $ bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth i)

  -- blk is the allocation number that this global is stored in.
  -- In contrast to the case for @IntConst@ above, it is non-zero.
  let (blk, offset) = llvmPointerView ptr
  LLVMValInt blk <$> liftIO (bvAdd sym offset ibv)

constToLLVMValP _sym _look (ZeroConst memty) = liftIO $
  LLVMValZero <$> toStorableType memty
constToLLVMValP _sym _look (UndefConst memty) = liftIO $
  LLVMValUndef <$> toStorableType memty


-- | Translate a constant into an LLVM runtime value. Assumes all necessary
-- globals have already been populated into the @'MemImpl'@.
constToLLVMVal :: forall wptr sym bak io.
  ( MonadIO io
  , MonadFail io
  , HasPtrWidth wptr
  , IsSymBackend sym bak
  , HasCallStack
  ) => bak               -- ^ The symbolic backend
    -> MemImpl sym       -- ^ The current memory state, for looking up globals
    -> LLVMConst         -- ^ Constant expression to translate
    -> io (LLVMVal sym)  -- ^ Runtime representation of the constant expression

-- See comment on @LLVMVal@ on why we use a literal 0.
constToLLVMVal bak mem =
  constToLLVMValP (backendGetSym bak)
     (\symb -> liftIO $ doResolveGlobal bak mem symb)

-- TODO are these types just identical? Maybe we should combine them.
fiToFT :: (HasPtrWidth wptr, MonadFail m) => FieldInfo -> m (Field StorageType)
fiToFT fi = fmap (\t -> mkField (fiOffset fi) t (fiPadding fi))
                 (toStorableType $ fiType fi)

----------------------------------------------------------------------
-- Globals
--

-- | Look up a 'Symbol' in the global map of the given 'MemImpl'.
-- Panic if the symbol is not present in the global map.
doResolveGlobal ::
  (IsSymBackend sym bak, HasPtrWidth wptr, HasCallStack) =>
  bak ->
  MemImpl sym ->
  L.Symbol {- ^ name of global -} ->
  IO (LLVMPtr sym wptr)
doResolveGlobal bak mem symbol@(L.Symbol name) =
  let lookedUp = Map.lookup symbol (memImplGlobalMap mem)
      msg1 = "Global allocation has incorrect width"
      msg1Details = mconcat [ "Allocation associated with global symbol \""
                            , name
                            , "\" is not a pointer of the correct width"
                            ]
      msg2 = "Global symbol not allocated"
      msg2Details = mconcat [ "Global symbol \""
                            , name
                            , "\" has no associated allocation"
                            ]
  in case lookedUp of
       Just (SomePointer ptr) | PtrWidth <- ptrWidth ptr -> return ptr
       _ -> addFailedAssertion bak $
         if isJust lookedUp
         then AssertFailureSimError msg1 msg1Details
         else AssertFailureSimError msg2 msg2Details

-- | Add an entry to the global map of the given 'MemImpl'.
--
-- This takes a list of symbols because there may be aliases to a global.
registerGlobal ::
  (IsExprBuilder sym, 1 <= wptr) =>
  MemImpl sym -> [L.Symbol] -> LLVMPtr sym wptr -> MemImpl sym
registerGlobal (MemImpl blockSource gMap sMap hMap mem) symbols ptr =
  MemImpl blockSource gMap' sMap' hMap mem
  where
    gMap' = foldr (\s m -> Map.insert s (SomePointer ptr) m) gMap symbols
    sMap' =
      fromMaybe sMap $
      do symbol <- listToMaybe symbols
         n <- asNat (llvmPointerBlock ptr)
         z <- asBV (llvmPointerOffset ptr)
         guard (BV.asUnsigned z == 0)
         Just (Map.insert n symbol sMap)

-- | Allocate memory for each global, and register all the resulting
-- pointers in the global map.
allocGlobals ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  [(L.Global, [L.Symbol], Bytes, Alignment)] ->
  MemImpl sym ->
  IO (MemImpl sym)
allocGlobals bak gs mem = foldM (allocGlobal bak) mem gs

allocGlobal ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, Partial.HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  (L.Global, [L.Symbol], Bytes, Alignment) ->
  IO (MemImpl sym)
allocGlobal bak mem (g, aliases, sz, alignment) = do
  let sym = backendGetSym bak
  let symbol@(L.Symbol sym_str) = L.globalSym g
  let displayName = "[global variable  ] " ++ sym_str
  let mut = if L.gaConstant (L.globalAttrs g) then G.Immutable else G.Mutable
  sz' <- bvLit sym PtrWidth (bytesToBV PtrWidth sz)
  -- TODO: Aliases are not propagated to doMalloc for error messages
  (ptr, mem') <- doMalloc bak G.GlobalAlloc mut displayName mem sz' alignment
  return (registerGlobal mem' (symbol:aliases) ptr)


concSomePointer ::
  IsSymInterface sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  SomePointer sym -> IO (SomePointer sym)
concSomePointer sym conc (SomePointer ptr) =
  SomePointer <$> ML.concPtr sym conc ptr

concMemImpl ::
  IsSymInterface sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemImpl sym -> IO (MemImpl sym)
concMemImpl sym conc mem =
  do heap' <- ML.concMem sym conc (memImplHeap mem)
     gm'   <- traverse (concSomePointer sym conc) (memImplGlobalMap mem)
     pure mem{ memImplHeap = heap', memImplGlobalMap = gm' }
