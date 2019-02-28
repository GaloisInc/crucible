--------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyDataDecls #-}

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
  , ppMem
  , doDumpMem
  , BlockSource(..)
  , nextBlock

    -- * Pointers
  , LLVMPointerType
  , pattern LLVMPointerRepr
  , pattern PtrRepr
  , LLVMPtr
  , pattern LLVMPointer
  , llvmPointerView
  , ptrWidth
  , G.ppPtr
  , llvmPointer_bv
  , projectLLVM_bv

    -- * Memory operations
  , doMalloc
  , doMallocUnbounded
  , G.AllocType(..)
  , G.Mutability(..)
  , doMallocHandle
  , doLookupHandle
  , doMemcpy
  , doMemset
  , doCalloc
  , doFree
  , doLoad
  , doStore
  , doArrayStore
  , doArrayStoreUnbounded
  , doArrayConstStore
  , loadString
  , loadMaybeString
  , uncheckedMemcpy

    -- * \"Raw\" operations with LLVMVal
  , LLVMVal(..)
  , FloatSize(..)
  , unpackMemValue
  , packMemValue
  , loadRaw
  , loadRawWithCondition
  , storeRaw
  , storeConstRaw
  , mallocRaw
  , mallocConstRaw
  , constToLLVMVal
  , constToLLVMValP
  , ptrMessage

    -- * Storage types
  , StorageType
  , storageTypeF
  , StorageTypeF(..)
  , Field
  , storageTypeSize
  , fieldVal
  , fieldPad
  , bitvectorType
  , arrayType
  , mkStructType
  , floatType
  , doubleType
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
  , muxLLVMPtr

    -- * Disjointness
  , assertDisjointRegions
  , assertDisjointRegions'
  , buildDisjointRegionsAssertion

    -- * Globals
  , GlobalSymbol(..)
  , globalAliases
  , doResolveGlobal
  , registerGlobal
  , allocGlobals
  , allocGlobal
  , functionAliases

    -- * Misc
  , llvmStatementExec
  , SomeFnHandle(..)

    -- * PtrWidth (re-exports)
  , HasPtrWidth
  , pattern PtrWidth
  , withPtrWidth
  ) where

import           Prelude hiding (seq)

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.Trans (lift)
import           Control.Monad.Trans.State
import           Data.Dynamic
import           Data.IORef
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe)
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Word
import           GHC.TypeNats
import           System.IO (Handle, hPutStrLn)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import           What4.Interface
import           What4.InterpretedFloatingPoint
import           What4.Partial

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
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.MemModel.Type
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Value
import qualified Lang.Crucible.LLVM.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.Translation.Constant
import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.Panic (panic)

import           GHC.Stack

----------------------------------------------------------------------
-- The MemImpl type
--

-- | A pointer with an existentially-quantified width
data SomePointer sym = forall w. SomePointer !(LLVMPtr sym w)

newtype BlockSource = BlockSource (IORef Integer)
type GlobalMap sym = Map L.Symbol (SomePointer sym)

nextBlock :: BlockSource -> IO Integer
nextBlock (BlockSource ref) =
  atomicModifyIORef' ref (\n -> (n+1, n))

-- | The implementation of an LLVM memory, containing an
-- allocation-block source, global map, handle map, and heap.
data MemImpl sym =
  MemImpl
  { memImplBlockSource :: BlockSource
  , memImplGlobalMap   :: GlobalMap sym
  , memImplHandleMap   :: Map Integer Dynamic
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
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty (G.emptyMem endianness)

ppMem :: IsExprBuilder sym => MemImpl sym -> Doc
ppMem mem = G.ppMem (memImplHeap mem)

-- | Pretty print a memory state to the given handle.
doDumpMem :: IsExprBuilder sym => Handle -> MemImpl sym -> IO ()
doDumpMem h mem = do
  hPutStrLn h (show (ppMem mem))

----------------------------------------------------------------------
-- Memory operations
--


-- | Assert that some undefined behavior doesn't occur when performing memory
-- model operations
assertUndefined :: (IsSymInterface sym, HasPtrWidth wptr)
                => sym
                -> Pred sym
                -> Maybe UB.Config      -- ^ defaults to 'strictConfig'
                -> UB.UndefinedBehavior -- ^ The undesirable behavior
                -> [String]             -- ^ Additional error message lines
                -> IO ()
assertUndefined sym p (UB.defaultStrict -> ubConfig) ub extraErrMsg =
  when (UB.getConfig ubConfig ub) $ assert sym p $
    (AssertFailureSimError $ UB.pp ub ++ unlines extraErrMsg)

instance IntrinsicClass sym "LLVM_memory" where
  type Intrinsic sym "LLVM_memory" ctx = MemImpl sym

  -- NB: Here we are assuming the global maps of both memories are identical.
  -- This should be the case as memories are only supposed to allocate globals at
  -- startup, not during program execution.  We could check that the maps match,
  -- but that would be expensive...
  muxIntrinsic _sym _iTypes _nm _ p mem1 mem2 =
     do let MemImpl blockSource gMap1 hMap1 m1 = mem1
        let MemImpl _blockSource _gMap2 hMap2 m2 = mem2
        --putStrLn "MEM MERGE"
        return $ MemImpl blockSource gMap1
                   (Map.union hMap1 hMap2)
                   (G.mergeMem p m1 m2)

  pushBranchIntrinsic _sym _iTypes _nm _ctx mem =
     do let MemImpl nxt gMap hMap m = mem
        --putStrLn "MEM PUSH BRANCH"
        return $ MemImpl nxt gMap hMap $ G.branchMem m

  abortBranchIntrinsic _sym _iTypes _nm _ctx mem =
     do let MemImpl nxt gMap hMap m = mem
        --putStrLn "MEM ABORT BRANCH"
        return $ MemImpl nxt gMap hMap $ G.branchAbortMem m

-- | Top-level evaluation function for LLVM extension statements.
--   LLVM extension statements are used to implement the memory model operations.
llvmStatementExec :: HasPtrWidth (ArchWidth arch) => EvalStmtFunc p sym (LLVM arch)
llvmStatementExec stmt cst =
  let sym = cst^.stateSymInterface
   in stateSolverProof cst (runStateT (evalStmt sym stmt) cst)

type EvalM p sym ext rtp blocks ret args a =
  StateT (CrucibleState p sym ext rtp blocks ret args) IO a

-- | Actual workhorse function for evaluating LLVM extension statements.
--   The semantics are explicitly organized as a state transformer monad
--   that modifes the global state of the simulator; this captures the
--   memory accessing effects of these statements.
evalStmt :: forall p sym ext rtp blocks ret args wptr tp.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  LLVMStmt wptr (RegEntry sym) tp ->
  EvalM p sym ext rtp blocks ret args (RegValue sym tp)
evalStmt sym = eval
 where
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

  failedAssert :: String -> EvalM p sym ext rtp blocks ret args a
  failedAssert = lift . addFailedAssertion sym . AssertFailureSimError

  eval :: LLVMStmt wptr (RegEntry sym) tp ->
          EvalM p sym ext rtp blocks ret args (RegValue sym tp)
  eval (LLVM_PushFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.pushStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_PopFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.popStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_Alloca _w mvar (regValue -> sz) alignment loc) =
     do mem <- getMem mvar
        blkNum <- liftIO $ nextBlock (memImplBlockSource mem)
        blk <- liftIO $ natLit sym (fromIntegral blkNum)
        z <- liftIO $ bvLit sym PtrWidth 0

        let heap' = G.allocMem G.StackAlloc (fromInteger blkNum) (Just sz) alignment G.Mutable (show loc) (memImplHeap mem)
        let ptr = LLVMPointer blk z

        setMem mvar mem{ memImplHeap = heap' }
        return ptr

  eval (LLVM_Load mvar (regValue -> ptr) tpr valType alignment) =
     do mem <- getMem mvar
        liftIO $ doLoad sym mem ptr valType tpr alignment

  eval (LLVM_MemClear mvar (regValue -> ptr) bytes) =
    do mem <- getMem mvar
       z   <- liftIO $ bvLit sym knownNat 0
       len <- liftIO $ bvLit sym PtrWidth (bytesToInteger bytes)
       mem' <- liftIO $ doMemset sym Nothing PtrWidth mem ptr z len
       setMem mvar mem'

  eval (LLVM_Store mvar (regValue -> ptr) tpr valType alignment (regValue -> val)) =
     do mem <- getMem mvar
        mem' <- liftIO $ doStore sym mem ptr tpr valType alignment val
        setMem mvar mem'

  eval (LLVM_LoadHandle mvar (regValue -> ptr) args ret) =
     do mem <- getMem mvar
        mhandle <- liftIO $ doLookupHandle sym mem ptr
        case mhandle of
           Left doc -> failedAssert (show doc)
           Right (SomeFnHandle h)
             | Just Refl <- testEquality handleTp expectedTp -> return (HandleFnVal h)
             | otherwise -> failedAssert
                 $ unlines ["Expected function handle of type " ++
                                                              show expectedTp
                           ,"but found handle of type " ++ show handleTp]
            where handleTp   = FunctionHandleRepr (handleArgTypes h) (handleReturnType h)
                  expectedTp = FunctionHandleRepr args ret

  eval (LLVM_ResolveGlobal _w mvar (GlobalSymbol symbol)) =
     do mem <- getMem mvar
        liftIO $ doResolveGlobal sym mem symbol

  eval (LLVM_PtrEq mvar (regValue -> x) (regValue -> y)) = do
     mem <- getMem mvar
     liftIO $ do
        let allocs_doc = G.ppAllocs (G.memAllocs (memImplHeap mem))
        let x_doc = G.ppPtr x
        let y_doc = G.ppPtr y

        v1 <- isValidPointer sym x mem
        v2 <- isValidPointer sym y mem
        v3 <- G.notAliasable sym x y (memImplHeap mem)

        assertUndefined sym v1 Nothing UB.CompareInvalidPointer $
          ["Equality (==) comparison on pointer", show x_doc, show allocs_doc]
        assertUndefined sym v2 Nothing UB.CompareInvalidPointer $
          ["Equality (==) comparison on pointer", show y_doc, show allocs_doc]
        assert sym v3
           (AssertFailureSimError $ unlines ["Const pointers compared for equality:", show x_doc, show y_doc, show allocs_doc])

        ptrEq sym PtrWidth x y

  eval (LLVM_PtrLe mvar (regValue -> x) (regValue -> y)) = do
    mem <- getMem mvar
    liftIO $ do
       let x_doc = G.ppPtr x
           y_doc = G.ppPtr y
       v1 <- isValidPointer sym x mem
       v2 <- isValidPointer sym y mem
       assertUndefined sym v1 Nothing UB.CompareInvalidPointer $
         ["Ordering (<=) comparison on pointer", show x_doc]
       assertUndefined sym v2 Nothing UB.CompareInvalidPointer $
         ["Ordering (<=) comparison on pointer", show y_doc]

       (le, valid) <- ptrLe sym PtrWidth x y

       assertUndefined sym valid Nothing UB.CompareDifferentAllocs $
         ["Pointer 1: " ++ show x_doc, "Pointer 2:" ++ show y_doc]

       pure le

  eval (LLVM_PtrAddOffset _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrAddOffset sym Nothing mem x y

  eval (LLVM_PtrSubtract _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrSubtract sym Nothing mem x y

mkMemVar :: HandleAllocator s
         -> ST s (GlobalVar Mem)
mkMemVar halloc = freshGlobalVar halloc "llvm_memory" knownRepr


-- | For now, the core message should be on the first line, with details
-- on further lines. Later we should make it more structured.
ptrMessage ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  String ->
  LLVMPtr sym wptr {- ^ pointer involved in message -} ->
  StorageType      {- ^ type of value pointed to    -} ->
  String
ptrMessage msg ptr ty =
  unlines [ msg
          , "  address " ++ show (G.ppPtr ptr)
          , "  at type " ++ show (G.ppType ty)
          ]

-- | Load a 'RegValue' from memory. Both the 'StorageType' and 'TypeRepr'
-- arguments should be computed from a single 'MemType' using
-- 'toStorableType' and 'Lang.Crucible.LLVM.Translation.Types.llvmTypeAsRepr'
-- respectively.
--
-- Precondition: the pointer is valid and aligned, and the loaded value is defined.
doLoad ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ pointer to load from      -} ->
  StorageType      {- ^ type of value to load     -} ->
  TypeRepr tp      {- ^ crucible type of the result -} ->
  Alignment        {- ^ assumed pointer alignment -} ->
  IO (RegValue sym tp)
doLoad sym mem ptr valType tpr alignment = do
  --putStrLn "MEM LOAD"
  unpackMemValue sym tpr =<< loadRaw sym mem ptr valType alignment

-- | Store a 'RegValue' in memory. Both the 'StorageType' and 'TypeRepr'
-- arguments should be computed from a single 'MemType' using
-- 'toStorableType' and 'Lang.Crucible.LLVM.Translation.Types.llvmTypeAsRepr'
-- respectively.
--
-- Precondition: the pointer is valid and points to a mutable memory region.
doStore ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ pointer to store into  -} ->
  TypeRepr tp ->
  StorageType      {- ^ type of value to store -} ->
  Alignment ->
  RegValue sym tp  {- ^ value to store         -} ->
  IO (MemImpl sym)
doStore sym mem ptr tpr valType alignment val = do
    --putStrLn "MEM STORE"
    val' <- packMemValue sym valType tpr val
    storeRaw sym mem ptr valType alignment val'

data SomeFnHandle where
  SomeFnHandle :: FnHandle args ret -> SomeFnHandle


sextendBVTo :: (1 <= w, IsSymInterface sym)
            => sym
            -> NatRepr w
            -> NatRepr w'
            -> SymExpr sym (BaseBVType w)
            -> IO (SymExpr sym (BaseBVType w'))
sextendBVTo sym w w' x
  | Just Refl <- testEquality w w' = return x
  | Just LeqProof <- testLeq (incNat w) w' = bvSext sym w' x
  | otherwise =
    addFailedAssertion sym
        $ AssertFailureSimError
        $ unwords ["cannot extend bitvector of width", show (natValue w)
                                                     , "to", show (natValue w') ]


-- | Allocate and zero a memory region with /size * number/ bytes.
--
-- Precondition: the multiplication /size * number/ does not overflow.
doCalloc ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  SymBV sym wptr {- ^ size   -} ->
  SymBV sym wptr {- ^ number -} ->
  Alignment {- ^ Minimum alignment of the resulting allocation -} ->
  IO (LLVMPtr sym wptr, MemImpl sym)
doCalloc sym mem sz num alignment = do
  (ov, sz') <- unsignedWideMultiplyBV sym sz num
  ov_iszero <- notPred sym =<< bvIsNonzero sym ov
  assert sym ov_iszero
     (AssertFailureSimError "Multiplication overflow in calloc()")

  z <- bvLit sym knownNat 0
  (ptr, mem') <- doMalloc sym G.HeapAlloc G.Mutable "<calloc>" mem sz' alignment
  mem'' <- doMemset sym Nothing PtrWidth mem' ptr z sz'
  return (ptr, mem'')

-- | Allocate a memory region.
doMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> SymBV sym wptr {- ^ allocation size -}
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMalloc sym allocType mut loc mem sz alignment = doMallocSize (Just sz) sym allocType mut loc mem alignment

-- | Allocate a memory region of unbounded size.
doMallocUnbounded
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMallocUnbounded = doMallocSize Nothing

doMallocSize
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => Maybe (SymBV sym wptr) {- ^ allocation size -}
  -> sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMallocSize sz sym allocType mut loc mem alignment = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk    <- natLit sym (fromIntegral blkNum)
  z      <- bvLit sym PtrWidth 0
  let heap' = G.allocMem allocType (fromInteger blkNum) sz alignment mut loc (memImplHeap mem)
  let ptr   = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap' })

-- | Allocate a memory region for the given handle.
doMallocHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> a {- ^ handle -}
  -> IO (LLVMPtr sym wptr, MemImpl sym)
doMallocHandle sym allocType loc mem x = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym PtrWidth 0

  let heap' = G.allocMem allocType (fromInteger blkNum) (Just z) noAlignment G.Immutable loc (memImplHeap mem)
  let hMap' = Map.insert blkNum (toDyn x) (memImplHandleMap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap', memImplHandleMap = hMap' })

-- | Look up the handle associated with the given pointer, if any.
doLookupHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (Either Doc a)
doLookupHandle _sym mem ptr = do
  let LLVMPointer blk _ = ptr
  case asNat blk of
    Nothing -> return (Left (text "Cannot resolve a symbolic pointer to a function handle:" <$$> ppPtr ptr))
    Just i
      | i == 0 -> return (Left (text "Cannot treat raw bitvector as function pointer:" <$$> ppPtr ptr))
      | otherwise ->
          case Map.lookup (toInteger i) (memImplHandleMap mem) of
            Nothing -> return (Left ("Pointer is not a function pointer:" <$$> ppPtr ptr))
            Just x ->
              case fromDynamic x of
                Nothing -> return (Left ("Function handle did not have expected type:" <$$> ppPtr ptr))
                Just a  -> return (Right a)

-- | Free the memory region pointed to by the given pointer.
--
-- Precondition: the pointer either points to the beginning of an allocated
-- region, or is null. Freeing a null pointer has no effect.
doFree
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> Maybe UB.Config  {- ^ defaults to 'strictConfig' -}
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> IO (MemImpl sym)
doFree sym ubConfig mem ptr = do
  let LLVMPointer blk _ = ptr
  (heap', p1, p2) <- G.freeMem sym PtrWidth ptr (memImplHeap mem)

  -- If this pointer is a handle pointer, remove the associated data
  let hMap' =
       case asNat blk of
         Just i  -> Map.delete (toInteger i) (memImplHandleMap mem)
         Nothing -> memImplHandleMap mem


  -- NB: free is defined and has no effect if passed a null pointer
  isNull <- ptrIsNull sym PtrWidth ptr
  p1'    <- orPred sym p1 isNull
  p2'    <- orPred sym p2 isNull

  let errMsg1 = "Pointer didn't point to base of allocation. "
  let errMsg2 = "Invalid free (double free or invalid pointer): address " ++ show (G.ppPtr ptr)
  assertUndefined sym p1' ubConfig UB.FreeInvalidPointer [errMsg1, show (G.ppPtr ptr)]
  assert sym p2' (AssertFailureSimError errMsg2)

  return mem{ memImplHeap = heap', memImplHandleMap = hMap' }

-- | Fill a memory range with copies of the specified byte.
--
-- Precondition: the memory range falls within a valid allocated region.
doMemset ::
  (1 <= w, IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  Maybe UB.Config  {- ^ defaults to 'strictConfig' -} ->
  NatRepr w ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  SymBV sym 8      {- ^ fill byte   -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doMemset sym ubConfig w mem dest val len = do
  len' <- sextendBVTo sym w PtrWidth len

  (heap', p) <- G.setMem sym PtrWidth dest val len' (memImplHeap mem)

  assertUndefined sym p ubConfig UB.MemsetInvalidRegion
    -- [show (G.ppPtr dest), "Requested size: " ++ show len']
    [show (G.ppPtr dest)]

  return mem{ memImplHeap = heap' }

-- | Store an array in memory.
--
-- Precondition: the pointer is valid and points to a mutable memory region.
doArrayStore
  :: (IsSymInterface sym, HasPtrWidth w)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> SymBV sym w {- ^ array length -}
  -> IO (MemImpl sym)
doArrayStore sym mem ptr alignment arr len = doArrayStoreSize (Just len) sym mem ptr alignment arr

-- | Store an array of unbounded length in memory.
--
-- Precondition: the pointer is valid and points to a mutable memory region.
doArrayStoreUnbounded
  :: (IsSymInterface sym, HasPtrWidth w)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> IO (MemImpl sym)
doArrayStoreUnbounded = doArrayStoreSize Nothing


doArrayStoreSize
  :: (IsSymInterface sym, HasPtrWidth w)
  => Maybe (SymBV sym w) {- ^ possibly-unbounded array length -}
  -> sym
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> IO (MemImpl sym)
doArrayStoreSize len sym mem ptr alignment arr = do
  (heap', p1, p2) <-
    G.writeArrayMem sym PtrWidth ptr alignment arr len (memImplHeap mem)
  let errMsg1 = "Array store to unallocated or immutable region: "
  let errMsg2 = "Array store to improperly aligned region: "
  assert sym p1 $ AssertFailureSimError $ errMsg1 ++ show (G.ppPtr ptr)
  assert sym p2 $ AssertFailureSimError $ errMsg2 ++ show (G.ppPtr ptr)
  return mem { memImplHeap = heap' }

-- | Store an array in memory.
--
-- Precondition: the pointer is valid and points to a mutable or immutable memory region.
-- Therefore it can be used to initialize read-only memory regions.
doArrayConstStore
  :: (IsSymInterface sym, HasPtrWidth w)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym w {- ^ destination  -}
  -> Alignment
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ array value  -}
  -> SymBV sym w {- ^ array length -}
  -> IO (MemImpl sym)
doArrayConstStore sym mem ptr alignment arr len = do
  (heap', p1, p2) <-
    G.writeArrayConstMem sym PtrWidth ptr alignment arr (Just len) (memImplHeap mem)
  let errMsg1 = "Array store to unallocated region: "
  let errMsg2 = "Array store to improperly aligned region: "
  assert sym p1 $ AssertFailureSimError $ errMsg1 ++ show (G.ppPtr ptr)
  assert sym p2 $ AssertFailureSimError $ errMsg2 ++ show (G.ppPtr ptr)
  return mem { memImplHeap = heap' }

-- | Copy memory from source to destination.
--
-- Precondition: the source and destination pointers fall within valid allocated
-- regions.
doMemcpy ::
  (1 <= w, IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  NatRepr w ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ destination -} ->
  LLVMPtr sym wptr {- ^ source      -} ->
  SymBV sym w      {- ^ length      -} ->
  IO (MemImpl sym)
doMemcpy sym w mem dest src len = do
  len' <- sextendBVTo sym w PtrWidth len

  (heap', p1, p2) <- G.copyMem sym PtrWidth dest src len' (memImplHeap mem)

  let errMsg1 = "Source region was not allocated:" ++ show (G.ppPtr src)
  let errMsg2 = "Dest region was not allocated, or not mutable:" ++ show (G.ppPtr dest)
  assert sym p1 (AssertFailureSimError errMsg1)
  assert sym p2 (AssertFailureSimError errMsg2)

  return mem{ memImplHeap = heap' }


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
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  Maybe UB.Config  {- ^ defaults to 'strictConfig' -} ->
  MemImpl sym ->
  LLVMPtr sym wptr ->
  LLVMPtr sym wptr ->
  IO (SymBV sym wptr)
doPtrSubtract sym ubConfig _m x y = do
  (diff, valid) <- ptrDiff sym PtrWidth x y
  assertUndefined sym valid ubConfig UB.PtrSubDifferentAllocs $
     map unwords [ ["Pointer 1:", show (G.ppPtr x)]
                 , ["Pointer 2:", show (G.ppPtr y)]
                 ]
  pure diff

-- | Add an offset to a pointer and asserts that the result is a valid pointer.
doPtrAddOffset ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  Maybe UB.Config  {- ^ defaults to 'strictConfig' -} ->
  MemImpl sym ->
  LLVMPtr sym wptr {- ^ base pointer -} ->
  SymBV sym wptr   {- ^ offset       -} ->
  IO (LLVMPtr sym wptr)
doPtrAddOffset sym ubConfig m x off = do
  x' <- ptrAdd sym PtrWidth x off
  v  <- isValidPointer sym x' m

  assertUndefined sym v ubConfig UB.PtrAddOffsetOutOfBounds $
     map unwords [ ["Pointer:", show (G.ppPtr x)]
                 , ["Offset:", show (printSymExpr off)]
                 ]

  return x'

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

-- | Load a null-terminated string from the memory.
--
-- The pointer to read from must be concrete and nonnull.  Moreover,
-- we require all the characters in the string to be concrete.
-- Otherwise it is very difficult to tell when the string has
-- terminated.  If a maximum number of characters is provided, no more
-- than that number of charcters will be read.  In either case,
-- `loadString` will stop reading if it encounters a null-terminator.
loadString ::
  forall sym wptr.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  Maybe Int        {- ^ maximum characters to read -} ->
  IO [Word8]
loadString sym mem = go id
 where
  go :: ([Word8] -> [Word8]) -> LLVMPtr sym wptr -> Maybe Int -> IO [Word8]
  go f _ (Just 0) = return $ f []
  go f p maxChars = do
     v <- doLoad sym mem p (bitvectorType 1) (LLVMPointerRepr (knownNat :: NatRepr 8)) noAlignment
     x <- projectLLVM_bv sym v
     case asUnsignedBV x of
       Just 0 -> return $ f []
       Just c -> do
           let c' :: Word8 = toEnum $ fromInteger c
           p' <- doPtrAddOffset sym Nothing mem p =<< bvLit sym PtrWidth 1
           go (f . (c':)) p' (fmap (\n -> n - 1) maxChars)
       Nothing ->
         addFailedAssertion sym
            $ Unsupported "Symbolic value encountered when loading a string"

-- | Like 'loadString', except the pointer to load may be null.  If
--   the pointer is null, we return Nothing.  Otherwise we load
--   the string as with 'loadString' and return it.
loadMaybeString ::
  forall sym wptr.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym      {- ^ memory to read from        -} ->
  LLVMPtr sym wptr {- ^ pointer to string value    -} ->
  Maybe Int        {- ^ maximum characters to read -} ->
  IO (Maybe [Word8])
loadMaybeString sym mem ptr n = do
  isnull <- ptrIsNull sym PtrWidth ptr
  case asConstantPred isnull of
    Nothing    -> addFailedAssertion sym
                    $ Unsupported "Symbolic pointer encountered when loading a string"
    Just True  -> return Nothing
    Just False -> Just <$> loadString sym mem ptr n



toStorableType :: (Monad m, HasPtrWidth wptr)
               => MemType
               -> m StorageType
toStorableType mt =
  case mt of
    IntType n -> return $ bitvectorType (bitsToBytes n)
    PtrType _ -> return $ bitvectorType (bitsToBytes (natValue PtrWidth))
    FloatType -> return $ floatType
    DoubleType -> return $ doubleType
    X86_FP80Type -> return $ x86_fp80Type
    ArrayType n x -> arrayType (fromIntegral n) <$> toStorableType x
    VecType n x -> arrayType (fromIntegral n) <$> toStorableType x
    MetadataType -> fail "toStorableType: Cannot store metadata values"
    StructType si -> mkStructType <$> traverse transField (siFields si)
      where transField :: Monad m => FieldInfo -> m (StorageType, Bytes)
            transField fi = do
               t <- toStorableType $ fiType fi
               return (t, fiPadding fi)

----------------------------------------------------------------------
-- "Raw" operations
--

-- | Load an LLVM value from memory. Asserts that the pointer is valid and the
-- result value is not undefined.
loadRaw :: (IsSymInterface sym, HasPtrWidth wptr)
        => sym
        -> MemImpl sym
        -> LLVMPtr sym wptr
        -> StorageType
        -> Alignment
        -> IO (LLVMVal sym)
loadRaw sym mem ptr valType alignment =
  do res <- loadRawWithCondition sym mem ptr valType alignment
     case res of
       Right (v, p1, p2, p3) -> v <$ (sequence $
         [ assert sym p1 (AssertFailureSimError "Read from unallocated memory")
         , assert sym p2 (AssertFailureSimError "Read from unaligned memory")
         , assert sym p3 (AssertFailureSimError "Invalid memory load")
         ])
       Left e        -> addFailedAssertion sym (AssertFailureSimError e)


-- | Load an LLVM value from memory. This version of 'loadRaw'
-- returns the side-conditions explicitly so that they can
-- be conditionally asserted.
--
-- The side conditions assert that:
-- 1. The region of memory is allocated
-- 2. The region of memory has the proper alignment
-- 3. A /lot/ of other things, see the source of "MemModel.Generic"
loadRawWithCondition ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym                  ->
  MemImpl sym          {- ^ LLVM heap       -} ->
  LLVMPtr sym wptr     {- ^ pointer         -} ->
  StorageType          {- ^ pointed-to type -} ->
  Alignment            {- ^ alignment of this load -} ->
  IO (Either String (LLVMVal sym, Pred sym, Pred sym, Pred sym))
loadRawWithCondition sym mem ptr valType alignment =
  do (v, isAllocated, isAligned) <-
       G.readMem sym PtrWidth ptr valType alignment (memImplHeap mem)
     let errMsg = ptrMessage "Invalid memory load." ptr valType
     case v of
       Unassigned -> return (Left errMsg)
       PE p' v' -> return (Right (v', isAllocated, isAligned, p'))

-- | Store an LLVM value in memory. Asserts that the pointer is valid and points
-- to a mutable memory region.
storeRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> StorageType      {- ^ type of value to store -}
  -> Alignment
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeRaw sym mem ptr valType alignment val = do
    (heap', p1, p2) <- G.writeMem sym PtrWidth ptr valType alignment val (memImplHeap mem)
    let errMsg1 = "Invalid memory store: the region wasn't allocated, or wasn't mutable"
    let errMsg2 = "Invalid memory store: the region's alignment wasn't correct"
    assert sym p1 (AssertFailureSimError $ ptrMessage errMsg1 ptr valType)
    assert sym p2 (AssertFailureSimError $ ptrMessage errMsg2 ptr valType)
    return mem{ memImplHeap = heap' }

-- | Store an LLVM value in memory. The pointed-to memory region may
-- be either mutable or immutable; thus 'storeConstRaw' can be used to
-- initialize read-only memory regions.
storeConstRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> StorageType      {- ^ type of value to store -}
  -> Alignment
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeConstRaw sym mem ptr valType alignment val = do
    (heap', p1, p2) <- G.writeConstMem sym PtrWidth ptr valType alignment val (memImplHeap mem)
    let errMsg1 = "Invalid memory store: the region wasn't allocated"
    let errMsg2 = "Invalid memory store: the region's alignment wasn't correct"
    assert sym p1 (AssertFailureSimError $ ptrMessage errMsg1 ptr valType)
    assert sym p2 (AssertFailureSimError $ ptrMessage errMsg2 ptr valType)
    return mem{ memImplHeap = heap' }

-- | Allocate a memory region on the heap, with no source location info.
mallocRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymBV sym wptr {- ^ size in bytes -}
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocRaw sym mem sz alignment =
  doMalloc sym G.HeapAlloc G.Mutable "<malloc>" mem sz alignment

-- | Allocate a read-only memory region on the heap, with no source location info.
mallocConstRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymBV sym wptr
  -> Alignment
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocConstRaw sym mem sz alignment =
  doMalloc sym G.HeapAlloc G.Immutable "<malloc>" mem sz alignment

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
      FloatRepr SingleFloatRepr -> iFloatLit sym SingleFloatRepr 0
      _ -> mismatch

  Double ->
    case tpr of
      FloatRepr DoubleFloatRepr -> iFloatLit sym DoubleFloatRepr 0
      _ -> mismatch

  X86_FP80 ->
    case tpr of
      FloatRepr X86_80FloatRepr -> iFloatLit sym X86_80FloatRepr 0
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
assertDisjointRegions' ::
  (1 <= w, HasPtrWidth wptr, IsSymInterface sym) =>
  String {- ^ label used for error message -} ->
  sym ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1 -} ->
  SymBV sym w      {- ^ length of region 1  -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2 -} ->
  SymBV sym w      {- ^ length of region 2  -} ->
  IO ()
assertDisjointRegions' lbl sym w dest dlen src slen = do
  c <- buildDisjointRegionsAssertion sym w dest dlen src slen
  assert sym c
     (AssertFailureSimError ("Memory regions not disjoint in " ++ lbl))


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
  let LLVMPointer dblk doff = dest
  let LLVMPointer sblk soff = src

  dend <- bvAdd sym doff =<< sextendBVTo sym w PtrWidth dlen
  send <- bvAdd sym soff =<< sextendBVTo sym w PtrWidth slen

  diffBlk   <- notPred sym =<< natEq sym dblk sblk
  destfirst <- bvSle sym dend soff
  srcfirst  <- bvSle sym send doff

  orPred sym diffBlk =<< orPred sym destfirst srcfirst


-- | Simpler interface to 'assertDisjointRegions'' where the lengths
-- of the two regions are equal as used by the @memcpy@ operation.
assertDisjointRegions ::
  (1 <= w, HasPtrWidth wptr, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym wptr {- ^ pointer to region 1       -} ->
  LLVMPtr sym wptr {- ^ pointer to region 2       -} ->
  SymBV sym w      {- ^ length of regions 1 and 2 -} ->
  IO ()
assertDisjointRegions sym w dest src len =
  assertDisjointRegions' "memcpy" sym w dest len src len

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
  , HasPtrWidth wptr
  , IsSymInterface sym
  ) => sym                                 -- ^ The symbolic backend
    -> (L.Symbol -> io (LLVMPtr sym wptr)) -- ^ How to look up global symbols
    -> LLVMConst                           -- ^ Constant expression to translate
    -> io (LLVMVal sym)

-- See comment on @LLVMVal@ on why we use a literal 0.
constToLLVMValP sym _ (IntConst w i) = liftIO $
  LLVMValInt <$> natLit sym 0 <*> (bvLit sym w i)

constToLLVMValP sym _ (FloatConst f) = liftIO $
  LLVMValFloat SingleSize <$> iFloatLitSingle sym f

constToLLVMValP sym _ (DoubleConst d) = liftIO $
  LLVMValFloat DoubleSize <$> iFloatLitDouble sym d

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
  ptr <- look symb                       -- Pointer to the global "symb"
  ibv <- liftIO $ bvLit sym ?ptrWidth i  -- Offset to be added, as a bitvector

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
constToLLVMVal :: forall wptr sym io.
  ( MonadIO io
  , HasPtrWidth wptr
  , IsSymInterface sym
  ) => sym               -- ^ The symbolic backend
    -> MemImpl sym       -- ^ The current memory state, for looking up globals
    -> LLVMConst         -- ^ Constant expression to translate
    -> io (LLVMVal sym)  -- ^ Runtime representation of the constant expression

-- See comment on @LLVMVal@ on why we use a literal 0.
constToLLVMVal sym mem =
  constToLLVMValP sym (\symb -> liftIO $ doResolveGlobal sym mem symb)

-- TODO are these types just identical? Maybe we should combine them.
fiToFT :: (HasPtrWidth wptr, Monad m) => FieldInfo -> m (Field StorageType)
fiToFT fi = fmap (\t -> mkField (fiOffset fi) t (fiPadding fi))
                 (toStorableType $ fiType fi)

----------------------------------------------------------------------
-- Globals
--

-- | Reverse a set of alias/aliasee relationships
--
-- Given a list of values @l : List A@ and a function @aliasOf : A -> A@,
-- compute a map @Map A (Set A)@ which records the set of things that are
-- transitive aliases of a given @a : A@.
--
-- The keys in the resulting map should be only terminals, e.g. those @a@
-- which aren't aliases of another @a'@ in @l@.
--
-- Outline:
-- * Initialize the empty map @M : Map A (Set A)@
-- * Initialize an auxilary map @N : Map A A@ which records the final aliasee
--   of each key (the last one in the chain of aliases).
-- * For each @a : A@ in l,
--   1. If @aliasOf a@ is in @N@ as @aliasee@,
--       a. insert @aliasee@ at key @a@ in @N@ (memoize the result)
--       b. insert @a@ into the set at key @aliasee@ in @M@ (record the result)
--       c. recurse on @s@ minus @aliasee@ and @a@.
--   2. If @aliasOf a@ is in @s@, recurse on @l ++ [a]@
--   3. Otherwise,
--       a. insert @a@ at key @a@ in @N@ (memoize the result)
--       b. return the map as-is
--
-- For the sake of practical concerns, the implementation uses \"labels\" for
-- comparison and @aliasOf@, and uses sequences rather than lists.
reverseAliases :: (Ord a, Ord l)
               => (a -> l)         -- ^ \"Label of\"
               -> (a -> Maybe l)   -- ^ \"Alias of\"
               -> Seq a
               -> Map a (Set a)
reverseAliases lab aliasOf_ seq =
   evalState (go Map.empty seq) (Map.empty :: Map l a)

  where go map_ Seq.Empty      = pure map_
        go map_ (a Seq.:<| as) =
          case aliasOf_ a of
            Nothing ->
              do -- Don't overwrite it if it's already in the map
                 modify (Map.insert (lab a) a)
                 go (Map.insertWith (\_ old -> old) a Set.empty map_) as
            Just l ->
              do st <- get
                 case Map.lookup l st of
                   Just aliasee ->
                     modify (Map.insert l aliasee) >>                              -- 1a
                     go (mapSetInsert aliasee a map_)                              -- 1b
                        (Seq.filter (\b -> lab b /= lab aliasee && lab b /= l) as) -- 1c
                   Nothing      ->
                     if isJust (List.find ((l ==) . lab) as)
                     then go map_ (as <> Seq.singleton a)                          -- 2
                     else modify (Map.insert (lab a) a) >>                         -- 3a
                          pure map_                                                -- 3b
                 where mapSetInsert k v m  = Map.update (pure . Set.insert v) k m

-- | This is one step closer to the application of 'reverseAliases':
-- There are two \"sorts\" of objects:
-- Objects in sort @a@ are never aliases (think global variables).
-- Objects in sort @b@ are usually aliases, to things of either sort
-- (think aliases to global variables).
reverseAliasesTwoSorted :: (Ord a, Ord b, Ord l)
                        => (a -> l)       -- ^ \"Label of\" for type @a@
                        -> (b -> l)       -- ^ \"Label of\" for type @b@
                        -> (b -> Maybe l) -- ^ \"Alias of\"
                        -> Seq a
                        -> Seq b
                        -> Map a (Set b)
reverseAliasesTwoSorted laba labb aliasOf_ seqa seqb =
  Map.fromList . mapMaybe go . Map.toList $
    reverseAliases (either laba labb)
                   (either (const Nothing) aliasOf_)
                   (fmap Left seqa <> fmap Right seqb)
  where -- Drop the b's which have been added as keys and
        go (Right _, _) = Nothing
        -- Call "error" if an a has been tagged as an alias
        go (Left k, s) = Just (k, Set.map errLeft s)
        -- TODO: Should this throw an exception?
        errLeft (Left _)  = error "Internal error: unexpected Left value"
        errLeft (Right v) = v

-- | What does this alias point to?
aliasOf :: (?lc :: TypeContext, HasPtrWidth wptr)
        => L.GlobalAlias
        -> Maybe L.Symbol
aliasOf alias =
  case L.aliasTarget alias of
    L.ValSymbol    symb      -> Just symb
    L.ValConstExpr constExpr ->
      case transConstantExpr constExpr of
        Right (SymbolConst symb 0) -> Just symb
        _ -> Nothing
    -- All other things silently get dropped; it's invalid LLVM code to not have
    -- a symbol or constexpr.
    _ -> Nothing

-- | Get all the aliases that alias (transitively) to a certain global.
globalAliases :: (?lc :: TypeContext, HasPtrWidth wptr)
              => L.Module
              -> Map L.Global (Set L.GlobalAlias)
globalAliases mod_ =
  reverseAliasesTwoSorted L.globalSym L.aliasName aliasOf
    (Seq.fromList (L.modGlobals mod_)) (Seq.fromList (L.modAliases mod_))

-- | Get all the aliases that alias (transitively) to a certain function.
functionAliases :: (?lc :: TypeContext, HasPtrWidth wptr)
                => L.Module
                -> Map L.Define (Set L.GlobalAlias)
functionAliases mod_ =
  reverseAliasesTwoSorted L.defName L.aliasName aliasOf
    (Seq.fromList (L.modDefines mod_)) (Seq.fromList (L.modAliases mod_))

-- | Look up a 'Symbol' in the global map of the given 'MemImpl'.
-- Panic if the symbol is not present in the global map.
doResolveGlobal ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  MemImpl sym ->
  L.Symbol {- ^ name of global -} ->
  IO (LLVMPtr sym wptr)
doResolveGlobal _sym mem symbol =
  let lookedUp = Map.lookup symbol (memImplGlobalMap mem)
  in case lookedUp of
       Just (SomePointer ptr) | PtrWidth <- ptrWidth ptr -> return ptr
       _ -> panic "MemModel.doResolveGlobal" $
               (if isJust lookedUp
               then "Symbol was not a pointer of the correct width."
               else "Unable to resolve global symbol.") :
               [ "*** Name: " ++ show symbol ]

-- | Add an entry to the global map of the given 'MemImpl'.
--
-- This takes a list of symbols because there may be aliases to a global.
registerGlobal :: MemImpl sym -> [L.Symbol] -> LLVMPtr sym wptr -> MemImpl sym
registerGlobal (MemImpl blockSource gMap hMap mem) symbols ptr =
  let gMap' = foldr (\s m -> Map.insert s (SomePointer ptr) m) gMap symbols
  in MemImpl blockSource gMap' hMap mem

-- | Allocate memory for each global, and register all the resulting
-- pointers in the global map.
allocGlobals :: (IsSymInterface sym, HasPtrWidth wptr)
             => sym
             -> [(L.Global, [L.Symbol], Bytes, Alignment)]
             -> MemImpl sym
             -> IO (MemImpl sym)
allocGlobals sym gs mem = foldM (allocGlobal sym) mem gs

allocGlobal :: (IsSymInterface sym, HasPtrWidth wptr)
            => sym
            -> MemImpl sym
            -> (L.Global, [L.Symbol], Bytes, Alignment)
            -> IO (MemImpl sym)
allocGlobal sym mem (g, aliases, sz, alignment) = do
  let symbol@(L.Symbol sym_str) = L.globalSym g
  let mut = if L.gaConstant (L.globalAttrs g) then G.Immutable else G.Mutable
  sz' <- bvLit sym PtrWidth (bytesToInteger sz)
  -- TODO: Aliases are not propagated to doMalloc for error messages
  (ptr, mem') <- doMalloc sym G.GlobalAlloc mut sym_str mem sz' alignment
  return (registerGlobal mem' (symbol:aliases) ptr)
