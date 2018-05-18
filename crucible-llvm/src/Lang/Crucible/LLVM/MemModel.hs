------------------------------------------------------------------------
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE EmptyDataDecls #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel
  ( LLVMPointerType
  , pattern LLVMPointerRepr
  , pattern PtrWidth
  , ptrWidth
  , Mem
  , memRepr
  , MemImpl
  , emptyMem
  , mkMemVar
  , GlobalSymbol(..)
  , llvmStatementExec
  , allocGlobals
  , registerGlobal
  , assertDisjointRegions
  , assertDisjointRegions'
  , buildDisjointRegionsAssertion
  , doMemcpy
  , doMemset
  , doMalloc
  , doMallocHandle
  , doLookupHandle
  , doCalloc
  , doFree
  , doLoad
  , doStore
  , doPtrAddOffset
  , doPtrSubtract
  , doDumpMem
  , doResolveGlobal
  , loadString
  , loadMaybeString
  , SomeFnHandle(..)
  , G.ppPtr
  , ppMem
  , isValidPointer
  , memEndian

  -- * Direct API to LLVMVal
  , LLVMVal(..)
  , LLVMPtr
  , coerceAny
  , unpackMemValue
  , packMemValue
  , loadRaw
  , loadRawWithCondition
  , storeRaw
  , storeConstRaw
  , mallocRaw
  , mallocConstRaw
  ) where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.Trans.State
import           Data.Dynamic
import           Data.List hiding (group)
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Word
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           GHC.TypeLits

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import           What4.ProgramLoc
import           What4.Interface
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
import qualified Lang.Crucible.LLVM.Bytes as G
import qualified Lang.Crucible.LLVM.MemModel.Type as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.Types

import GHC.Stack

--import Debug.Trace as Debug

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
  let sym = stateSymInterface cst
   in stateSolverProof cst (runStateT (evalStmt sym stmt) cst)

-- | Actual workhorse function for evaluating LLVM extension statements.
--   The semantics are explicitly organized as a state transformer monad
--   that modifes the global state of the simulator; this captures the
--   memory accessing effects of these statements.
evalStmt :: forall p sym ext rtp blocks ret args wptr tp.
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym ->
  LLVMStmt wptr (RegEntry sym) tp ->
  StateT (CrucibleState p sym ext rtp blocks ret args) IO (RegValue sym tp)
evalStmt sym = eval
 where
  getMem :: GlobalVar Mem -> StateT (CrucibleState p sym ext rtp blocks ret args) IO (RegValue sym Mem)
  getMem mvar =
    do gs <- use (stateTree.actFrame.gpGlobals)
       case lookupGlobal mvar gs of
         Just mem -> return mem
         Nothing  -> fail ("Global heap value not initialized!: " ++ show mvar)

  setMem :: GlobalVar Mem -> RegValue sym Mem -> StateT (CrucibleState p sym ext rtp blocks ret args) IO ()
  setMem mvar mem = stateTree.actFrame.gpGlobals %= insertGlobal mvar mem

  eval :: LLVMStmt wptr (RegEntry sym) tp -> StateT (CrucibleState p sym ext rtp blocks ret args) IO (RegValue sym tp)
  eval (LLVM_PushFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.pushStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_PopFrame mvar) =
     do mem <- getMem mvar
        let heap' = G.popStackFrameMem (memImplHeap mem)
        setMem mvar mem{ memImplHeap = heap' }

  eval (LLVM_Alloca _w mvar (regValue -> sz) loc) =
     do mem <- getMem mvar
        blkNum <- liftIO $ nextBlock (memImplBlockSource mem)
        blk <- liftIO $ natLit sym (fromIntegral blkNum)
        z <- liftIO $ bvLit sym PtrWidth 0

        let heap' = G.allocMem G.StackAlloc (fromInteger blkNum) sz G.Mutable (show loc) (memImplHeap mem)
        let ptr = LLVMPointer blk z

        setMem mvar mem{ memImplHeap = heap' }
        return ptr

  eval (LLVM_Load mvar (regValue -> ptr) tpr valType alignment) =
     do mem <- getMem mvar
        liftIO $ (coerceAny sym tpr =<< doLoad sym mem ptr valType alignment)

  eval (LLVM_Store mvar (regValue -> ptr) tpr valType _alignment (regValue -> val)) =
     do mem <- getMem mvar
        mem' <- liftIO $ doStore sym mem ptr tpr valType val
        setMem mvar mem'

  eval (LLVM_LoadHandle mvar (regValue -> ptr) args ret) =
     do mem <- getMem mvar
        mhandle <- liftIO $ doLookupHandle sym mem ptr
        case mhandle of
           Nothing -> fail "LoadHandle: not a valid function pointer"
           Just (SomeFnHandle h)
             | Just Refl <- testEquality handleTp expectedTp -> return (HandleFnVal h)
             | otherwise ->
                 fail $ unlines ["Expected function handle of type " ++ show expectedTp
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
        assert sym v1
           (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show x_doc, show allocs_doc])
        assert sym v2
           (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show y_doc, show allocs_doc])
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
       assert sym v1
          (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show x_doc])
       assert sym v2
          (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show y_doc])
       ptrLe sym PtrWidth x y

  eval (LLVM_PtrAddOffset _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrAddOffset sym mem x y

  eval (LLVM_PtrSubtract _w mvar (regValue -> x) (regValue -> y)) =
    do mem <- getMem mvar
       liftIO $ doPtrSubtract sym mem x y

mkMemVar :: HandleAllocator s
         -> ST s (GlobalVar Mem)
mkMemVar halloc = freshGlobalVar halloc "llvm_memory" knownRepr

newtype BlockSource = BlockSource (IORef Integer)

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

-- | Produce a fresh empty memory.
--   NB, we start counting allocation blocks at '1'.
--   Block number 0 is reserved for representing raw bitvectors.
emptyMem :: EndianForm -> IO (MemImpl sym)
emptyMem endianness = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty (G.emptyMem endianness)

data SomePointer sym = forall w. SomePointer !(RegValue sym (LLVMPointerType w))
type GlobalMap sym = Map L.Symbol (SomePointer sym)

-- | Allocate memory for each global, and register all the resulting
-- pointers in the global map.
allocGlobals :: (IsSymInterface sym, HasPtrWidth wptr)
             => sym
             -> [(L.Symbol, G.Size)]
             -> MemImpl sym
             -> IO (MemImpl sym)
allocGlobals sym gs mem = foldM (allocGlobal sym) mem gs

allocGlobal :: (IsSymInterface sym, HasPtrWidth wptr)
            => sym
            -> MemImpl sym
            -> (L.Symbol, G.Size)
            -> IO (MemImpl sym)
allocGlobal sym mem (symbol@(L.Symbol sym_str), sz) = do
  sz' <- bvLit sym PtrWidth (G.bytesToInteger sz)
  (ptr, mem') <- doMalloc sym G.GlobalAlloc G.Mutable sym_str mem sz' -- TODO
  return (registerGlobal mem' symbol ptr)

-- | Add an entry to the global map of the given 'MemImpl'.
registerGlobal :: MemImpl sym
               -> L.Symbol
               -> RegValue sym (LLVMPointerType wptr)
               -> MemImpl sym
registerGlobal (MemImpl blockSource gMap hMap mem) symbol ptr =
  let gMap' = Map.insert symbol (SomePointer ptr) gMap
  in MemImpl blockSource gMap' hMap mem

asCrucibleType
  :: G.Type
  -> (forall tpr. TypeRepr tpr -> x)
  -> x
asCrucibleType (G.Type tf _) k =
  case tf of
    G.Bitvector sz ->
       case someNat (G.bytesToBits sz) of
         Just (Some w)
           | Just LeqProof <- isPosNat w -> k (LLVMPointerRepr w)
         _ -> error $ unwords ["invalid bitvector size", show sz]
    G.Float  -> k RealValRepr
    G.Double -> k RealValRepr
    G.Array _n t -> asCrucibleType t $ \tpr -> k (VectorRepr tpr)
    G.Struct xs -> go Ctx.empty (V.toList xs) $ \ctx -> k (StructRepr ctx)
      where go :: CtxRepr ctx0
               -> [G.Field G.Type]
               -> (forall ctx. CtxRepr ctx -> x)
               -> x
            go ctx [] k' = k' ctx
            go ctx (f:fs) k' =
                 asCrucibleType (f^.G.fieldVal) $ \tpr ->
                   go (ctx Ctx.:> tpr) fs k'

coerceAny :: (HasCallStack, IsSymInterface sym)
          => sym
          -> TypeRepr tpr
          -> AnyValue sym
          -> IO (RegValue sym tpr)
coerceAny sym tpr (AnyValue tpr' x)
  | Just Refl <- testEquality tpr tpr' = return x
  | otherwise =
      do loc <- getCurrentProgramLoc sym
         fail $ unlines [unwords ["coerceAny: cannot coerce from", show tpr', "to", show tpr]
                        , "in: " ++ show (plFunction loc)
                        , "at: " ++ show (plSourceLoc loc)
                        ]

unpackMemValue
   :: (HasCallStack, IsSymInterface sym)
   => sym
   -> LLVMVal sym
   -> IO (AnyValue sym)

-- If the block number is 0, we know this is a raw bitvector, and not an actual pointer.
unpackMemValue _sym (LLVMValInt blk bv)
  = return . AnyValue (LLVMPointerRepr (bvWidth bv)) $ LLVMPointer blk bv
unpackMemValue _ (LLVMValReal _ x) =
  return $ AnyValue RealValRepr x
unpackMemValue sym (LLVMValStruct xs) = do
  xs' <- traverse (unpackMemValue sym . snd) $ V.toList xs
  unpackStruct sym xs' Ctx.empty Ctx.empty $ \ctx fls -> return $ AnyValue (StructRepr ctx) $ fls
unpackMemValue sym (LLVMValArray tp xs) =
  asCrucibleType tp $ \tpr -> do
    xs' <- traverse (coerceAny sym tpr <=< unpackMemValue sym) xs
    return $ AnyValue (VectorRepr tpr) xs'

unpackStruct
   :: IsSymInterface sym
   => sym
   -> [AnyValue sym]
   -> CtxRepr ctx0
   -> Ctx.Assignment (RegValue' sym) ctx0
   -> (forall ctx. CtxRepr ctx -> Ctx.Assignment (RegValue' sym) ctx -> IO x)
   -> IO x
unpackStruct _ [] ctx fls k = k ctx fls
unpackStruct sym (v:vs) ctx fls k =
  case v of
    AnyValue tpr x ->
      unpackStruct sym vs (ctx Ctx.:> tpr) (fls Ctx.:> RV x) k


packMemValue
   :: IsSymInterface sym
   => sym
   -> G.Type
   -> TypeRepr tp
   -> RegValue sym tp
   -> IO (LLVMVal sym)
packMemValue _ (G.Type G.Float _) RealValRepr x =
       return $ LLVMValReal SingleSize x

packMemValue _ (G.Type G.Double _) RealValRepr x =
       return $ LLVMValReal DoubleSize x

packMemValue sym (G.Type (G.Bitvector bytes) _) (BVRepr w) bv
  | G.bytesToBits bytes == toInteger (natValue w) =
      do blk0 <- natLit sym 0
         return $ LLVMValInt blk0 bv

packMemValue _sym (G.Type (G.Bitvector bytes) _) (LLVMPointerRepr w) (LLVMPointer blk off)
  | G.bytesToBits bytes == toInteger (natValue w) =
       return $ LLVMValInt blk off

packMemValue sym (G.Type (G.Array sz tp) _) (VectorRepr tpr) vec
  | V.length vec == fromIntegral sz = do
       vec' <- traverse (packMemValue sym tp tpr) vec
       return $ LLVMValArray tp vec'

packMemValue sym (G.Type (G.Struct fls) _) (StructRepr ctx) xs = do
  fls' <- V.generateM (V.length fls) $ \i -> do
              let fl = fls V.! i
              case Ctx.intIndex i (Ctx.size ctx) of
                Just (Some idx) -> do
                  let tpr = ctx Ctx.! idx
                  let RV val = xs Ctx.! idx
                  val' <- packMemValue sym (fl^.G.fieldVal) tpr val
                  return (fl, val')
                _ -> fail "packMemValue: actual value has insufficent structure fields"
  return $ LLVMValStruct fls'

packMemValue _ stTy crTy _ =
  fail $ unlines [ "Type mismatch when storing value."
                 , "Expected storable type: " ++ show stTy
                 , "but got incompatible crucible type: " ++ show crTy
                 ]

doResolveGlobal
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> L.Symbol
  -> IO (RegValue sym (LLVMPointerType wptr))
doResolveGlobal _sym mem symbol =
  case Map.lookup symbol (memImplGlobalMap mem) of
    Just (SomePointer ptr) | PtrWidth <- ptrWidth ptr -> return ptr
    _ -> fail $ unwords ["Unable to resolve global symbol", show symbol]

ppMem :: IsExprBuilder sym => RegValue sym Mem -> Doc
ppMem mem = G.ppMem (memImplHeap mem)

-- | Pretty print a memory state to the given handle.
doDumpMem
  :: IsExprBuilder sym
  => Handle
  -> RegValue sym Mem
  -> IO ()
doDumpMem h mem = do
  hPutStrLn h (show (ppMem mem))

-- | Load an LLVM value from memory. Also assert that the pointer is
-- valid and the result value is not undefined.
loadRaw :: (IsSymInterface sym, HasPtrWidth wptr)
        => sym
        -> MemImpl sym
        -> LLVMPtr sym wptr
        -> G.Type
        -> IO (LLVMVal sym)
loadRaw sym mem ptr valType =
  do res <- loadRawWithCondition sym mem ptr valType
     case res of
       Right (p,r,v) -> v <$ assert sym p r
       Left e        -> fail e


-- | Load an LLVM value from memory. This version of 'loadRaw'
-- returns the side-conditions explicitly so that they can
-- be conditionally asserted.
loadRawWithCondition ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  sym                  ->
  MemImpl sym          {- ^ LLVM heap       -} ->
  LLVMPtr sym wptr     {- ^ pointer         -} ->
  G.Type               {- ^ pointed-to type -} ->
  IO (Either
        String
        (Pred sym, SimErrorReason, LLVMVal sym))
  -- ^ Either error message or
  -- (assertion, assertion failure description, dereferenced value)
loadRawWithCondition sym mem ptr valType =
  do v <- G.readMem sym PtrWidth ptr valType 0 (memImplHeap mem)
     let errMsg = "Invalid memory load: address " ++ show (G.ppPtr ptr) ++
                  " at type "                     ++ show (G.ppType valType)
     case v of
       Unassigned -> return (Left errMsg)
       PE p' v' -> return (Right (p', AssertFailureSimError errMsg, v'))

-- | Load a 'RegValue' from memory. Also assert that the pointer is
-- valid and aligned, and that the loaded value is defined.
doLoad :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem
  -> RegValue sym (LLVMPointerType wptr) {- ^ pointer to load from -}
  -> G.Type {- ^ type of value to load -}
  -> Alignment {- ^ assumed pointer alignment -}
  -> IO (RegValue sym AnyType)
doLoad sym mem ptr valType alignment = do
    --putStrLn "MEM LOAD"
    let errMsg = "Invalid memory load: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    v <- G.readMem sym PtrWidth ptr valType alignment (memImplHeap mem)
    case v of
      Unassigned ->
        fail errMsg
      PE p' v' -> do
        assert sym p' (AssertFailureSimError errMsg)
        unpackMemValue sym v'

-- | Store an LLVM value in memory. Also assert that the pointer is
-- valid and points to a mutable memory region.
storeRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> G.Type           {- ^ type of value to store -}
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeRaw sym mem ptr valType val = do
    (p, heap') <- G.writeMem sym PtrWidth ptr valType val (memImplHeap mem)
    let errMsg = "Invalid memory store: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    assert sym p (AssertFailureSimError errMsg)
    return mem{ memImplHeap = heap' }

-- | Store an LLVM value in memory. The pointed-to memory region may
-- be either mutable or immutable; thus 'storeConstRaw' can be used to
-- initialize read-only memory regions.
storeConstRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr {- ^ pointer to store into -}
  -> G.Type           {- ^ type of value to store -}
  -> LLVMVal sym      {- ^ value to store -}
  -> IO (MemImpl sym)
storeConstRaw sym mem ptr valType val = do
    (p, heap') <- G.writeConstMem sym PtrWidth ptr valType val (memImplHeap mem)
    let errMsg = "Invalid memory store: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    assert sym p (AssertFailureSimError errMsg)
    return mem{ memImplHeap = heap' }

-- | Store a 'RegValue' in memory. Also assert that the pointer is
-- valid and points to a mutable memory region.
doStore :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem
  -> RegValue sym (LLVMPointerType wptr) {- ^ pointer to store into -}
  -> TypeRepr tp
  -> G.Type                              {- ^ type of value to store -}
  -> RegValue sym tp                     {- ^ value to store -}
  -> IO (RegValue sym Mem)
doStore sym mem ptr tpr valType val = do
    --putStrLn "MEM STORE"
    val' <- packMemValue sym valType tpr val
    storeRaw sym mem ptr valType val'

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
  | otherwise = fail $ unwords ["cannot extend bitvector of width", show (natValue w)
                               , "to", show (natValue w')
                               ]

-- Two memory regions are disjoint if any of the following are true:
--   1) Their block pointers are different
--   2) Their blocks are the same, but dest+dlen <= src
--   3) Their blocks are the same, but src+slen <= dest
assertDisjointRegions'
  :: (1 <= w, HasPtrWidth wptr, IsSymInterface sym)
  => String -- ^ label used for error message
  -> sym
  -> NatRepr w
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType w)
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType w)
  -> IO ()
assertDisjointRegions' lbl sym w dest dlen src slen = do
  c <- buildDisjointRegionsAssertion sym w dest dlen src slen
  assert sym c
     (AssertFailureSimError ("Memory regions not disjoint in " ++ lbl))


buildDisjointRegionsAssertion
  :: (1 <= w, HasPtrWidth wptr, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType w)
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType w)
  -> IO (SymExpr sym BaseBoolType)
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
-- of the two regions are equal as used by the memcpy operation.
assertDisjointRegions
  :: (1 <= w, HasPtrWidth wptr, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType w)
  -> IO ()
assertDisjointRegions sym w dest src len =
  assertDisjointRegions' "memcpy" sym w dest len src len


-- | Allocate and zero a memory region with /size * number/ bytes.
-- Also assert that the multiplication does not overflow.
doCalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> RegValue sym (BVType wptr) {- ^ size -}
  -> RegValue sym (BVType wptr) {- ^ number -}
  -> IO (RegValue sym (LLVMPointerType wptr), MemImpl sym)
doCalloc sym mem sz num = do
  (ov, sz') <- unsignedWideMultiplyBV sym sz num
  ov_iszero <- notPred sym =<< bvIsNonzero sym ov
  assert sym ov_iszero
     (AssertFailureSimError "Multiplication overflow in calloc()")

  z <- bvLit sym knownNat 0
  (ptr, mem') <- doMalloc sym G.HeapAlloc G.Mutable "<calloc>" mem sz'
  mem'' <- doMemset sym PtrWidth mem' ptr z sz'
  return (ptr, mem'')

-- | Allocate a memory region.
doMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> G.Mutability {- ^ whether region is read-only -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> RegValue sym (BVType wptr) {- ^ allocation size -}
  -> IO (RegValue sym (LLVMPointerType wptr), MemImpl sym)
doMalloc sym allocType mut loc mem sz = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym PtrWidth 0
  let heap' = G.allocMem allocType (fromInteger blkNum) sz mut loc (memImplHeap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap' })

-- | Allocate a memory region on the heap, with no source location info.
mallocRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymExpr sym (BaseBVType wptr)
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocRaw sym mem sz =
  doMalloc sym G.HeapAlloc G.Mutable "<malloc>" mem sz

-- | Allocate a read-only memory region on the heap, with no source location info.
mallocConstRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymExpr sym (BaseBVType wptr)
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocConstRaw sym mem sz =
  doMalloc sym G.HeapAlloc G.Immutable "<malloc>" mem sz

-- | Allocate a memory region for the given handle.
doMallocHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType {- ^ stack, heap, or global -}
  -> String {- ^ source location for use in error messages -}
  -> MemImpl sym
  -> a {- ^ handle -}
  -> IO (RegValue sym (LLVMPointerType wptr), MemImpl sym)
doMallocHandle sym allocType loc mem x = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym PtrWidth 0

  let heap' = G.allocMem allocType (fromInteger blkNum) z G.Mutable loc (memImplHeap mem)
  let hMap' = Map.insert blkNum (toDyn x) (memImplHandleMap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap', memImplHandleMap = hMap' })

-- | Look up the handle associated with the given pointer, if any.
doLookupHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> RegValue sym (LLVMPointerType wptr)
  -> IO (Maybe a)
doLookupHandle _sym mem ptr = do
  let LLVMPointer blk _ = ptr
  case asNat blk of
    Just i | i /= 0 ->
      case Map.lookup (toInteger i) (memImplHandleMap mem) of
        Just x -> return $! fromDynamic x
        Nothing -> return Nothing
    _ -> return Nothing

-- | Free the memory region pointed to by the given pointer. Also
-- assert that the pointer either points to the beginning of an
-- allocated region, or is null. Freeing a null pointer has no effect.
doFree
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> RegValue sym (LLVMPointerType wptr)
  -> IO (MemImpl sym)
doFree sym mem ptr = do
  let LLVMPointer blk _ = ptr
  (c, heap') <- G.freeMem sym PtrWidth ptr (memImplHeap mem)

  -- If this pointer is a handle pointer, remove the associated data
  let hMap' =
       case asNat blk of
         Just i  -> Map.delete (toInteger i) (memImplHandleMap mem)
         Nothing -> memImplHandleMap mem

  let errMsg = "Invalid free (double free or invalid pointer): address " ++ show (G.ppPtr ptr)

  -- NB: free is defined and has no effect if passed a null pointer
  isNull <- ptrIsNull sym PtrWidth ptr
  c' <- orPred sym c isNull
  assert sym c' (AssertFailureSimError errMsg)
  return mem{ memImplHeap = heap', memImplHandleMap = hMap' }

doMemset
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> NatRepr w
  -> MemImpl sym
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType 8)
  -> RegValue sym (BVType w)
  -> IO (MemImpl sym)
doMemset sym _w mem dest val len = do
  --dest_doc <- ppPtr sym dest
  --val_doc <- printSymExpr sym val
  --len_doc <- printSymExpr sym len
  --putStrLn $ unwords ["doMemset:", show dest_doc, show val_doc, show len_doc]

  case asUnsignedBV len of
    Nothing -> do
      -- FIXME? can we lift this restriction?
      -- Perhaps should add a MemSet constructor
      -- to MemWrites and deal with things that way...
      fail "memset requires concrete length"
    Just sz -> do
      let tp   = G.arrayType (fromInteger sz) (G.bitvectorType 1)
      blk0 <- natLit sym 0
      let val' = LLVMValInt blk0 val
      let xs   = V.generate (fromInteger sz) (\_ -> val')
      let arr  = LLVMValArray (G.bitvectorType 1) xs
      (c, heap') <- G.writeMem sym PtrWidth dest tp arr (memImplHeap mem)
      assert sym c
         (AssertFailureSimError "Invalid region specified in memset")
      return mem{ memImplHeap = heap' }


doMemcpy
  :: (1 <= w, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> NatRepr w
  -> MemImpl sym
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (BVType w)
  -> IO (MemImpl sym)
doMemcpy sym w mem dest src len = do
  len' <- sextendBVTo sym w PtrWidth len

  (c, heap') <- G.copyMem sym PtrWidth dest src len' (memImplHeap mem)

  assert sym c
     (AssertFailureSimError "Invalid memory region in memcpy")

  return mem{ memImplHeap = heap' }


doPtrSubtract
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem
  -> RegValue sym (LLVMPointerType wptr)
  -> RegValue sym (LLVMPointerType wptr)
  -> IO (RegValue sym (BVType wptr))
doPtrSubtract sym _m x y =
  do ptrDiff sym PtrWidth x y

doPtrAddOffset
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem
  -> RegValue sym (LLVMPointerType wptr) {- ^ base pointer -}
  -> RegValue sym (BVType wptr)          {- ^ offset -}
  -> IO (RegValue sym (LLVMPointerType wptr))
doPtrAddOffset sym m x off = do
   x' <- ptrAdd sym PtrWidth x off
   v  <- isValidPointer sym x' m
   let x_doc = G.ppPtr x
   let off_doc = printSymExpr off
   assert sym v
       (AssertFailureSimError $ unlines ["Pointer arithmetic resulted in invalid pointer:", show x_doc, show off_doc])
   return x'

-- | This predicate tests if the pointer is a valid, live pointer
--   into the heap, OR is the distinguished NULL pointer.
isValidPointer :: (IsSymInterface sym, HasPtrWidth wptr)
               => sym
               -> RegValue sym (LLVMPointerType wptr)
               -> RegValue sym Mem
               -> IO (Pred sym)
isValidPointer sym p mem =
   do np <- ptrIsNull sym PtrWidth p
      case asConstantPred np of
        Just True  -> return np
        Just False -> G.isValidPointer sym PtrWidth p (memImplHeap mem)
        _ -> orPred sym np =<< G.isValidPointer sym PtrWidth p (memImplHeap mem)

instance IsExpr (SymExpr sym) => Show (LLVMVal sym) where
  show (LLVMValInt blk w)
    | Just 0 <- asNat blk = "<int" ++ show (bvWidth w) ++ ">"
    | otherwise = "<ptr " ++ show (bvWidth w) ++ ">"
  show (LLVMValReal SingleSize _) = "<float>"
  show (LLVMValReal DoubleSize _) = "<double>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]

-- | Load a null-terminated string from the memory.
--
-- The pointer to read from must be concrete and nonnull.  Moreover,
-- we require all the characters in the string to be concrete.
-- Otherwise it is very difficult to tell when the string has
-- terminated.  If a maximum number of characters is provided, no more
-- than that number of charcters will be read.  In either case,
-- `loadString` will stop reading if it encounters a null-terminator.
loadString :: forall sym wptr
   . (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem -- ^ memory to read from
  -> RegValue sym (LLVMPointerType wptr) -- ^ pointer to string value
  -> Maybe Int -- ^ maximum characters to read
  -> IO [Word8]
loadString sym mem = go id
 where
  go :: ([Word8] -> [Word8]) -> RegValue sym (LLVMPointerType wptr) -> Maybe Int -> IO [Word8]
  go f _ (Just 0) = return $ f []
  go f p maxChars = do
     v <- doLoad sym mem p (G.bitvectorType 1) 0 -- one byte, no alignment
     case v of
       AnyValue (LLVMPointerRepr w) x
         | Just Refl <- testEquality w (knownNat :: NatRepr 8) ->
            do x' <- projectLLVM_bv sym x
               case asUnsignedBV x' of
                 Just 0 -> return $ f []
                 Just c -> do
                     let c' :: Word8 = toEnum $ fromInteger c
                     p' <- doPtrAddOffset sym mem p =<< bvLit sym PtrWidth 1
                     go (f . (c':)) p' (fmap (\n -> n - 1) maxChars)
                 Nothing ->
                   fail "Symbolic value encountered when loading a string"
       _ -> fail "Invalid value encountered when loading a string"


-- | Like 'loadString', except the pointer to load may be null.  If
--   the pointer is null, we return Nothing.  Otherwise we load
--   the string as with 'loadString' and return it.
loadMaybeString :: forall sym wptr
   . (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem -- ^ memory to read from
  -> RegValue sym (LLVMPointerType wptr) -- ^ pointer to string value
  -> Maybe Int -- ^ maximum characters to read
  -> IO (Maybe [Word8])
loadMaybeString sym mem ptr n = do
  isnull <- ptrIsNull sym PtrWidth ptr
  case asConstantPred isnull of
    Nothing    -> fail "Symbolic pointer encountered when loading a string"
    Just True  -> return Nothing
    Just False -> Just <$> loadString sym mem ptr n
