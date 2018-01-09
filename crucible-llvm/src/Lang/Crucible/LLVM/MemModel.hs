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

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel
  ( LLVMPointerType
  , LLVMValTypeType
  , pattern LLVMPointerRepr
  , pattern PtrWidth
  , ptrWidth
  , Mem
  , memRepr
  , MemImpl
  , emptyMem
  , LLVMMemOps(..)
  , newMemOps
  , llvmMemIntrinsics
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

  -- * Direct API to LLVMVal
  , LLVMVal(..)
  , LLVMPtr
  , coerceAny
  , unpackMemValue
  , packMemValue
  , loadRaw
  , loadRawWithCondition
  , storeRaw
  , mallocRaw
  ) where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
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
import           Data.Parameterized.Context (pattern Empty, pattern (:>))
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L

import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
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
  muxIntrinsic _sym _nm _ p mem1 mem2 =
     do let MemImpl blockSource gMap1 hMap1 m1 = mem1
        let MemImpl _blockSource _gMap2 hMap2 m2 = mem2
        --putStrLn "MEM MERGE"
        return $ MemImpl blockSource gMap1
                   (Map.union hMap1 hMap2)
                   (G.mergeMem p m1 m2)

  pushBranchIntrinsic _sym _nm _ctx mem =
     do let MemImpl nxt gMap hMap m = mem
        --putStrLn "MEM PUSH BRANCH"
        return $ MemImpl nxt gMap hMap $ G.branchMem m

  abortBranchIntrinsic _sym _nm _ctx mem =
     do let MemImpl nxt gMap hMap m = mem
        --putStrLn "MEM ABORT BRANCH"
        return $ MemImpl nxt gMap hMap $ G.branchAbortMem m

-- | @'RegValue' sym 'LLVMValTypeType'@ is equivalent to 'G.Type'.
type LLVMValTypeType = ConcreteType G.Type

-- | @'RegValue' sym 'AlignmentType'@ is equivalent to 'Alignment'.
type AlignmentType = ConcreteType Alignment

data LLVMMemOps wptr
  = LLVMMemOps
  { llvmDataLayout :: DataLayout
  , llvmMemVar    :: GlobalVar Mem
  , llvmMemAlloca :: FnHandle (EmptyCtx ::> Mem ::> BVType wptr ::> StringType)
                              (StructType (EmptyCtx ::> Mem ::> LLVMPointerType wptr))
  , llvmMemPushFrame :: FnHandle (EmptyCtx ::> Mem) Mem
  , llvmMemPopFrame :: FnHandle (EmptyCtx ::> Mem) Mem
  , llvmMemLoad  :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMValTypeType ::> AlignmentType) AnyType
  , llvmMemStore :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMValTypeType ::> AnyType) Mem
  , llvmMemLoadHandle :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr) AnyType
  , llvmResolveGlobal :: FnHandle (EmptyCtx ::> Mem ::> ConcreteType GlobalSymbol) (LLVMPointerType wptr)
  , llvmPtrEq :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMPointerType wptr) BoolType
  , llvmPtrLe :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMPointerType wptr) BoolType
  , llvmPtrAddOffset :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> BVType wptr) (LLVMPointerType wptr)
  , llvmPtrSubtract :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMPointerType wptr) (BVType wptr)
  }

llvmStatementExec :: EvalStmtFunc p sym (LLVM wptr)
llvmStatementExec _cst _stmt =
  fail "LLVM Statement Exec: IMPLEMENT ME! (FIXME)"


data LLVMIntrinsicImpl p sym arch args ret =
  LLVMIntrinsicImpl
  { llvmIntrinsicName     :: FunctionName
  , llvmIntrinsicArgTypes :: CtxRepr args
  , llvmIntrinsicRetType  :: TypeRepr ret
  , llvmIntrinsicImpl     :: IntrinsicImpl p sym (LLVM arch) args ret
  }

useLLVMIntrinsic :: IsSymInterface sym
                 => FnHandle args ret
                 -> LLVMIntrinsicImpl p sym arch args ret
                 -> FnBinding p sym (LLVM arch)
useLLVMIntrinsic hdl impl = useIntrinsic hdl (llvmIntrinsicImpl impl)

mkLLVMHandle :: HandleAllocator s
             -> LLVMIntrinsicImpl p sym arch args ret
             -> ST s (FnHandle args ret)
mkLLVMHandle halloc impl =
  mkHandle' halloc
    (llvmIntrinsicName impl)
    (llvmIntrinsicArgTypes impl)
    (llvmIntrinsicRetType impl)


llvmMemIntrinsics :: (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch)
                  => LLVMMemOps wptr
                  -> [FnBinding p sym (LLVM arch)]
llvmMemIntrinsics memOps =
  [ useLLVMIntrinsic (llvmMemAlloca memOps)
                     memAlloca
  , useLLVMIntrinsic (llvmMemLoad memOps)
                     memLoad
  , useLLVMIntrinsic (llvmMemStore memOps)
                     memStore
  , useLLVMIntrinsic (llvmMemLoadHandle memOps)
                     memLoadHandle
  , useLLVMIntrinsic (llvmMemPushFrame memOps)
                     memPushFrame
  , useLLVMIntrinsic (llvmMemPopFrame memOps)
                     memPopFrame
  , useLLVMIntrinsic (llvmResolveGlobal memOps)
                     memResolveGlobal
  , useLLVMIntrinsic (llvmPtrEq memOps)
                     ptrEqOverride
  , useLLVMIntrinsic (llvmPtrLe memOps)
                     ptrLeOverride
  , useLLVMIntrinsic (llvmPtrAddOffset memOps)
                     ptrAddOffsetOverride
  , useLLVMIntrinsic (llvmPtrSubtract memOps)
                     ptrSubtractOverride
  ]

newMemOps :: forall s wptr arch. (HasPtrWidth wptr, wptr ~ ArchWidth arch)
          => Proxy arch
          -> HandleAllocator s
          -> DataLayout
          -> ST s (LLVMMemOps wptr)
newMemOps _ halloc dl = do
  memVar      <- freshGlobalVar halloc "llvm_memory" knownRepr
  alloca      <- mkLLVMHandle halloc (memAlloca @arch)
  pushFrame   <- mkLLVMHandle halloc (memPushFrame @arch)
  popFrame    <- mkLLVMHandle halloc (memPopFrame @arch)
  load        <- mkLLVMHandle halloc (memLoad @arch)
  store       <- mkLLVMHandle halloc (memStore @arch)
  loadHandle  <- mkLLVMHandle halloc (memLoadHandle @arch)
  resolveGlob <- mkLLVMHandle halloc (memResolveGlobal @arch)
  pEq         <- mkLLVMHandle halloc (ptrEqOverride @arch)
  pLe         <- mkLLVMHandle halloc (ptrLeOverride @arch)
  pAddOffset  <- mkLLVMHandle halloc (ptrAddOffsetOverride @arch)
  pSubtract   <- mkLLVMHandle halloc (ptrSubtractOverride @arch)
  let ops = LLVMMemOps
            { llvmDataLayout     = dl
            , llvmMemVar         = memVar
            , llvmMemAlloca      = alloca
            , llvmMemPushFrame   = pushFrame
            , llvmMemPopFrame    = popFrame
            , llvmMemLoad        = load
            , llvmMemStore       = store
            , llvmMemLoadHandle  = loadHandle
            , llvmResolveGlobal  = resolveGlob
            , llvmPtrEq          = pEq
            , llvmPtrLe          = pLe
            , llvmPtrAddOffset   = pAddOffset
            , llvmPtrSubtract    = pSubtract
            }
  return ops

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

-- | Produce a fresh empty memory.
--   NB, we start counting allocation blocks at '1'.
--   Block number 0 is reserved for representing raw bitvectors.
emptyMem :: IO (MemImpl sym)
emptyMem = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty G.emptyMem

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
  (ptr, mem') <- doMalloc sym G.GlobalAlloc sym_str mem sz'
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
coerceAny _sym tpr (AnyValue tpr' x)
  | Just Refl <- testEquality tpr tpr' = return x
  | otherwise = error $ unwords ["coerceAny: cannot coerce from", show tpr', "to", show tpr]


unpackMemValue
   :: (HasCallStack, IsSymInterface sym)
   => sym
   -> LLVMVal sym
   -> IO (AnyValue sym)

-- If the block number is 0, we know this is a raw bitvector, and not an actual pointer.
unpackMemValue _sym (LLVMValInt blk bv)
  = return . AnyValue (LLVMPointerRepr (bvWidth bv)) $ LLVMPointer blk bv
unpackMemValue _ (LLVMValReal x) =
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
packMemValue _ _ RealValRepr x =
       return $ LLVMValReal x
packMemValue sym _ (BVRepr _w) bv =
    do blk0 <- natLit sym 0
       return $ LLVMValInt blk0 bv
packMemValue _sym _ (LLVMPointerRepr _w) (LLVMPointer blk off) =
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
packMemValue _ _ _ _ =
  fail "Unexpected values in packMemValue"

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

memResolveGlobal :: forall arch p sym wptr. (ArchWidth arch ~ wptr, HasPtrWidth wptr) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> ConcreteType GlobalSymbol) (LLVMPointerType wptr)
memResolveGlobal =
  LLVMIntrinsicImpl
    "llvm_resolve_global"
    knownRepr
    PtrRepr $
    mkIntrinsic $ \_ sym
       (regValue -> mem)
       (regValue -> (GlobalSymbol symbol)) -> liftIO $ doResolveGlobal sym mem symbol

memLoad :: forall arch p sym wptr. (ArchWidth arch ~ wptr, HasPtrWidth wptr) =>
  LLVMIntrinsicImpl p sym arch
    (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMValTypeType ::> AlignmentType) AnyType
memLoad =
  LLVMIntrinsicImpl
    "llvm_load"
    (Empty :> memRepr :> PtrRepr :> knownRepr :> knownRepr) AnyRepr $
    mkIntrinsic $ \_ sym
      (regValue -> mem)
      (regValue -> ptr)
      (regValue -> valType)
      (regValue -> alignment) ->
        liftIO $ doLoad sym mem ptr valType alignment

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


loadRaw :: (IsSymInterface sym, HasPtrWidth wptr)
        => sym
        -> MemImpl sym
        -> LLVMPtr sym wptr
        -> G.Type
        -> IO (LLVMVal sym)
loadRaw sym mem ptr valType =
  do res <- loadRawWithCondition sym mem ptr valType
     case res of
       Right (p,r,v) -> v <$ addAssertion sym p r
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
  do v <- G.readMem sym PtrWidth ptr valType (memImplHeap mem)
     let errMsg = "Invalid memory load: address " ++ show (G.ppPtr ptr) ++
                  " at type "                     ++ show (G.ppType valType)
     case v of
       Unassigned -> return (Left errMsg)
       PE p' v' -> return (Right (p', AssertFailureSimError errMsg, v'))

doLoad :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem
  -> RegValue sym (LLVMPointerType wptr) {- ^ pointer to load from -}
  -> RegValue sym LLVMValTypeType        {- ^ type of value to load -}
  -> RegValue sym AlignmentType          {- ^ pointer alignment -}
  -> IO (RegValue sym AnyType)
doLoad sym mem ptr valType _align = do
    --putStrLn "MEM LOAD"
    let errMsg = "Invalid memory load: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    v <- G.readMem sym PtrWidth ptr valType (memImplHeap mem)
    case v of
      Unassigned ->
        fail errMsg
      PE p' v' -> do
        addAssertion sym p' (AssertFailureSimError errMsg)
        unpackMemValue sym v'

storeRaw :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> LLVMPtr sym wptr
  -> G.Type
  -> LLVMVal sym
  -> IO (MemImpl sym)
storeRaw sym mem ptr valType val = do
    (p, heap') <- G.writeMem sym PtrWidth ptr valType val (memImplHeap mem)
    let errMsg = "Invalid memory store: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    addAssertion sym p (AssertFailureSimError errMsg)
    return mem{ memImplHeap = heap' }


doStore :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> RegValue sym Mem
  -> RegValue sym (LLVMPointerType wptr) {- ^ pointer to store into -}
  -> RegValue sym LLVMValTypeType        {- ^ type of value to store -}
  -> RegValue sym AnyType                {- ^ value to store -}
  -> IO (RegValue sym Mem)
doStore sym mem ptr valType (AnyValue tpr val) = do
    --putStrLn "MEM STORE"
    let errMsg = "Invalid memory store: address " ++ show (G.ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    val' <- packMemValue sym valType tpr val
    (p, heap') <- G.writeMem sym PtrWidth ptr valType val' (memImplHeap mem)
    addAssertion sym p (AssertFailureSimError errMsg)
    return mem{ memImplHeap = heap' }

memStore :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMValTypeType ::> AnyType) Mem
memStore =
  LLVMIntrinsicImpl
    "llvm_store"
    (Empty :> memRepr :> PtrRepr :> knownRepr :> AnyRepr) memRepr $
    mkIntrinsic $ \_ sym
       (regValue -> mem)
       (regValue -> ptr)
       (regValue -> valType)
       (regValue -> val) ->
          liftIO $ doStore sym mem ptr valType val

data SomeFnHandle where
  SomeFnHandle :: FnHandle args ret -> SomeFnHandle

memLoadHandle :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> LLVMPointerType wptr) AnyType
memLoadHandle =
  LLVMIntrinsicImpl
    "llvm_load_handle"
    (Empty :> memRepr :> PtrRepr) AnyRepr $
    mkIntrinsic $ \_ sym
      (regValue -> mem)
      (regValue -> ptr) ->
         do mhandle <- liftIO $ doLookupHandle sym mem ptr
            case mhandle of
              Nothing -> fail "memLoadHandle: not a valid function pointer"
              Just (SomeFnHandle h) ->
                do let ty = FunctionHandleRepr (handleArgTypes h) (handleReturnType h)
                   return (AnyValue ty (HandleFnVal h))

memAlloca :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
   LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> BVType wptr ::> StringType)
                           (StructType (EmptyCtx ::> Mem ::> LLVMPointerType wptr))
memAlloca =
  LLVMIntrinsicImpl
    "llvm_alloca"
    (Empty :> memRepr :> SizeT :> StringRepr)
    (StructRepr (Empty :> memRepr :> PtrRepr)) $
      mkIntrinsic $ \_ sym
        (regValue -> mem)
        (regValue -> sz)
        (regValue -> loc) -> do
           liftIO $ do
             --sz_doc <- printSymExpr sym sz
             --putStrLn $ unwords ["MEM ALLOCA:", show nextBlock, show sz_doc]

           blkNum <- nextBlock (memImplBlockSource mem)
           blk <- liftIO $ natLit sym (fromIntegral blkNum)
           z <- liftIO $ bvLit sym PtrWidth 0

           let heap' = G.allocMem G.StackAlloc (fromInteger blkNum) sz (show loc) (memImplHeap mem)
           let ptr = LLVMPointer blk z
           return (Ctx.empty Ctx.:> (RV $ mem{ memImplHeap = heap' }) Ctx.:> RV ptr)

memPushFrame :: forall arch p sym. LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem) Mem
memPushFrame =
  LLVMIntrinsicImpl "llvm_pushFrame" knownRepr knownRepr $
  mkIntrinsic $ \_ _sym
  (regValue -> mem) -> do
     --liftIO $ putStrLn "MEM PUSH FRAME"
     let heap' = G.pushStackFrameMem (memImplHeap mem)
     return mem{ memImplHeap = heap' }

memPopFrame :: forall arch p sym. LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem) Mem
memPopFrame =
  LLVMIntrinsicImpl "llvm_popFrame "knownRepr knownRepr $
  mkIntrinsic $ \_ _sym
  (regValue -> mem) -> do
     --liftIO $ putStrLn "MEM POP FRAME"
     let heap' = G.popStackFrameMem (memImplHeap mem)
     return $ mem{ memImplHeap = heap' }

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
  addAssertion sym c
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


doCalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> RegValue sym (BVType wptr)
  -> RegValue sym (BVType wptr)
  -> IO (RegValue sym (LLVMPointerType wptr), MemImpl sym)
doCalloc sym mem sz num = do
  (ov, sz') <- unsignedWideMultiplyBV sym sz num
  ov_iszero <- notPred sym =<< bvIsNonzero sym ov
  addAssertion sym ov_iszero
     (AssertFailureSimError "Multiplication overflow in calloc()")

  z <- bvLit sym knownNat 0
  (ptr, mem') <- doMalloc sym G.HeapAlloc "<calloc>" mem sz'
  mem'' <- doMemset sym PtrWidth mem' ptr z sz'
  return (ptr, mem'')


doMalloc
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType
  -> String
  -> MemImpl sym
  -> RegValue sym (BVType wptr)
  -> IO (RegValue sym (LLVMPointerType wptr), MemImpl sym)
doMalloc sym allocType loc mem sz = do
  --sz_doc <- printSymExpr sym sz
  --putStrLn $ unwords ["doMalloc", show nextBlock, show sz_doc]

  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- liftIO $ natLit sym (fromIntegral blkNum)
  z <- liftIO $ bvLit sym PtrWidth 0

  let heap' = G.allocMem allocType (fromInteger blkNum) sz loc (memImplHeap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap' })

mallocRaw
  :: (IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> MemImpl sym
  -> SymExpr sym (BaseBVType wptr)
  -> IO (LLVMPtr sym wptr, MemImpl sym)
mallocRaw sym mem sz = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym PtrWidth 0

  let ptr = LLVMPointer blk z
  let heap' = G.allocMem G.HeapAlloc (fromInteger blkNum) sz "<malloc>" (memImplHeap mem)
  return (ptr, mem{ memImplHeap = heap' })


doMallocHandle
  :: (Typeable a, IsSymInterface sym, HasPtrWidth wptr)
  => sym
  -> G.AllocType
  -> String
  -> MemImpl sym
  -> a
  -> IO (RegValue sym (LLVMPointerType wptr), MemImpl sym)
doMallocHandle sym allocType loc mem x = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- liftIO $ natLit sym (fromIntegral blkNum)
  z <- liftIO $ bvLit sym PtrWidth 0

  let heap' = G.allocMem allocType (fromInteger blkNum) z loc (memImplHeap mem)
  let hMap' = Map.insert blkNum (toDyn x) (memImplHandleMap mem)
  let ptr = LLVMPointer blk z
  return (ptr, mem{ memImplHeap = heap', memImplHandleMap = hMap' })


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
  addAssertion sym c' (AssertFailureSimError errMsg)
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
      addAssertion sym c
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

  addAssertion sym c
     (AssertFailureSimError "Invalid memory region in memcpy")

  return mem{ memImplHeap = heap' }


ptrAddOffsetOverride :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> BVType wptr) (LLVMPointerType wptr)
ptrAddOffsetOverride =
   LLVMIntrinsicImpl
     "llvm_ptrAdd"
     (Empty :> memRepr :> PtrRepr :> SizeT) PtrRepr $
       mkIntrinsic $ \_ sym
       (regValue -> m)
       (regValue -> x)
       (regValue -> off) ->
         liftIO $ doPtrAddOffset sym m x off

ptrSubtractOverride :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMPointerType wptr) (BVType wptr)
ptrSubtractOverride =
  LLVMIntrinsicImpl
    "llvm_ptrSub"
    (Empty :> memRepr :> PtrRepr :> PtrRepr) SizeT $
    mkIntrinsic $ \_ sym
      (regValue -> m)
      (regValue -> x)
      (regValue -> y) ->
        liftIO $ doPtrSubtract sym m x y

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
   addAssertion sym v
       (AssertFailureSimError $ unlines ["Pointer arithmetic resulted in invalid pointer:", show x_doc, show off_doc])
   return x'

ptrEqOverride :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMPointerType wptr) BoolType
ptrEqOverride =
  LLVMIntrinsicImpl
    "llvm_ptrEq"
    (Empty :> memRepr :> PtrRepr :> PtrRepr) BoolRepr $
    mkIntrinsic $ \_ sym
      (regValue -> mem)
      (regValue -> x)
      (regValue -> y) -> liftIO $ do
         let allocs_doc = G.ppAllocs (G.memAllocs (memImplHeap mem))
         let x_doc = G.ppPtr x
         let y_doc = G.ppPtr y

         v1 <- isValidPointer sym x mem
         v2 <- isValidPointer sym y mem
         addAssertion sym v1
            (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show x_doc, show allocs_doc])
         addAssertion sym v2
            (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show y_doc, show allocs_doc])

         ptrEq sym PtrWidth x y

ptrLeOverride :: forall arch p sym wptr. (HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMIntrinsicImpl p sym arch (EmptyCtx ::> Mem ::> LLVMPointerType wptr ::> LLVMPointerType wptr) BoolType
ptrLeOverride =
  LLVMIntrinsicImpl
    "llvm_ptrLe"
    (Empty :> memRepr :> PtrRepr :> PtrRepr) BoolRepr $
    mkIntrinsic $ \_ sym
      (regValue -> mem)
      (regValue -> x)
      (regValue -> y) -> liftIO $ do
         let x_doc = G.ppPtr x
             y_doc = G.ppPtr y
         v1 <- isValidPointer sym x mem
         v2 <- isValidPointer sym y mem
         addAssertion sym v1
            (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show x_doc])
         addAssertion sym v2
            (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show y_doc])
         ptrLe sym PtrWidth x y

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
  show (LLVMValReal _) = "<real>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]

-- | Load a null-terminated string from the memory.  The pointer to read from
-- must be concrete and nonnull.  Moreover, we require all the characters in
-- the string to be concrete.  Otherwise it is very difficult to tell when the string
-- has terminated.  If a maximum number of characters is provided, no more than that
-- number of charcters will be read.  In either case, `loadString` will stop reading
-- if it encounters a null-terminator.
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
