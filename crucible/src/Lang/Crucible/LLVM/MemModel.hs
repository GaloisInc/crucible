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
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel
  ( LLVMPointerType
  , llvmPointerRepr
  , nullPointer
  , mkNullPointer
  , isNullPointer
  , PtrWidth
  , ptrWidth
  , ppPtr
  , Mem
  , memRepr
  , MemImpl
  , emptyMem
  , LLVMMemOps(..)
  , newMemOps
  , llvmMemIntrinsics
  , crucibleTermGenerator
  , GlobalMap
  , GlobalSymbol(..)
  , allocGlobals
  , assertDisjointRegions
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
  , ppMem

  -- * Direct API to LLVMVal
  , LLVMVal(..)
  , LLVMPtrExpr(..)
  , coerceAny
  , unpackMemValue
  , packMemValue
  , loadRaw
  , storeRaw
  , mallocRaw
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Dynamic
import           Data.List hiding (group)
import           Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Word
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Vector( Vector )
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L


import qualified Lang.Crucible.Core as C
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.MSSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import qualified Lang.Crucible.Syntax as S
import           Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.MemModel.Common as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G

--import Debug.Trace as Debug


type PtrWidth = 64
ptrWidth :: NatRepr PtrWidth
ptrWidth = knownNat

type LLVMPointerType = RecursiveType "LLVM_pointer"
llvmPointerRepr :: TypeRepr LLVMPointerType
llvmPointerRepr = knownRepr

instance IsRecursiveType "LLVM_pointer" where
  type UnrollType "LLVM_pointer" = StructType (EmptyCtx ::> NatType ::> BVType PtrWidth ::> BVType PtrWidth)
  unrollType _ = StructRepr (Ctx.empty Ctx.%> NatRepr Ctx.%> BVRepr ptrWidth Ctx.%> BVRepr ptrWidth)

type Mem = IntrinsicType "LLVM_memory"
memRepr :: TypeRepr Mem
memRepr = knownRepr


instance IntrinsicClass sym "LLVM_memory" where
  type Intrinsic sym "LLVM_memory" = MemImpl sym PtrWidth

  -- NB: Here we are assuming the global maps of both memories are identical.
  -- This should be the case as memories are only supposed to allocate globals at
  -- startup, not during program execution.  We could check that the maps match,
  -- but that would be expensive...
  muxIntrinsic _sym _nm p (MemImpl blockSource gMap1 hMap1 m1) (MemImpl _blockSource _gMap2 hMap2 m2) = do
     --putStrLn "MEM MERGE"
     return $ MemImpl blockSource gMap1
               (Map.union hMap1 hMap2)
               (G.mergeMem p m1 m2)
  pushBranchIntrinsic _sym _nm (MemImpl nxt gMap hMap m) = do
     --putStrLn "MEM PUSH BRANCH"
     return $ MemImpl nxt gMap hMap $ G.branchMem m
  abortBranchIntrinsic _sym _nm (MemImpl nxt gMap hMap m) = do
     --putStrLn "MEM ABORT BRANCH"
     return $ MemImpl nxt gMap hMap $ G.branchAbortMem m

type LLVMValTypeType = ConcreteType G.Type

-- Block 0 is the distinguished block corresponding to the null pointer.
-- It is always a valid pointer, but has no allocated offsets.
nullPointer :: S.IsExpr e
            => e LLVMPointerType
nullPointer = S.app $ C.RollRecursive knownSymbol $ S.app $ C.MkStruct
  (Ctx.empty Ctx.%> NatRepr
             Ctx.%> BVRepr ptrWidth
             Ctx.%> BVRepr ptrWidth)
  (Ctx.empty Ctx.%> (S.app (C.NatLit 0))
             Ctx.%> (S.app (C.BVLit ptrWidth 0))
             Ctx.%> (S.app (C.BVLit ptrWidth 0)))

mkNullPointer
  :: IsSymInterface sym
  => sym
  -> IO (RegValue sym LLVMPointerType)
mkNullPointer sym = do
  zn  <- RV <$> natLit sym 0
  zbv <- RV <$> bvLit sym ptrWidth 0
  let rec = (Ctx.empty Ctx.%> zn Ctx.%> zbv Ctx.%> zbv)
  return $ RolledType rec

isNullPointer
  :: IsSymInterface sym
  => sym
  -> RegValue sym LLVMPointerType
  -> IO (RegValue sym BoolType)
isNullPointer sym (RolledType ptr) = do
  let RV blk = ptr^._1
  let RV end = ptr^._2
  let RV off = ptr^._3

  zn  <- natLit sym 0
  zbv <- bvLit sym ptrWidth 0

  blk_z <- natEq sym blk zn
  end_z <- bvEq sym end zbv
  off_z <- bvEq sym off zbv

  andPred sym blk_z =<< andPred sym end_z off_z



newtype GlobalSymbol = GlobalSymbol L.Symbol
 deriving (Typeable, Eq, Ord, Show)

data LLVMMemOps
  = LLVMMemOps
  { llvmDataLayout :: DataLayout
  , llvmMemVar    :: C.GlobalVar Mem
  , llvmMemAlloca :: FnHandle (EmptyCtx ::> Mem ::> BVType PtrWidth)
                              (StructType (EmptyCtx ::> Mem ::> LLVMPointerType))
  , llvmMemPushFrame :: FnHandle (EmptyCtx ::> Mem) Mem
  , llvmMemPopFrame :: FnHandle (EmptyCtx ::> Mem) Mem
  , llvmMemLoad  :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType) AnyType
  , llvmMemStore :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType ::> AnyType) Mem
  , llvmResolveGlobal :: FnHandle (EmptyCtx ::> Mem ::> ConcreteType GlobalSymbol) LLVMPointerType
  , llvmPtrEq :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
  , llvmPtrLe :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
  , llvmPtrAddOffset :: FnHandle (EmptyCtx ::> LLVMPointerType ::> BVType PtrWidth) LLVMPointerType
  , llvmPtrSubtract :: FnHandle (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType) (BVType PtrWidth)
  , llvmPtrIsNull :: FnHandle (EmptyCtx ::> LLVMPointerType) BoolType
  }

llvmMemIntrinsics :: IsSymInterface sym
                  => LLVMMemOps
                  -> [FnBinding sym]
llvmMemIntrinsics memOps =
  [ useIntrinsic (llvmMemAlloca memOps)
                 memAlloca
  , useIntrinsic (llvmMemLoad memOps)
                 memLoad
  , useIntrinsic (llvmMemStore memOps)
                 memStore
  , useIntrinsic (llvmMemPushFrame memOps)
                 memPushFrame
  , useIntrinsic (llvmMemPopFrame memOps)
                 memPopFrame
  , useIntrinsic (llvmResolveGlobal memOps)
                 memResolveGlobal
  , useIntrinsic (llvmPtrEq memOps)
                 ptrEqOverride
  , useIntrinsic (llvmPtrLe memOps)
                 ptrLeOverride
  , useIntrinsic (llvmPtrIsNull memOps)
                 ptrIsNullOverride
  , useIntrinsic (llvmPtrAddOffset memOps)
                 ptrAddOffsetOverride
  , useIntrinsic (llvmPtrSubtract memOps)
                 ptrSubtractOverride
  ]

newMemOps :: HandleAllocator s
          -> DataLayout
          -> ST s LLVMMemOps
newMemOps halloc dl = do
  memVar      <- C.freshGlobalVar halloc "llvm_memory" knownRepr
  alloca      <- mkHandle halloc "llvm_alloca"
  pushFrame   <- mkHandle halloc "llvm_pushFrame"
  popFrame    <- mkHandle halloc "llvm_popFrame"
  load        <- mkHandle halloc "llvm_load"
  store       <- mkHandle halloc "llvm_store"
  resolveGlob <- mkHandle halloc "llvm_resolve_global"
  pEq         <- mkHandle halloc "llvm_ptrEq"
  pLe         <- mkHandle halloc "llvm_ptrLe"
  pAddOffset  <- mkHandle halloc "llvm_ptrAddOffset"
  pSubtract   <- mkHandle halloc "llvm_ptrSubtract"
  pIsNull     <- mkHandle halloc "llvm_ptrIsNull"
  let ops = LLVMMemOps
            { llvmDataLayout     = dl
            , llvmMemVar         = memVar
            , llvmMemAlloca      = alloca
            , llvmMemPushFrame   = pushFrame
            , llvmMemPopFrame    = popFrame
            , llvmMemLoad        = load
            , llvmMemStore       = store
            , llvmResolveGlobal  = resolveGlob
            , llvmPtrEq          = pEq
            , llvmPtrLe          = pLe
            , llvmPtrAddOffset   = pAddOffset
            , llvmPtrSubtract    = pSubtract
            , llvmPtrIsNull      = pIsNull
            }
  return ops

newtype BlockSource = BlockSource (IORef Integer)

nextBlock :: BlockSource -> IO Integer
nextBlock (BlockSource ref) =
  atomicModifyIORef' ref (\n -> (n+1, n))


data MemImpl sym w =
  MemImpl
  { memImplBlockSource :: BlockSource
  , memImplGlobalMap   :: GlobalMap sym
  , memImplHandleMap   :: Map Integer Dynamic
  , memImplHeap        :: G.Mem (LLVMPtrExpr (SymExpr sym) w) (Pred sym) (PartExpr (Pred sym) (LLVMVal sym w))
  }

-- NB block numbers start counting at 1 because the null pointer
-- uses distinguished block 0
emptyMem :: IO (MemImpl sym w)
emptyMem = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty G.emptyMem

type GlobalMap sym = Map L.Symbol (RegValue sym LLVMPointerType)

allocGlobals :: IsSymInterface sym
             => sym
             -> [(L.Symbol, G.Size)]
             -> MemImpl sym PtrWidth
             -> IO (MemImpl sym PtrWidth)
allocGlobals sym gs mem = foldM (allocGlobal sym) mem gs

allocGlobal :: IsSymInterface sym
            => sym
            -> MemImpl sym PtrWidth
            -> (L.Symbol, G.Size)
            -> IO (MemImpl sym PtrWidth)
allocGlobal sym (MemImpl blockSource gMap hMap mem) (symbol, sz) = do
  blkNum <- nextBlock blockSource
  blk <- natLit sym (fromIntegral blkNum)
  z   <- bvLit sym ptrWidth 0
  sz' <- bvLit sym ptrWidth (fromIntegral sz)

  let mem'  = G.allocMem G.GlobalAlloc (LLVMPtr blk sz' z) (LLVMOffset sz') mem
  let ptr   = RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV sz' Ctx.%> RV z)
  let gMap' = Map.insert symbol ptr gMap
  return (MemImpl blockSource gMap' hMap mem')


asCrucibleType
  :: G.Type
  -> (forall tpr. TypeRepr tpr -> x)
  -> x
asCrucibleType (G.Type tf _) k =
  case tf of
    G.Bitvector sz ->
       case someNat (fromIntegral sz * 8) of
         Just (Some w)
           | Just LeqProof <- isPosNat w -> k (BVRepr w)
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
                   go (ctx Ctx.%> tpr) fs k'

coerceAny :: IsSymInterface sym
          => sym
          -> TypeRepr tpr
          -> AnyValue sym
          -> IO (RegValue sym tpr)
coerceAny _sym tpr (AnyValue tpr' x)
  | Just Refl <- testEquality tpr tpr' = return x
  | otherwise = fail $ unwords ["coerceAny: cannot coerce from", show tpr', "to", show tpr]

unpackMemValue
   :: IsSymInterface sym
   => sym
   -> LLVMVal sym PtrWidth
   -> IO (AnyValue sym)
unpackMemValue _ (LLVMValPtr blk end off) =
  return $ AnyValue llvmPointerRepr $ RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV end Ctx.%> RV off)
unpackMemValue _ (LLVMValFunPtr args ret h) = do
  return $ AnyValue (FunctionHandleRepr args ret) $ h
unpackMemValue _ (LLVMValInt w x) =
  return $ AnyValue (BVRepr w) x
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
      unpackStruct sym vs (ctx Ctx.%> tpr) (fls Ctx.%> RV x) k


packMemValue
   :: IsSymInterface sym
   => sym
   -> G.Type
   -> TypeRepr tp
   -> RegValue sym tp
   -> IO (LLVMVal sym PtrWidth)
packMemValue _ _ (BVRepr w) x =
       return $ LLVMValInt w x
packMemValue _ _ RealValRepr x =
       return $ LLVMValReal x
packMemValue _ _ (RecursiveRepr nm) (RolledType xs)
  | Just Refl <- testEquality nm (knownSymbol :: SymbolRepr "LLVM_pointer") = do
      let RV blk = xs^._1
      let RV end = xs^._2
      let RV off = xs^._3
      return $ LLVMValPtr blk end off
packMemValue _ _ (FunctionHandleRepr args ret) h =
  return $ LLVMValFunPtr args ret h
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
  :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> L.Symbol
  -> IO (RegValue sym LLVMPointerType)
doResolveGlobal _sym mem symbol =
  case Map.lookup symbol (memImplGlobalMap mem) of
    Just ptr -> return ptr
    Nothing  -> fail $ unwords ["Unable to resolve global symbol", show symbol]

memResolveGlobal :: IntrinsicImpl sym (EmptyCtx ::> Mem ::> ConcreteType GlobalSymbol) LLVMPointerType
memResolveGlobal = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> (GlobalSymbol symbol)) -> liftIO $ doResolveGlobal sym mem symbol

memLoad :: IntrinsicImpl sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType) AnyType
memLoad = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> ptr)
  (regValue -> valType) ->
    liftIO $ doLoad sym mem ptr valType

ppMem
  :: IsSymInterface sym
  => sym
  -> RegValue sym Mem
  -> IO Doc
ppMem _sym mem = do
  let pp = G.PP
           { G.ppPtr  = \_x p -> return $ ppPtrExpr ptrWidth p
           , G.ppCond = \_x c -> return $ printSymExpr c
           , G.ppTerm = \_x t -> return $ ppPartTermExpr ptrWidth t
           }
  G.ppMem pp (memImplHeap mem)

doDumpMem :: IsSymInterface sym
  => sym
  -> Handle
  -> RegValue sym Mem
  -> IO ()
doDumpMem sym h mem = do
  doc <- ppMem sym mem
  hPutStrLn h (show doc)


loadRaw :: IsSymInterface sym
        => sym
        -> MemImpl sym PtrWidth
        -> LLVMPtrExpr (SymExpr sym) PtrWidth
        -> G.Type
        -> IO (LLVMVal sym PtrWidth)
loadRaw sym mem ptr valType = do
  (p,v) <- G.readMem (crucibleTermGenerator sym ptrWidth) ptr valType (memImplHeap mem)
  case v of
      Unassigned ->
        fail errMsg
      PE p' v' -> do
        p'' <- andPred sym p p'
        addAssertion sym p'' (AssertFailureSimError errMsg)
        return v'
  where
    errMsg = "Invalid memory load: " ++ show (ppPtrExpr ptrWidth ptr)

doLoad :: IsSymInterface sym
  => sym
  -> RegValue sym Mem
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMValTypeType
  -> IO (RegValue sym AnyType)
doLoad sym mem ptr valType = do
    --putStrLn "MEM LOAD"
    let ptr' = translatePtr ptr
        errMsg = "Invalid memory load: " ++ show (ppPtr ptr)
    (p, v) <- G.readMem (crucibleTermGenerator sym ptrWidth) ptr' valType (memImplHeap mem)
    case v of
      Unassigned ->
        fail errMsg
      PE p' v' -> do
        p'' <- andPred sym p p'
        addAssertion sym p'' (AssertFailureSimError errMsg)
        unpackMemValue sym v'

storeRaw :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> LLVMPtrExpr (SymExpr sym) PtrWidth
  -> G.Type
  -> LLVMVal sym PtrWidth
  -> IO (MemImpl sym PtrWidth)
storeRaw sym mem ptr valType val = do
    (p, heap') <- G.writeMem (crucibleTermGenerator sym ptrWidth) ptr valType (PE (truePred sym) val) (memImplHeap mem)
    addAssertion sym p (AssertFailureSimError "Invalid memory store")
    return mem{ memImplHeap = heap' }


doStore :: IsSymInterface sym
  => sym
  -> RegValue sym Mem
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMValTypeType
  -> RegValue sym AnyType
  -> IO (RegValue sym Mem)
doStore sym mem ptr valType (AnyValue tpr val) = do
    --putStrLn "MEM STORE"
    val' <- packMemValue sym valType tpr val
    let ptr' = translatePtr ptr
    (p, heap') <- G.writeMem (crucibleTermGenerator sym ptrWidth) ptr' valType (PE (truePred sym) val') (memImplHeap mem)
    addAssertion sym p (AssertFailureSimError "Invalid memory store")
    return mem{ memImplHeap = heap' }

memStore :: IntrinsicImpl sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType ::> AnyType) Mem
memStore = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> ptr)
  (regValue -> valType)
  (regValue -> val) ->
     liftIO $ doStore sym mem ptr valType val

memAlloca :: IntrinsicImpl sym (EmptyCtx ::> Mem ::> BVType PtrWidth)
                           (StructType (EmptyCtx ::> Mem ::> LLVMPointerType))
memAlloca = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> sz) -> do
     liftIO $ do
       --sz_doc <- printSymExpr sym sz
       --putStrLn $ unwords ["MEM ALLOCA:", show nextBlock, show sz_doc]

     blkNum <- nextBlock (memImplBlockSource mem)
     blk <- liftIO $ natLit sym (fromIntegral blkNum)
     z <- liftIO $ bvLit sym ptrWidth 0

     let heap' = G.allocMem G.StackAlloc (LLVMPtr blk sz z) (LLVMOffset sz) (memImplHeap mem)
     let ptr = RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV sz Ctx.%> RV z)
     return (Ctx.empty Ctx.%> (RV $ mem{ memImplHeap = heap' }) Ctx.%> RV ptr)

memPushFrame :: IntrinsicImpl sym (EmptyCtx ::> Mem) Mem
memPushFrame = mkIntrinsic $ \_ _sym
  (regValue -> mem) -> do
     --liftIO $ putStrLn "MEM PUSH FRAME"
     let heap' = G.pushStackFrameMem (memImplHeap mem)
     return mem{ memImplHeap = heap' }

memPopFrame :: IntrinsicImpl sym (EmptyCtx ::> Mem) Mem
memPopFrame = mkIntrinsic $ \_ _sym
  (regValue -> mem) -> do
     --liftIO $ putStrLn "MEM POP FRAME"
     let heap' = G.popStackFrameMem (memImplHeap mem)
     return $ mem{ memImplHeap = heap' }


translatePtr :: RegValue sym LLVMPointerType
             -> LLVMPtrExpr (SymExpr sym) PtrWidth
translatePtr (RolledType xs) =
   let RV blk = xs^._1 in
   let RV end = xs^._2 in
   let RV off = xs^._3 in
   LLVMPtr blk end off


translatePtrBack :: LLVMPtrExpr (SymExpr sym) PtrWidth
                 -> IO (RegValue sym LLVMPointerType)
translatePtrBack (LLVMPtr blk end off) =
  return $ RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV end Ctx.%> RV off)
translatePtrBack (LLVMOffset _) =
  fail "Expected pointer value, but got offset value instead"

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
--   2) Their blocks are the same, but dest+len <= src
--   3) Their blocks are the same, but src+len <= dest
assertDisjointRegions
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType w)
  -> IO ()
assertDisjointRegions sym w dest src len = do
  len' <- sextendBVTo sym w ptrWidth len
  let LLVMPtr dblk _ doff = translatePtr dest
  let LLVMPtr sblk _ soff = translatePtr src

  dend <- bvAdd sym doff len'
  send <- bvAdd sym soff len'

  diffBlk   <- notPred sym =<< natEq sym dblk sblk
  destfirst <- bvSle sym dend soff
  srcfirst  <- bvSle sym send doff

  c <- orPred sym diffBlk =<< orPred sym destfirst srcfirst

  addAssertion sym c
     (AssertFailureSimError "Memory regions not disjoint in memcpy")


doCalloc
  :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> RegValue sym (BVType PtrWidth)
  -> RegValue sym (BVType PtrWidth)
  -> IO (RegValue sym LLVMPointerType, MemImpl sym PtrWidth)
doCalloc sym mem sz num = do
  (ov, sz') <- unsignedWideMultiplyBV sym sz num
  ov_iszero <- notPred sym =<< bvIsNonzero sym ov
  addAssertion sym ov_iszero
     (AssertFailureSimError "Multiplication overflow in calloc()")

  z <- bvLit sym knownNat 0
  (ptr, mem') <- doMalloc sym mem sz'
  mem'' <- doMemset sym ptrWidth mem' ptr z sz'
  return (ptr, mem'')


doMalloc
  :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> RegValue sym (BVType PtrWidth)
  -> IO (RegValue sym LLVMPointerType, MemImpl sym PtrWidth)
doMalloc sym mem sz = do
  --sz_doc <- printSymExpr sym sz
  --putStrLn $ unwords ["doMalloc", show nextBlock, show sz_doc]

  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- liftIO $ natLit sym (fromIntegral blkNum)
  z <- liftIO $ bvLit sym ptrWidth 0

  let heap' = G.allocMem G.HeapAlloc (LLVMPtr blk sz z) (LLVMOffset sz) (memImplHeap mem)
  let ptr = RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV sz Ctx.%> RV z)
  return (ptr, mem{ memImplHeap = heap' })

mallocRaw
  :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> SymExpr sym (BaseBVType PtrWidth)
  -> IO (LLVMPtrExpr (SymExpr sym) PtrWidth, MemImpl sym PtrWidth)
mallocRaw sym mem sz = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym ptrWidth 0

  let ptr = LLVMPtr blk sz z
  let heap' = G.allocMem G.HeapAlloc ptr (LLVMOffset sz) (memImplHeap mem)
  return (ptr, mem{ memImplHeap = heap' })


doMallocHandle
  :: (Typeable a, IsSymInterface sym)
  => sym
  -> MemImpl sym PtrWidth
  -> a
  -> IO (RegValue sym LLVMPointerType, MemImpl sym PtrWidth)
doMallocHandle sym mem x = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- liftIO $ natLit sym (fromIntegral blkNum)
  z <- liftIO $ bvLit sym ptrWidth 0

  let heap' = G.allocMem G.HeapAlloc (LLVMPtr blk z z) (LLVMOffset z) (memImplHeap mem)
  let hMap' = Map.insert blkNum (toDyn x) (memImplHandleMap mem)
  let ptr = RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV z Ctx.%> RV z)

  return (ptr, mem{ memImplHeap = heap', memImplHandleMap = hMap' })


doLookupHandle
  :: (Typeable a, IsSymInterface sym)
  => sym
  -> MemImpl sym PtrWidth
  -> RegValue sym LLVMPointerType
  -> IO (Maybe a)
doLookupHandle _sym mem ptr = do
  let (LLVMPtr blk _ _) = translatePtr ptr
  case asNat blk of
    Just i ->
      case Map.lookup (toInteger i) (memImplHandleMap mem) of
        Just x -> return $! fromDynamic x
        Nothing -> return Nothing
    Nothing -> return Nothing


doFree
  :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> RegValue sym LLVMPointerType
  -> IO (MemImpl sym PtrWidth)
doFree sym mem ptr = do
  let tg = crucibleTermGenerator sym ptrWidth
  let ptr'@(LLVMPtr blk _ _) = translatePtr ptr
  (c, heap') <- G.freeMem tg ptr' (memImplHeap mem)

  -- If this pointer is a handle pointer, remove the associated data
  let hMap' =
       case asNat blk of
         Just i  -> Map.delete (toInteger i) (memImplHandleMap mem)
         Nothing -> memImplHandleMap mem

  -- NB: free is defined and has no effect if passed a null pointer
  isNull <- ptrIsNull sym ptr
  c' <- orPred sym c isNull
  addAssertion sym c'
     (AssertFailureSimError "Invalid free (double free or invalid pointer)")
  return mem{ memImplHeap = heap', memImplHandleMap = hMap' }

doMemset
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> MemImpl sym PtrWidth
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType 8)
  -> RegValue sym (BVType w)
  -> IO (MemImpl sym PtrWidth)
doMemset sym _w mem dest val len = do
  --dest_doc <- ppPtr sym dest
  --val_doc <- printSymExpr sym val
  --len_doc <- printSymExpr sym len
  --putStrLn $ unwords ["doMemset:", show dest_doc, show val_doc, show len_doc]

  let tg = crucibleTermGenerator sym ptrWidth
  case asUnsignedBV len of
    Nothing -> do
      -- FIXME? can we lift this restriction?
      -- Perhaps should add a MemSet constructor
      -- to MemWrites and deal with things that way...
      fail "memset requires concrete length"
    Just sz -> do
      let tp   = G.arrayType (fromInteger sz) (G.bitvectorType 1)
      let val' = LLVMValInt (knownNat :: NatRepr 8) val
      let xs   = V.generate (fromInteger sz) (\_ -> val')
      let arr  = PE (truePred sym) (LLVMValArray (G.bitvectorType 1) xs)
      (c, heap') <- G.writeMem tg (translatePtr dest) tp arr (memImplHeap mem)
      addAssertion sym c
         (AssertFailureSimError "Invalid region specified in memset")
      return mem{ memImplHeap = heap' }


doMemcpy
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> MemImpl sym PtrWidth
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType w)
  -> IO (MemImpl sym PtrWidth)
doMemcpy sym w mem dest src len = do
  let dest' = translatePtr dest
  let src'  = translatePtr src
  len' <- LLVMOffset <$> sextendBVTo sym w ptrWidth len
  let tg = crucibleTermGenerator sym ptrWidth

  (c, heap') <- G.copyMem tg dest' src' len' (memImplHeap mem)

  addAssertion sym c
     (AssertFailureSimError "Invalid memory region in memcpy")

  return mem{ memImplHeap = heap' }

ppPtr :: IsExpr (SymExpr sym) => RegValue sym LLVMPointerType -> Doc
ppPtr (RolledType xs) =
    text "(" <> blk_doc <> text "," <+> end_doc <> text "," <+> off_doc <> text ")"
  where RV blk = xs^._1
        RV end = xs^._2
        RV off = xs^._3
        blk_doc = printSymExpr blk
        end_doc = printSymExpr end
        off_doc = printSymExpr off

ppPtrExpr :: IsExpr e => NatRepr w -> LLVMPtrExpr e w -> Doc
ppPtrExpr _w (LLVMPtr blk _ off) = parens $ blk_doc <> ", " <> off_doc
  where blk_doc = printSymExpr blk
        off_doc = printSymExpr off
ppPtrExpr _w (LLVMOffset off) = printSymExpr off

ppAllocs :: IsSymInterface sym => sym -> [G.MemAlloc (LLVMPtrExpr (SymExpr sym) PtrWidth) (Pred sym)] -> IO Doc
ppAllocs sym xs = vcat <$> mapM ppAlloc xs
 where ppAlloc (G.Alloc allocTp base sz) = do
            let base_doc = ppPtrExpr ptrWidth base
            let sz_doc   = ppPtrExpr ptrWidth sz
            return $ text (show allocTp) <+> base_doc <+> text "SIZE:" <+> sz_doc
       ppAlloc (G.AllocMerge p a1 a2) = do
            a1_doc <- ppAllocs sym a1
            a2_doc <- ppAllocs sym a2
            return $ text "if" <+> printSymExpr p <+> text "then"
                     <$$>
                     (indent 2 a1_doc)
                     <$$>
                     text "else"
                     <$$>
                     (indent 2 a2_doc)


ptrAddOffsetOverride :: IntrinsicImpl sym (EmptyCtx ::> LLVMPointerType ::> BVType PtrWidth) LLVMPointerType
ptrAddOffsetOverride = mkIntrinsic $ \_ sym
   (regValue -> x)
   (regValue -> off) ->
     liftIO $ doPtrAddOffset sym x off

ptrSubtractOverride :: IntrinsicImpl sym (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType) (BVType PtrWidth)
ptrSubtractOverride = mkIntrinsic $ \_ sym
   (regValue -> x)
   (regValue -> y) ->
     liftIO $ doPtrSubtract sym x y

doPtrSubtract
  :: IsSymInterface sym
  => sym
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMPointerType
  -> IO (RegValue sym (BVType PtrWidth))
doPtrSubtract sym x y = do
   let px = translatePtr x
   let py = translatePtr y
   diff <- ptrSub sym ptrWidth px py
   case diff of
     LLVMOffset off -> return off
     LLVMPtr _ _ _ ->
       fail "Expected offset as result of subtraction, but got pointer instead"

doPtrAddOffset
  :: IsSymInterface sym
  => sym
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType PtrWidth)
  -> IO (RegValue sym LLVMPointerType)
doPtrAddOffset sym x off = do
      let px = translatePtr x
      let poff = LLVMOffset off
      (v, p') <- ptrCheckedAdd sym ptrWidth px poff
      let x_doc = ppPtr x
      let off_doc = printSymExpr off
      addAssertion sym v
         (AssertFailureSimError $ unlines ["Pointer arithmetic resulted in invalid pointer:", show x_doc, show off_doc])
      translatePtrBack p'

ptrEqOverride :: IntrinsicImpl sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
ptrEqOverride = mkIntrinsic $ \_ sym
   (regValue -> mem)
   (regValue -> x)
   (regValue -> y) -> liftIO $ do
      allocs_doc <- ppAllocs sym (G.memAllocs (memImplHeap mem))
      let x_doc = ppPtr x
      let y_doc = ppPtr y

      v1 <- isValidPointer sym x mem
      v2 <- isValidPointer sym y mem
      addAssertion sym v1
         (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show x_doc, show allocs_doc])
      addAssertion sym v2
         (AssertFailureSimError $ unlines ["Invalid pointer compared for equality:", show y_doc, show allocs_doc])

      let px = translatePtr x
      let py = translatePtr y
      ptrEq sym ptrWidth px py

ptrLeOverride :: IntrinsicImpl sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
ptrLeOverride = mkIntrinsic $ \_ sym
   (regValue -> mem)
   (regValue -> x)
   (regValue -> y) -> liftIO $ do
      let x_doc = ppPtr x
          y_doc = ppPtr y
      v1 <- isValidPointer sym x mem
      v2 <- isValidPointer sym y mem
      addAssertion sym v1
         (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show x_doc])
      addAssertion sym v2
         (AssertFailureSimError $ unwords ["Invalid pointer compared for ordering:", show y_doc])

      let px = translatePtr x
      let py = translatePtr y
      ptrLe sym ptrWidth px py

ptrIsNullOverride :: IntrinsicImpl sym (EmptyCtx ::> LLVMPointerType) BoolType
ptrIsNullOverride = mkIntrinsic $ \_ sym
  (regValue -> x) -> liftIO $ ptrIsNull sym x

isValidPointer :: IsSymInterface sym => sym
               -> RegValue sym LLVMPointerType
               -> RegValue sym Mem
               -> IO (Pred sym)
isValidPointer sym p mem = do
   c1 <- ptrIsNull sym p
   c2 <- G.isValidPointer (crucibleTermGenerator sym ptrWidth) (translatePtr p) (memImplHeap mem)
   orPred sym c1 c2

ptrIsNull :: IsSymInterface sym
          => sym
          -> RegValue sym LLVMPointerType
          -> IO (Pred sym)
ptrIsNull sym _p@(RolledType x) = do
    let RV blk = x^._1
    --let RV end = x^._2
    let RV off = x^._3
    --p_doc <- ppPtr sym p
    --putStrLn $ unwords ["Testing for null pointer:" , show p_doc]
    pblk <- natEq sym blk =<< natLit sym 0
    poff <- bvEq sym off =<< bvLit sym ptrWidth 0
    andPred sym pblk poff


data LLVMPtrExpr e w
  = LLVMPtr (e BaseNatType)     --  Block number
            (e (BaseBVType w))  --  End-of-block offset (1 past end of valid bytes)
            (e (BaseBVType w))  --  Current offset in block
  | LLVMOffset (e (BaseBVType w))

-- NB, this is a somewhat strange Eq instance.  It is used by
-- the Generic memory model module to compare pointers that are
-- known to be concrete base pointers.
-- Thus, we simply assume that the given values are concrete and
-- have offset 0.  This essentially comes down to comparing the
-- allocation block numbers.
instance IsExpr e => Eq (LLVMPtrExpr e w) where
  LLVMPtr b1 _ _== LLVMPtr b2 _ _
    | Just blk1 <- asNat b1
    , Just blk2 <- asNat b2 = blk1 == blk2
         --Debug.trace (unwords ["Comparing blocks:",show blk1, show blk2]) $ blk1 == blk2
  _ == _ = False


instance (IsExpr e, OrdF e) => Ord (LLVMPtrExpr e w) where
  compare (LLVMPtr _ _ _) (LLVMOffset _) = LT
  compare (LLVMPtr b1 _ off1) (LLVMPtr b2 _ off2) =
     case compareF b1 b2 of
       LTF -> LT
       GTF -> GT
       EQF -> case compareF off1 off2 of
                LTF -> LT
                GTF -> GT
                EQF -> EQ
  compare (LLVMOffset _) (LLVMPtr _ _ _) = GT
  compare (LLVMOffset off1) (LLVMOffset off2) =
     case compareF off1 off2 of
       LTF -> LT
       GTF -> GT
       EQF -> EQ

data LLVMVal sym w where
  LLVMValPtr :: SymNat sym -> SymBV sym w -> SymBV sym w -> LLVMVal sym w
  LLVMValFunPtr :: CtxRepr args -> TypeRepr ret -> FnVal sym args ret -> LLVMVal sym w
  LLVMValInt :: (1 <= x) => NatRepr x -> SymBV sym x -> LLVMVal sym w
  LLVMValReal :: SymReal sym -> LLVMVal sym w
  LLVMValStruct :: Vector (G.Field G.Type, LLVMVal sym w) -> LLVMVal sym w
  LLVMValArray :: G.Type -> Vector (LLVMVal sym w) -> LLVMVal sym w

ppPartTermExpr
  :: IsSymInterface sym
  => NatRepr w
  -> PartExpr (Pred sym) (LLVMVal sym w)
  -> Doc
ppPartTermExpr _w Unassigned = text "<undef>"
ppPartTermExpr w (PE _p t) = ppTermExpr w t

ppTermExpr
  :: IsSymInterface sym
  => NatRepr w
  -> LLVMVal sym w
  -> Doc
ppTermExpr w t = -- FIXME, do something with the predicate?
  case t of
    LLVMValPtr base end off -> text "ptr" <> ppPtrExpr w (LLVMPtr base end off)
    LLVMValFunPtr _args _ret fnval -> text "fun(" <> (text $ show fnval) <> text ")"
    LLVMValInt _x v -> printSymExpr v
    LLVMValReal v -> printSymExpr v
    LLVMValStruct v -> encloseSep lbrace rbrace comma v''
      where v'  = fmap (over _2 (ppTermExpr w)) (V.toList v)
            v'' = map (\(fld,doc) ->
                        group (text "base+" <> text (show $ G.fieldOffset fld) <+> equals <+> doc))
                      v'
    LLVMValArray _tp v -> encloseSep lbracket rbracket comma v'
      where v' = ppTermExpr w <$> V.toList v

instance Show (LLVMVal sym w) where
  show (LLVMValPtr _ _ _) = "<ptr>"
  show (LLVMValFunPtr _ _ h) = "<fnptr: "++ show h ++">"
  show (LLVMValInt w _ ) = "<int" ++ show w ++ ">"
  show (LLVMValReal _) = "<real>"
  show (LLVMValStruct xs) =
    unwords $ [ "{" ]
           ++ intersperse ", " (map (show . snd) $ V.toList xs)
           ++ [ "}" ]
  show (LLVMValArray _ xs) =
    unwords $ [ "[" ]
           ++ intersperse ", " (map show $ V.toList xs)
           ++ [ "]" ]

crucibleTermGenerator
   :: (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.TermGenerator IO (LLVMPtrExpr (SymExpr sym) w)
                         (Pred sym)
                         (PartExpr (Pred sym) (LLVMVal sym w))
crucibleTermGenerator sym w =
   G.TG
   { G.tgPtrWidth = fromIntegral $ natValue w
   , G.tgPtrDecompose = ptrDecompose sym w
   , G.tgPtrSizeDecompose = ptrSizeDecompose sym w
   , G.tgConstPtr = \x -> LLVMOffset <$> bvLit sym w (fromIntegral x)
   , G.tgAddPtr = ptrAdd sym w
   , G.tgCheckedAddPtr = ptrCheckedAdd sym w
   , G.tgSubPtr = ptrSub sym w

   , G.tgFalse = falsePred sym
   , G.tgTrue = truePred sym
   , G.tgPtrEq = ptrEq sym w
   , G.tgPtrLe = \x y -> do
        ans <- ptrLe sym w x y
        --x_doc <- ppPtrExpr sym w x
        --y_doc <- ppPtrExpr sym w y
        --ans_doc <- printSymExpr ans
        --putStrLn (unwords ["PTR <=", show x_doc, show y_doc, show ans_doc])
        return ans

   , G.tgAnd = andPred sym
   , G.tgOr = orPred sym
   , G.tgMuxCond = itePred sym

   , G.tgUndefValue = \_tp -> return $ Unassigned
   , G.tgApplyCtorF = applyCtorFLLVMVal sym w
   , G.tgApplyViewF = applyViewFLLVMVal sym w
   , G.tgMuxTerm = \c _ -> muxLLVMVal sym w c
   }



ptrDecompose :: (1 <= w, IsExprBuilder sym)
             => sym
             -> NatRepr w
             -> LLVMPtrExpr (SymExpr sym) w
             -> IO (G.AddrDecomposeResult (LLVMPtrExpr (SymExpr sym) w))
ptrDecompose sym w (LLVMPtr base@(asNat -> Just _) end (asUnsignedBV -> Just off)) = do
  z <- bvLit sym w 0
  return (G.ConcreteOffset (LLVMPtr base end z) off)
ptrDecompose sym w (LLVMPtr base@(asNat -> Just _) end off) = do
  z <- bvLit sym w 0
  return $ G.SymbolicOffset (LLVMPtr base end z) (LLVMOffset off)
ptrDecompose _sym _w p@(LLVMPtr _ _ _) = do
  return $ G.Symbolic p
ptrDecompose _ _ (LLVMOffset _) =
  fail "Attempted to treat raw offset as pointer"

ptrSizeDecompose
  :: IsExprBuilder sym
  => sym
  -> NatRepr w
  -> LLVMPtrExpr (SymExpr sym) w
  -> IO (Maybe Integer)
ptrSizeDecompose _ _ (LLVMOffset (asUnsignedBV -> Just off)) =
  return (Just off)
ptrSizeDecompose _ _ _ = return Nothing


ptrEq :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtrExpr (SymExpr sym) w
      -> LLVMPtrExpr (SymExpr sym) w
      -> IO (Pred sym)
ptrEq sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) = do
  p1 <- natEq sym base1 base2
  p2 <- bvEq sym off1 off2
  andPred sym p1 p2
ptrEq sym _w (LLVMOffset off1) (LLVMOffset off2) = do
  bvEq sym off1 off2

-- Comparison of a pointer to the null pointer (offset 0) is allowed,
-- but all other direct ptr/offset comparisons are not allowed
ptrEq sym w (LLVMOffset off) (LLVMPtr _ _ _) = do
  z <- bvLit sym w 0
  p <- bvEq sym off z
  addAssertion sym p (AssertFailureSimError "Invalid attempt to compare a pointer and a raw offset for equality")
  return (falsePred sym)
ptrEq sym w (LLVMPtr _ _ _) (LLVMOffset off) = do
  z <- bvLit sym w 0
  p <- bvEq sym off z
  addAssertion sym p (AssertFailureSimError "Invalid attempt to compare a pointer and a raw offset for equality")
  return (falsePred sym)

ptrLe :: (1 <= w, IsSymInterface sym)
      => sym
      -> NatRepr w
      -> LLVMPtrExpr (SymExpr sym) w
      -> LLVMPtrExpr (SymExpr sym) w
      -> IO (Pred sym)
ptrLe sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) = do
  p1 <- natEq sym base1 base2
  addAssertion sym p1 (AssertFailureSimError "Attempted to compare pointers from different allocations")
  bvSle sym off1 off2
ptrLe sym _w (LLVMOffset off1) (LLVMOffset off2) = do
  bvSle sym off1 off2
ptrLe _ _ _ _ =
  fail "Invalid attempt to compare a pointer and a raw offset"


ptrAdd :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtrExpr (SymExpr sym) w
       -> LLVMPtrExpr (SymExpr sym) w
       -> IO (LLVMPtrExpr (SymExpr sym) w)
ptrAdd sym _w (LLVMPtr base end off1) (LLVMOffset off2) = do
  off' <- bvAdd sym off1 off2
  return $ LLVMPtr base end off'
ptrAdd sym _w (LLVMOffset off1) (LLVMPtr base end off2) = do
  off' <- bvAdd sym off1 off2
  return $ LLVMPtr base end off'
ptrAdd sym _w (LLVMOffset off1) (LLVMOffset off2) = do
  off' <- bvAdd sym off1 off2
  return $ LLVMOffset off'
ptrAdd _sym _w (LLVMPtr _ _ _) (LLVMPtr _ _ _) = do
  fail "Attempted to add to pointers"

ptrCheckedAdd
       :: (1 <= w, IsExprBuilder sym)
       => sym
       -> NatRepr w
       -> LLVMPtrExpr (SymExpr sym) w
       -> LLVMPtrExpr (SymExpr sym) w
       -> IO (Pred sym, LLVMPtrExpr (SymExpr sym) w)
ptrCheckedAdd sym w (LLVMPtr base end off1) (LLVMOffset off2) = do
  z <- bvLit sym w 0
  (p1, off') <- addSignedOF sym off1 off2
  p1' <- notPred sym p1
  p2 <- bvSle sym off' end
  p3 <- bvSle sym z off'
  p <- andPred sym p1' =<< andPred sym p2 p3
  return $ (p, LLVMPtr base end off')
ptrCheckedAdd sym w (LLVMOffset off1) (LLVMPtr base end off2) = do
  z <- bvLit sym w 0
  (p1, off') <- addSignedOF sym off1 off2
  p1' <- notPred sym p1
  p2 <- bvSle sym off' end
  p3 <- bvSle sym z off'
  p <- andPred sym p1' =<< andPred sym p2 p3
  return $ (p, LLVMPtr base end off')
ptrCheckedAdd sym _w (LLVMOffset off1) (LLVMOffset off2) = do
  (p, off') <- addSignedOF sym off1 off2
  p' <- notPred sym p
  return $ (p', LLVMOffset off')
ptrCheckedAdd _sym _w (LLVMPtr _ _ _) (LLVMPtr _ _ _) = do
  fail "Attempted to add to pointers"


ptrSub :: (1 <= w, IsSymInterface sym)
       => sym
       -> NatRepr w
       -> LLVMPtrExpr (SymExpr sym) w
       -> LLVMPtrExpr (SymExpr sym) w
       -> IO (LLVMPtrExpr (SymExpr sym) w)
ptrSub sym _w (LLVMPtr base1 _ off1) (LLVMPtr base2 _ off2) = do
  p <- natEq sym base1 base2
  addAssertion sym p (AssertFailureSimError "Attempted to subtract pointers from different allocations")
  diff <- bvSub sym off1 off2
  return (LLVMOffset diff)
ptrSub sym _w (LLVMOffset off1) (LLVMOffset off2) = do
  diff <- bvSub sym off1 off2
  return (LLVMOffset diff)
ptrSub _sym _w (LLVMOffset _) (LLVMPtr _ _ _) = do
  fail "Cannot substract pointer value from raw offset"
ptrSub sym _w (LLVMPtr base end off1) (LLVMOffset off2) = do
  diff <- bvSub sym off1 off2
  return (LLVMPtr base end diff)


applyCtorFLLVMVal :: forall sym w
    . (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.ValueCtorF (PartExpr (Pred sym) (LLVMVal sym w))
   -> IO (PartExpr (Pred sym) (LLVMVal sym w))
applyCtorFLLVMVal sym _w ctor =
  case ctor of
    G.ConcatBV low_w  (PE p1 (LLVMValInt low_w' low))
               high_w (PE p2 (LLVMValInt high_w' high))
       | fromIntegral (low_w*8)  == natValue low_w' &&
         fromIntegral (high_w*8) == natValue high_w' -> do
            bv <- bvConcat sym high low
            Just LeqProof <- return $ isPosNat (addNat high_w' low_w')
            p <- andPred sym p1 p2
            return $ PE p $ LLVMValInt (addNat high_w' low_w') bv
    G.ConsArray tp (PE p1 hd) n (PE p2 (LLVMValArray tp' vec))
       | tp == tp' && n == fromIntegral (V.length vec) -> do
          p <- andPred sym p1 p2
          return $ PE p $ LLVMValArray tp' (V.cons hd vec)
    G.AppendArray tp n1 (PE p1 (LLVMValArray tp1 v1)) n2 (PE p2 (LLVMValArray tp2 v2))
       | tp == tp1 && tp == tp2 &&
         n1 == fromIntegral (V.length v1) &&
         n2 == fromIntegral (V.length v2) -> do
           p <- andPred sym p1 p2
           return $ PE p $ LLVMValArray tp (v1 V.++ v2)
    G.MkArray tp vec -> do
       let f :: PartExpr (Pred sym) (LLVMVal sym w) -> StateT (Pred sym) (MaybeT IO) (LLVMVal sym w)
           f Unassigned = mzero
           f (PE p1 x) = do
               p0 <- get
               p <- liftIO $ andPred sym p0 p1
               put p
               return x
       x <- runMaybeT $ flip runStateT (truePred sym) $ (traverse f vec)
       case x of
         Nothing -> return $ Unassigned
         Just (vec',p) -> return $ PE p $ LLVMValArray tp vec'

    G.MkStruct vec -> do
       let f :: (G.Field G.Type, PartExpr (Pred sym) (LLVMVal sym w))
             -> StateT (Pred sym) (MaybeT IO) (G.Field G.Type, LLVMVal sym w)
           f (_fld, Unassigned) = mzero
           f (fld, PE p1 x) = do
               p0 <- get
               p <- liftIO $ andPred sym p0 p1
               put p
               return (fld, x)
       x <- runMaybeT $ flip runStateT (truePred sym) $ (traverse f vec)
       case x of
         Nothing -> return $ Unassigned
         Just (vec',p) -> return $ PE p $ LLVMValStruct vec'

    _ -> return $ Unassigned

    -- G.BVToFloat _ ->
    --    fail "applyCtoreFLLVMVal: Floating point values not supported"
    -- G.BVToDouble _ ->
    --    fail "applyCtoreFLLVMVal: Floating point values not supported"


applyViewFLLVMVal
   :: (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> G.ViewF (PartExpr (Pred sym) (LLVMVal sym w))
   -> IO (PartExpr (Pred sym) (LLVMVal sym w))
applyViewFLLVMVal sym _wptr v =
  case v of
    G.SelectLowBV low hi (PE p (LLVMValInt w bv))
      | Just (Some (low_w)) <- someNat (fromIntegral low)
      , Just (Some (hi_w))  <- someNat (fromIntegral hi)
      , Just LeqProof <- isPosNat low_w
      , Just Refl <- testEquality (addNat low_w hi_w) w
      , Just LeqProof <- testLeq low_w w
      -> do
        bv' <- bvSelect sym (knownNat :: NatRepr 0) low_w bv
        return $ PE p $ LLVMValInt low_w bv'
    G.SelectHighBV low hi (PE p (LLVMValInt w bv))
      | Just (Some (low_w)) <- someNat (fromIntegral low)
      , Just (Some (hi_w))  <- someNat (fromIntegral hi)
      , Just LeqProof <- isPosNat hi_w
      , Just Refl <- testEquality (addNat low_w hi_w) w
      -> do
        bv' <- bvSelect sym low_w hi_w bv
        return $ PE p $ LLVMValInt hi_w bv'
    G.FloatToBV _ ->
      return $ Unassigned
      --fail "applyViewFLLVM: Floating point values not supported"
    G.DoubleToBV _ ->
      return $ Unassigned
      --fail "applyViewFLLVM: Floating point values not supported"
    G.ArrayElt sz tp idx (PE p (LLVMValArray tp' vec))
      | sz == fromIntegral (V.length vec)
      , 0 <= idx
      , idx < sz
      , tp == tp' ->
        return $ PE p $ (vec V.! fromIntegral idx)
    G.FieldVal flds idx (PE p (LLVMValStruct vec))
      | flds == fmap fst vec
      , 0 <= idx
      , idx < V.length vec ->
          return $ PE p $ snd $ (vec V.! idx)
    _ -> return Unassigned

muxLLVMVal :: forall sym w
    . (1 <= w, IsSymInterface sym)
   => sym
   -> NatRepr w
   -> Pred sym
   -> PartExpr (Pred sym) (LLVMVal sym w)
   -> PartExpr (Pred sym) (LLVMVal sym w)
   -> IO (PartExpr (Pred sym) (LLVMVal sym w))
muxLLVMVal sym _w p = mux
 where
   mux Unassigned Unassigned = return Unassigned
   mux Unassigned (PE p2 y)  = PE <$> (itePred sym p (falsePred sym) p2) <*> return y
   mux (PE p1 x) Unassigned  = PE <$> (itePred sym p p1 (falsePred sym)) <*> return x
   mux (PE p1 x) (PE p2 y) = do
     mz <- runMaybeT $ muxval x y
     case mz of
       Nothing -> return $ Unassigned
       Just z  -> PE <$> itePred sym p p1 p2 <*> return z

   muxval :: LLVMVal sym w -> LLVMVal sym w -> MaybeT IO (LLVMVal sym w)

   muxval (LLVMValPtr base1 end1 off1) (LLVMValPtr base2 end2 off2) = do
     base <- liftIO $ natIte sym p base1 base2
     end  <- liftIO $ bvIte sym p end1 end2
     off  <- liftIO $ bvIte sym p off1 off2
     return $ LLVMValPtr base end off

   muxval (LLVMValFunPtr args1 ret1 h1) (LLVMValFunPtr args2 ret2 h2)
     | Just Refl <- testEquality args1 args2
     , Just Refl <- testEquality ret1 ret2 = do
        h' <- liftIO $ muxHandle sym p h1 h2
        return $ LLVMValFunPtr args1 ret1 h'

   muxval (LLVMValReal x) (LLVMValReal y) = do
     z  <- liftIO $ realIte sym p x y
     return $ LLVMValReal z

   muxval (LLVMValInt wx x) (LLVMValInt wy y)
     | Just Refl <- testEquality wx wy = do
         z <- liftIO $ bvIte sym p x y
         return $ LLVMValInt wx z

   muxval (LLVMValStruct fls1) (LLVMValStruct fls2)
     | fmap fst fls1 == fmap fst fls2 = do
         fls <- traverse id $ V.zipWith (\(f,x) (_,y) -> (f,) <$> muxval x y) fls1 fls2
         return $ LLVMValStruct fls

   muxval (LLVMValArray tp1 v1) (LLVMValArray tp2 v2)
     | tp1 == tp2 && V.length v1 == V.length v2 = do
         v <- traverse id $ V.zipWith muxval v1 v2
         return $ LLVMValArray tp1 v

   muxval _ _ = mzero


-- | Load a null-terminated string from the memory.  The pointer to read from
-- must be concrete and nonnull.  Moreover, we require all the characters in
-- the string to be concrete.  Otherwise it is very difficult to tell when the string
-- has terminated.  If a maximum number of characters is provided, no more than that
-- number of charcters will be read.  In either case, `loadString` will stop reading
-- if it encounters a null-terminator.
loadString :: forall sym
   . IsSymInterface sym
  => sym
  -> RegValue sym Mem -- ^ memory to read from
  -> RegValue sym LLVMPointerType -- ^ pointer to string value
  -> Maybe Int -- ^ maximum characters to read
  -> IO [Word8]
loadString sym mem = go id
 where
  go :: ([Word8] -> [Word8]) -> RegValue sym LLVMPointerType -> Maybe Int -> IO [Word8]
  go f _ (Just 0) = return $ f []
  go f p maxChars = do
     v <- doLoad sym mem p (G.bitvectorType 1) -- one byte
     case v of
       AnyValue (BVRepr w) x
         | Just Refl <- testEquality w (knownNat :: NatRepr 8) ->
            case asUnsignedBV x of
              Just 0 -> return $ f []
              Just c -> do
                  let c' :: Word8 = toEnum $ fromInteger c
                  p' <- doPtrAddOffset sym p =<< bvLit sym ptrWidth 1
                  go (f . (c':)) p' (fmap (\n -> n - 1) maxChars)
              Nothing ->
                fail "Symbolic value encountered when loading a string"
       _ -> fail "Invalid value encountered when loading a string"


-- | Like 'loadString', except the pointer to load may be null.  If
--   the pointer is null, we return Nothing.  Otherwise we load
--   the string as with 'loadString' and return it.
loadMaybeString :: forall sym
   . IsSymInterface sym
  => sym
  -> RegValue sym Mem -- ^ memory to read from
  -> RegValue sym LLVMPointerType -- ^ pointer to string value
  -> Maybe Int -- ^ maximum characters to read
  -> IO (Maybe [Word8])
loadMaybeString sym mem ptr n = do
  isnull <- isNullPointer sym ptr
  case asConstantPred isnull of
    Nothing    -> fail "Symbolic pointer encountered when loading a string"
    Just True  -> return Nothing
    Just False -> Just <$> loadString sym mem ptr n
