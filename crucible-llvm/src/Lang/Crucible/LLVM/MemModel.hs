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
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Lang.Crucible.LLVM.MemModel
  ( LLVMPointerType
  , llvmPointerRepr
  , pattern LLVMPointerRepr
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
  , GlobalMap
  , GlobalSymbol(..)
  , allocGlobals
  , registerGlobal
  , assertDisjointRegions
  , assertDisjointRegions'
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
  , SomeFnHandle(..)

  -- * Direct API to LLVMVal
  , LLVMVal(..)
  , LLVMPtr(..)
  , coerceAny
  , unpackMemValue
  , packMemValue
  , loadRaw
  , loadRawWithCondition
  , storeRaw
  , mallocRaw
  ) where

import           Control.Lens
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

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Vector as V
import qualified Text.LLVM.AST as L


import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Common
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import qualified Lang.Crucible.Syntax as S
import           Lang.Crucible.LLVM.DataLayout
import qualified Lang.Crucible.LLVM.MemModel.Common as G
import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import           Lang.Crucible.LLVM.MemModel.Pointer

--import Debug.Trace as Debug


type PtrWidth = 64
ptrWidth :: NatRepr PtrWidth
ptrWidth = knownNat

type LLVMPointerType = RecursiveType "LLVM_pointer"
llvmPointerRepr :: TypeRepr LLVMPointerType
llvmPointerRepr = knownRepr

pattern LLVMPointerRepr :: () => (ty ~ LLVMPointerType) => TypeRepr ty
pattern LLVMPointerRepr <- RecursiveRepr (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
  where
    LLVMPointerRepr = llvmPointerRepr

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
nullPointer = S.app $ RollRecursive knownSymbol $ S.app $ MkStruct
  (Ctx.empty Ctx.%> NatRepr
             Ctx.%> BVRepr ptrWidth
             Ctx.%> BVRepr ptrWidth)
  (Ctx.empty Ctx.%> (S.app (NatLit 0))
             Ctx.%> (S.app (BVLit ptrWidth 0))
             Ctx.%> (S.app (BVLit ptrWidth 0)))

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
  , llvmMemVar    :: GlobalVar Mem
  , llvmMemAlloca :: FnHandle (EmptyCtx ::> Mem ::> BVType PtrWidth ::> StringType)
                              (StructType (EmptyCtx ::> Mem ::> LLVMPointerType))
  , llvmMemPushFrame :: FnHandle (EmptyCtx ::> Mem) Mem
  , llvmMemPopFrame :: FnHandle (EmptyCtx ::> Mem) Mem
  , llvmMemLoad  :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType) AnyType
  , llvmMemStore :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType ::> AnyType) Mem
  , llvmMemLoadHandle :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType) AnyType
  , llvmResolveGlobal :: FnHandle (EmptyCtx ::> Mem ::> ConcreteType GlobalSymbol) LLVMPointerType
  , llvmPtrEq :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
  , llvmPtrLe :: FnHandle (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
  , llvmPtrAddOffset :: FnHandle (EmptyCtx ::> LLVMPointerType ::> BVType PtrWidth) LLVMPointerType
  , llvmPtrSubtract :: FnHandle (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType) (BVType PtrWidth)
  , llvmPtrIsNull :: FnHandle (EmptyCtx ::> LLVMPointerType) BoolType
  }

llvmMemIntrinsics :: IsSymInterface sym
                  => LLVMMemOps
                  -> [FnBinding p sym]
llvmMemIntrinsics memOps =
  [ useIntrinsic (llvmMemAlloca memOps)
                 memAlloca
  , useIntrinsic (llvmMemLoad memOps)
                 memLoad
  , useIntrinsic (llvmMemStore memOps)
                 memStore
  , useIntrinsic (llvmMemLoadHandle memOps)
                 memLoadHandle
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
  memVar      <- freshGlobalVar halloc "llvm_memory" knownRepr
  alloca      <- mkHandle halloc "llvm_alloca"
  pushFrame   <- mkHandle halloc "llvm_pushFrame"
  popFrame    <- mkHandle halloc "llvm_popFrame"
  load        <- mkHandle halloc "llvm_load"
  store       <- mkHandle halloc "llvm_store"
  loadHandle  <- mkHandle halloc "llvm_load_handle"
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
            , llvmMemLoadHandle  = loadHandle
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
  , memImplHeap        :: G.Mem sym w
  }

-- NB block numbers start counting at 1 because the null pointer
-- uses distinguished block 0
emptyMem :: IO (MemImpl sym w)
emptyMem = do
  blkRef <- newIORef 1
  return $ MemImpl (BlockSource blkRef) Map.empty Map.empty G.emptyMem

type GlobalMap sym = Map L.Symbol (RegValue sym LLVMPointerType)

-- | Allocate memory for each global, and register all the resulting
-- pointers in the 'GlobalMap'.
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
allocGlobal sym mem (symbol, sz) = do
  sz' <- bvLit sym ptrWidth (fromIntegral sz)
  (ptr, mem') <- doMalloc sym mem sz'
  return (registerGlobal mem' symbol ptr)

-- | Add an entry to the 'GlobalMap' of the given 'MemImpl'.
registerGlobal :: MemImpl sym PtrWidth
               -> L.Symbol
               -> RegValue sym LLVMPointerType
               -> MemImpl sym PtrWidth
registerGlobal (MemImpl blockSource gMap hMap mem) symbol ptr =
  let gMap' = Map.insert symbol ptr gMap
  in MemImpl blockSource gMap' hMap mem

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

memResolveGlobal :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> ConcreteType GlobalSymbol) LLVMPointerType
memResolveGlobal = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> (GlobalSymbol symbol)) -> liftIO $ doResolveGlobal sym mem symbol

memLoad :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType) AnyType
memLoad = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> ptr)
  (regValue -> valType) ->
    liftIO $ doLoad sym mem ptr valType

ppMem
  :: IsSymInterface sym
  => sym
  -> RegValue sym Mem
  -> Doc
ppMem _sym mem = G.ppMem (memImplHeap mem)

doDumpMem :: IsSymInterface sym
  => sym
  -> Handle
  -> RegValue sym Mem
  -> IO ()
doDumpMem sym h mem = do
  hPutStrLn h (show (ppMem sym mem))


loadRaw :: IsSymInterface sym
        => sym
        -> MemImpl sym PtrWidth
        -> LLVMPtr sym PtrWidth
        -> G.Type
        -> IO (LLVMVal sym PtrWidth)
loadRaw sym mem ptr valType =
  do res <- loadRawWithCondition sym mem ptr valType
     case res of
       Right (p,r,v) -> v <$ addAssertion sym p r
       Left e        -> fail e


-- | Load an LLVM value from memory. This version of 'loadRaw'
-- returns the side-conditions explicitly so that they can
-- be conditionally asserted.
loadRawWithCondition ::
  IsSymInterface sym   =>
  sym                  ->
  MemImpl sym PtrWidth {- ^ LLVM heap       -} ->
  LLVMPtr sym PtrWidth {- ^ pointer         -} ->
  G.Type               {- ^ pointed-to type -} ->
  IO (Either
        String
        (Pred sym, SimErrorReason, LLVMVal sym PtrWidth))
  -- ^ Either error message or
  -- (assertion, assertion failure description, dereferenced value)
loadRawWithCondition sym mem ptr valType =
  do (p,v) <- G.readMem sym ptrWidth ptr valType (memImplHeap mem)
     let errMsg = "Invalid memory load: address " ++ show (G.ppLLVMPtr ptr) ++
                  " at type "                     ++ show (G.ppType valType)
     case v of
       Unassigned -> return (Left errMsg)
       PE p' v' ->
         do p'' <- andPred sym p p'
            return (Right (p'', AssertFailureSimError errMsg, v'))

doLoad :: IsSymInterface sym
  => sym
  -> RegValue sym Mem
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMValTypeType
  -> IO (RegValue sym AnyType)
doLoad sym mem ptr valType = do
    --putStrLn "MEM LOAD"
    let ptr' = translatePtr ptr
        errMsg = "Invalid memory load: address " ++ show (ppPtr ptr) ++
                 " at type " ++ show (G.ppType valType)
    (p, v) <- G.readMem sym ptrWidth ptr' valType (memImplHeap mem)
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
  -> LLVMPtr sym PtrWidth
  -> G.Type
  -> LLVMVal sym PtrWidth
  -> IO (MemImpl sym PtrWidth)
storeRaw sym mem ptr valType val = do
    (p, heap') <- G.writeMem sym ptrWidth ptr valType (PE (truePred sym) val) (memImplHeap mem)
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
    (p, heap') <- G.writeMem sym ptrWidth ptr' valType (PE (truePred sym) val') (memImplHeap mem)
    addAssertion sym p (AssertFailureSimError "Invalid memory store")
    return mem{ memImplHeap = heap' }

memStore :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMValTypeType ::> AnyType) Mem
memStore = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> ptr)
  (regValue -> valType)
  (regValue -> val) ->
     liftIO $ doStore sym mem ptr valType val

data SomeFnHandle where
  SomeFnHandle :: FnHandle args ret -> SomeFnHandle

memLoadHandle :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> LLVMPointerType) AnyType
memLoadHandle = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> ptr) ->
     do mhandle <- liftIO $ doLookupHandle sym mem ptr
        case mhandle of
          Nothing -> fail "memLoadHandle: not a valid function pointer"
          Just (SomeFnHandle h) ->
            do let ty = FunctionHandleRepr (handleArgTypes h) (handleReturnType h)
               return (AnyValue ty (HandleFnVal h))

memAlloca :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> BVType PtrWidth ::> StringType)
                           (StructType (EmptyCtx ::> Mem ::> LLVMPointerType))
memAlloca = mkIntrinsic $ \_ sym
  (regValue -> mem)
  (regValue -> sz)
  (regValue -> loc) -> do
     liftIO $ do
       --sz_doc <- printSymExpr sym sz
       --putStrLn $ unwords ["MEM ALLOCA:", show nextBlock, show sz_doc]

     blkNum <- nextBlock (memImplBlockSource mem)
     blk <- liftIO $ natLit sym (fromIntegral blkNum)
     z <- liftIO $ bvLit sym ptrWidth 0

     let heap' = G.allocMem G.StackAlloc (fromInteger blkNum) sz (show loc) (memImplHeap mem)
     let ptr = RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV sz Ctx.%> RV z)
     return (Ctx.empty Ctx.%> (RV $ mem{ memImplHeap = heap' }) Ctx.%> RV ptr)

memPushFrame :: IntrinsicImpl p sym (EmptyCtx ::> Mem) Mem
memPushFrame = mkIntrinsic $ \_ _sym
  (regValue -> mem) -> do
     --liftIO $ putStrLn "MEM PUSH FRAME"
     let heap' = G.pushStackFrameMem (memImplHeap mem)
     return mem{ memImplHeap = heap' }

memPopFrame :: IntrinsicImpl p sym (EmptyCtx ::> Mem) Mem
memPopFrame = mkIntrinsic $ \_ _sym
  (regValue -> mem) -> do
     --liftIO $ putStrLn "MEM POP FRAME"
     let heap' = G.popStackFrameMem (memImplHeap mem)
     return $ mem{ memImplHeap = heap' }


translatePtr :: RegValue sym LLVMPointerType
             -> LLVMPtr sym PtrWidth
translatePtr (RolledType xs) =
   let RV blk = xs^._1 in
   let RV end = xs^._2 in
   let RV off = xs^._3 in
   LLVMPtr blk end off


translatePtrBack :: LLVMPtr sym PtrWidth
                 -> IO (RegValue sym LLVMPointerType)
translatePtrBack (LLVMPtr blk end off) =
  return $ RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV end Ctx.%> RV off)

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
  :: (1 <= w, IsSymInterface sym)
  => String -- ^ label used for error message
  -> sym
  -> NatRepr w
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType w)
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType w)
  -> IO ()
assertDisjointRegions' lbl sym w dest dlen src slen = do
  let LLVMPtr dblk _ doff = translatePtr dest
  let LLVMPtr sblk _ soff = translatePtr src

  dend <- bvAdd sym doff =<< sextendBVTo sym w ptrWidth dlen
  send <- bvAdd sym soff =<< sextendBVTo sym w ptrWidth slen

  diffBlk   <- notPred sym =<< natEq sym dblk sblk
  destfirst <- bvSle sym dend soff
  srcfirst  <- bvSle sym send doff

  c <- orPred sym diffBlk =<< orPred sym destfirst srcfirst

  addAssertion sym c
     (AssertFailureSimError ("Memory regions not disjoint in " ++ lbl))

-- | Simpler interface to 'assertDisjointRegions'' where the lengths
-- of the two regions are equal as used by the memcpy operation.
assertDisjointRegions
  :: (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> RegValue sym LLVMPointerType
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType w)
  -> IO ()
assertDisjointRegions sym w dest src len =
  assertDisjointRegions' "memcpy" sym w dest len src len


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

  let heap' = G.allocMem G.HeapAlloc (fromInteger blkNum) sz "<malloc>" (memImplHeap mem)
  let ptr = RolledType (Ctx.empty Ctx.%> RV blk Ctx.%> RV sz Ctx.%> RV z)
  return (ptr, mem{ memImplHeap = heap' })

mallocRaw
  :: IsSymInterface sym
  => sym
  -> MemImpl sym PtrWidth
  -> SymExpr sym (BaseBVType PtrWidth)
  -> IO (LLVMPtr sym PtrWidth, MemImpl sym PtrWidth)
mallocRaw sym mem sz = do
  blkNum <- nextBlock (memImplBlockSource mem)
  blk <- natLit sym (fromIntegral blkNum)
  z <- bvLit sym ptrWidth 0

  let ptr = LLVMPtr blk sz z
  let heap' = G.allocMem G.HeapAlloc (fromInteger blkNum) sz "<malloc>" (memImplHeap mem)
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

  let heap' = G.allocMem G.HeapAlloc (fromInteger blkNum) z "<malloc>" (memImplHeap mem)
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
  let ptr'@(LLVMPtr blk _ _) = translatePtr ptr
  (c, heap') <- G.freeMem sym ptrWidth ptr' (memImplHeap mem)

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
      (c, heap') <- G.writeMem sym ptrWidth (translatePtr dest) tp arr (memImplHeap mem)
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
  len' <- sextendBVTo sym w ptrWidth len

  (c, heap') <- G.copyMem sym ptrWidth dest' src' len' (memImplHeap mem)

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

ppAllocs :: IsSymInterface sym => sym -> [G.MemAlloc sym PtrWidth] -> IO Doc
ppAllocs sym xs = vcat <$> mapM ppAlloc xs
 where ppAlloc (G.Alloc allocTp base sz loc) = do
            let base_doc = text (show base)
            let sz_doc   = printSymExpr sz
            return $ text (show allocTp) <+> base_doc <+> text "SIZE:" <+> sz_doc <+> text loc
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


ptrAddOffsetOverride :: IntrinsicImpl p sym (EmptyCtx ::> LLVMPointerType ::> BVType PtrWidth) LLVMPointerType
ptrAddOffsetOverride = mkIntrinsic $ \_ sym
   (regValue -> x)
   (regValue -> off) ->
     liftIO $ doPtrAddOffset sym x off

ptrSubtractOverride :: IntrinsicImpl p sym (EmptyCtx ::> LLVMPointerType ::> LLVMPointerType) (BVType PtrWidth)
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
   ptrDiff sym ptrWidth px py

doPtrAddOffset
  :: IsSymInterface sym
  => sym
  -> RegValue sym LLVMPointerType
  -> RegValue sym (BVType PtrWidth)
  -> IO (RegValue sym LLVMPointerType)
doPtrAddOffset sym x off = do
      let px = translatePtr x
      (v, p') <- ptrCheckedAdd sym ptrWidth px off
      let x_doc = ppPtr x
      let off_doc = printSymExpr off
      addAssertion sym v
         (AssertFailureSimError $ unlines ["Pointer arithmetic resulted in invalid pointer:", show x_doc, show off_doc])
      translatePtrBack p'

ptrEqOverride :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
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

ptrLeOverride :: IntrinsicImpl p sym (EmptyCtx ::> Mem ::> LLVMPointerType ::> LLVMPointerType) BoolType
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

ptrIsNullOverride :: IntrinsicImpl p sym (EmptyCtx ::> LLVMPointerType) BoolType
ptrIsNullOverride = mkIntrinsic $ \_ sym
  (regValue -> x) -> liftIO $ ptrIsNull sym x

isValidPointer :: IsSymInterface sym => sym
               -> RegValue sym LLVMPointerType
               -> RegValue sym Mem
               -> IO (Pred sym)
isValidPointer sym p mem = do
   c1 <- ptrIsNull sym p
   c2 <- G.isValidPointer sym ptrWidth (translatePtr p) (memImplHeap mem)
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


instance Show (LLVMVal sym w) where
  show (LLVMValPtr _ _ _) = "<ptr>"
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
