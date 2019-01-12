------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Generic
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.MemModel.Generic
  ( Mem
  , emptyMem
  , AllocType(..)
  , Mutability(..)
  , MemAlloc(..)
  , memAllocs
  , memEndian
  , allocMem
  , allocAndWriteMem
  , readMem
  , isValidPointer
  , isAligned
  , notAliasable
  , writeMem
  , writeConstMem
  , copyMem
  , setMem
  , writeArrayMem
  , writeArrayConstMem
  , pushStackFrameMem
  , popStackFrameMem
  , freeMem
  , branchMem
  , branchAbortMem
  , mergeMem

    -- * Pretty printing
  , ppType
  , ppPtr
  , ppAlloc
  , ppAllocs
  , ppMem
  ) where

import Control.Lens
import Control.Monad
import Data.IORef
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as V
import Numeric.Natural
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Data.Parameterized.Classes
import Data.Parameterized.Ctx (SingleCtx)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some

import What4.Interface
import What4.Partial

import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.LLVM.MemModel.Type
import Lang.Crucible.LLVM.MemModel.Common
import Lang.Crucible.LLVM.MemModel.Pointer
import Lang.Crucible.LLVM.MemModel.Value
import Lang.Crucible.Backend


--import Debug.Trace as Debug

data AllocType = StackAlloc | HeapAlloc | GlobalAlloc
  deriving (Show)

data Mutability = Mutable | Immutable
  deriving (Eq, Show)

-- | Stores writeable memory allocations.
data MemAlloc sym
     -- | Allocation with given block ID and number of bytes. The
     -- 'Mutability' indicates whether the region is read-only. The
     -- 'String' contains source location information for use in error
     -- messages.
   = forall w. Alloc AllocType Natural (SymBV sym w) Mutability Alignment String
     -- | Freeing of the given block ID.
   | MemFree (SymNat sym)
     -- | The merger of two allocations.
   | AllocMerge (Pred sym) [MemAlloc sym] [MemAlloc sym]

data WriteSource sym w
    -- | @MemCopy src len@ copies @len@ bytes from [src..src+len).
  = MemCopy (LLVMPtr sym w) (SymBV sym w)
    -- | @MemSet val len@ fills the destination with @len@ copies of byte @val@.
  | MemSet (SymBV sym 8) (SymBV sym w)
    -- | @MemStore val ty al@ writes value @val@ with type @ty@ at the destination.
    --   with alignment at least @al@.
  | MemStore (LLVMVal sym) StorageType Alignment
    -- | @MemStoreBlock block len@ writes byte-array @block@ of size @len@
    -- at the destination.
  | MemArrayStore (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8)) (SymBV sym w)

data MemWrite sym
    -- | @MemWrite dst src@ represents a write to @dst@ from the given source.
  = forall w. MemWrite (LLVMPtr sym w) (WriteSource sym w)
    -- | The merger of two memories.
  | WriteMerge (Pred sym) [MemWrite sym] [MemWrite sym]

--------------------------------------------------------------------------------
-- Reading from memory

tgAddPtrC :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> LLVMPtr sym w -> Addr -> IO (LLVMPtr sym w)
tgAddPtrC sym w x y = ptrAdd sym w x =<< constOffset sym w y

genOffsetExpr ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  (SymBV sym w, SymBV sym w, SymBV sym w) ->
  OffsetExpr -> IO (SymBV sym w)
genOffsetExpr sym w f@(load, store, _size) expr =
  case expr of
    OffsetAdd pe ie -> do
      pe' <- genOffsetExpr sym w f pe
      ie' <- genIntExpr sym w f ie
      bvAdd sym pe' ie'
    Load -> return load
    Store -> return store

genIntExpr ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  (SymBV sym w, SymBV sym w, SymBV sym w) ->
  IntExpr -> IO (SymBV sym w)
genIntExpr sym w f@(_load, _store, size) expr =
  case expr of
    OffsetDiff e1 e2 -> do
      e1' <- genOffsetExpr sym w f e1
      e2' <- genOffsetExpr sym w f e2
      bvSub sym e1' e2'
    IntAdd e1 e2 -> do
      e1' <- genIntExpr sym w f e1
      e2' <- genIntExpr sym w f e2
      bvAdd sym e1' e2'
    CValue i -> bvLit sym w (bytesToInteger i)
    StoreSize -> return size

genCondVar ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  (SymBV sym w, SymBV sym w, SymBV sym w) ->
  Cond -> IO (Pred sym)
genCondVar sym w inst c =
  case c of
    OffsetEq x y   -> join $ bvEq sym <$> genOffsetExpr sym w inst x <*> genOffsetExpr sym w inst y
    OffsetLe x y   -> join $ bvUle sym <$> genOffsetExpr sym w inst x <*> genOffsetExpr sym w inst y
    IntEq x y      -> join $ bvEq sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    IntLe x y      -> join $ bvSle sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    And x y        -> join $ andPred sym <$> genCondVar sym w inst x <*> genCondVar sym w inst y
    Or x y         -> join $ orPred sym <$> genCondVar sym w inst x <*> genCondVar sym w inst y

genValueCtor :: forall sym .
  IsSymInterface sym => sym ->
  EndianForm ->
  ValueCtor (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
genValueCtor sym end v =
  case v of
    ValueCtorVar x -> return x
    ConcatBV vcl vch ->
      do vl <- genValueCtor sym end vcl
         vh <- genValueCtor sym end vch
         case end of
           BigEndian    -> bvConcatPartLLVMVal sym vh vl
           LittleEndian -> bvConcatPartLLVMVal sym vl vh
    ConsArray vc1 vc2 ->
      do lv1 <- genValueCtor sym end vc1
         lv2 <- genValueCtor sym end vc2
         consArrayPartLLVMVal sym lv1 lv2
    AppendArray vc1 vc2 ->
      do lv1 <- genValueCtor sym end vc1
         lv2 <- genValueCtor sym end vc2
         appendArrayPartLLVMVal sym lv1 lv2
    MkArray tp vv ->
      do vec <- traverse (genValueCtor sym end) vv
         mkArrayPartLLVMVal sym tp vec
    MkStruct vv ->
      do vec <- traverse (traverse (genValueCtor sym end)) vv
         mkStructPartLLVMVal sym vec
    BVToFloat x ->
      bvToFloatPartLLVMVal sym =<< genValueCtor sym end x
    BVToDouble x ->
      bvToDoublePartLLVMVal sym =<< genValueCtor sym end x
    BVToX86_FP80 x ->
      bvToX86_FP80PartLLVMVal sym =<< genValueCtor sym end x

-- | Compute the actual value of a value deconstructor expression.
applyView ::
  IsSymInterface sym => sym ->
  EndianForm ->
  PartLLVMVal sym ->
  ValueView ->
  IO (PartLLVMVal sym)
applyView sym end t val =
  case val of
    ValueViewVar _ ->
      return t
    SelectPrefixBV i j v ->
      do t' <- applyView sym end t v
         case end of
           BigEndian -> selectHighBvPartLLVMVal sym j i t'
           LittleEndian -> selectLowBvPartLLVMVal sym i j t'
    SelectSuffixBV i j v ->
      do t' <- applyView sym end t v
         case end of
           BigEndian -> selectLowBvPartLLVMVal sym j i t'
           LittleEndian -> selectHighBvPartLLVMVal sym i j t'
    FloatToBV _ ->
      return Unassigned
      --fail "applyView: Floating point values not supported"
    DoubleToBV _ ->
      return Unassigned
      --fail "applyView: Floating point values not supported"
    X86_FP80ToBV _ ->
      return Unassigned
    ArrayElt sz tp idx v ->
      arrayEltPartLLVMVal sz tp idx =<< applyView sym end t v
    FieldVal flds idx v ->
      fieldValPartLLVMVal flds idx =<< applyView sym end t v

evalMuxValueCtor ::
  forall u sym w .
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  EndianForm ->
  (SymBV sym w, SymBV sym w, SymBV sym w) {- ^ Evaluation function -} ->
  (u -> IO (PartLLVMVal sym)) {- ^ Function for reading specific subranges -} ->
  Mux (ValueCtor u) ->
  IO (PartLLVMVal sym)
evalMuxValueCtor sym _w end _vf subFn (MuxVar v) =
  do v' <- traverse subFn v
     genValueCtor sym end v'
evalMuxValueCtor sym w end vf subFn (Mux c t1 t2) =
  do c' <- genCondVar sym w vf c
     case asConstantPred c' of
       Just True  -> evalMuxValueCtor sym w end vf subFn t1
       Just False -> evalMuxValueCtor sym w end vf subFn t2
       Nothing ->
        do t1' <- evalMuxValueCtor sym w end vf subFn t1
           t2' <- evalMuxValueCtor sym w end vf subFn t2
           muxLLVMVal sym c' t1' t2'

evalMuxValueCtor sym w end vf subFn (MuxTable a b m t) =
  do m' <- traverse (evalMuxValueCtor sym w end vf subFn) m
     t' <- evalMuxValueCtor sym w end vf subFn t
     result <- Map.foldrWithKey f (return t') m'
     p' <- simplPred (Map.assocs (fmap predOf m')) (predOf t')
     case result of
       Unassigned -> return Unassigned
       PE _ v     -> return (PE p' v) -- replace predicate with simplified one
  where
    f :: Bytes -> PartLLVMVal sym -> IO (PartLLVMVal sym) -> IO (PartLLVMVal sym)
    f n t1 k =
      do c' <- genCondVar sym w vf (OffsetEq (aOffset n) b)
         case asConstantPred c' of
           Just True -> return t1
           Just False -> k
           Nothing ->
             do t2 <- k
                muxLLVMVal sym c' t1 t2

    aOffset :: Bytes -> OffsetExpr
    aOffset n = OffsetAdd a (CValue n)

    predOf :: PartLLVMVal sym -> Pred sym
    predOf Unassigned = falsePred sym
    predOf (PE p _) = p

    samePred :: Pred sym -> Pred sym -> Bool
    samePred p1 p2 =
      case (asConstantPred p1, asConstantPred p2) of
        (Just b1, Just b2) -> b1 == b2
        _ -> False

    simplPred :: [(Bytes, Pred sym)] -> Pred sym -> IO (Pred sym)
    simplPred [] p0 = return p0
    simplPred ((n, p) : xps) p0 =
      do let (xps1, xps2) = span (samePred p . snd) xps
         let c = if null xps1
                 then OffsetEq (aOffset n) b
                 else And (OffsetLe (aOffset n) b)
                          (OffsetLe b (aOffset (fst (last xps1))))
         c' <- genCondVar sym w vf c
         case asConstantPred c' of
           Just True -> return p
           Just False -> simplPred xps2 p0
           Nothing ->
             do p' <- simplPred xps2 p0
                itePred sym c' p p'

-- | Read from a memory with a memcopy to the same block we are reading.
readMemCopy ::
  forall sym w.
  (1 <= w, IsSymInterface sym) => sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w  {- ^ The loaded offset               -} ->
  StorageType    {- ^ The type we are reading         -} ->
  SymBV sym w    {- ^ The destination of the memcopy  -} ->
  LLVMPtr sym w  {- ^ The source of the copied region -} ->
  SymBV sym w    {- ^ The length of the copied region -} ->
  (StorageType -> LLVMPtr sym w -> IO (PartLLVMVal sym)) ->
  IO (PartLLVMVal sym)
readMemCopy sym w end (LLVMPointer blk off) tp d src sz readPrev =
  do let ld = asUnsignedBV off
     let dd = asUnsignedBV d
     let varFn = (off, d, sz)

     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: RangeLoad Addr Addr -> IO (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do o' <- bvLit sym w (bytesToInteger o)
                                              readPrev tp' (LLVMPointer blk o')
                subFn (InRange    o tp') = readPrev tp' =<< tgAddPtrC sym w src o
            case asUnsignedBV sz of
              Just csz -> do
                let s = R (fromInteger so) (fromInteger (so + csz))
                let vcr = rangeLoad (fromInteger lo) tp s
                genValueCtor sym end =<< traverse subFn vcr
              _ ->
                evalMuxValueCtor sym w end varFn subFn $
                  fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
         -- Symbolic offsets
       _ ->
         do let subFn :: RangeLoad OffsetExpr IntExpr -> IO (PartLLVMVal sym)
                subFn (OutOfRange o tp') =
                  do o' <- genOffsetExpr sym w varFn o
                     readPrev tp' (LLVMPointer blk o')
                subFn (InRange o tp') =
                  readPrev tp' =<< ptrAdd sym w src =<< genIntExpr sym w varFn o
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- asUnsignedBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end varFn subFn mux0


-- | Read from a memory with a memset to the same block we are reading.
readMemSet ::
  forall sym w .
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  EndianForm ->
  LLVMPtr sym w {- ^ The loaded offset             -} ->
  StorageType   {- ^ The type we are reading       -} ->
  SymBV sym w   {- ^ The destination of the memset -} ->
  SymBV sym 8   {- ^ The fill byte that was set    -} ->
  SymBV sym w   {- ^ The length of the set region  -} ->
  (StorageType -> LLVMPtr sym w -> IO (PartLLVMVal sym)) ->
  IO (PartLLVMVal sym)
readMemSet sym w end (LLVMPointer blk off) tp d byte sz readPrev =
  do let ld = asUnsignedBV off
     let dd = asUnsignedBV d
     let varFn = (off, d, sz)
     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: RangeLoad Addr Addr -> IO (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do o' <- bvLit sym w (bytesToInteger o)
                                              readPrev tp' (LLVMPointer blk o')
                subFn (InRange   _o tp') = do blk0 <- natLit sym 0
                                              let val = LLVMValInt blk0 byte
                                              let b = PE (truePred sym) val
                                              genValueCtor sym end (memsetValue b tp')
            case asUnsignedBV sz of
              Just csz ->
                do let s = R (fromInteger so) (fromInteger (so + csz))
                   let vcr = rangeLoad (fromInteger lo) tp s
                   genValueCtor sym end =<< traverse subFn vcr
              _ ->
                evalMuxValueCtor sym w end varFn subFn $
                  fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
       -- Symbolic offsets
       _ ->
         do let subFn :: RangeLoad OffsetExpr IntExpr -> IO (PartLLVMVal sym)
                subFn (OutOfRange o tp') =
                  do o' <- genOffsetExpr sym w varFn o
                     readPrev tp' (LLVMPointer blk o')
                subFn (InRange _o tp') =
                  do blk0 <- natLit sym 0
                     let val = LLVMValInt blk0 byte
                     let b = PE (truePred sym) val
                     genValueCtor sym end (memsetValue b tp')
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- asUnsignedBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end varFn subFn mux0


-- | Read from a memory with a store to the same block we are reading.
readMemStore ::
  forall sym w.
  (1 <= w, IsSymInterface sym) => sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w {- ^ The loaded address                 -} ->
  StorageType   {- ^ The type we are reading            -} ->
  SymBV sym w   {- ^ The destination of the store       -} ->
  LLVMVal sym   {- ^ The value that was stored          -} ->
  StorageType   {- ^ The type of value that was written -} ->
  Alignment     {- ^ The alignment of the pointer we are reading from -} ->
  Alignment     {- ^ The alignment of the store from which we are reading -} ->
  (StorageType -> LLVMPtr sym w -> IO (PartLLVMVal sym))
  {- ^ A callback function for when reading fails -} ->
  IO (PartLLVMVal sym)
readMemStore sym w end (LLVMPointer blk off) ltp d t stp loadAlign storeAlign readPrev =
  do ssz <- bvLit sym w (bytesToInteger (storageTypeSize stp))
     let varFn = (off, d, ssz)
     let ld = asUnsignedBV off
     let dd = asUnsignedBV d
     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: ValueLoad Addr -> IO (PartLLVMVal sym)
                subFn (OldMemory o tp')   = do o' <- bvLit sym w (bytesToInteger o)
                                               readPrev tp' (LLVMPointer blk o')
                subFn (LastStore v)       = applyView sym end (PE (truePred sym) t) v
                subFn (InvalidMemory _tp) = return Unassigned
            let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (ValueViewVar stp)
            genValueCtor sym end =<< traverse subFn vcr
       -- Symbolic offsets
       _ ->
         do let subFn :: ValueLoad OffsetExpr -> IO (PartLLVMVal sym)
                subFn (OldMemory o tp')   = do o' <- genOffsetExpr sym w varFn o
                                               readPrev tp' (LLVMPointer blk o')
                subFn (LastStore v)       = applyView sym end (PE (truePred sym) t) v
                subFn (InvalidMemory _tp) = return Unassigned
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed

            let align' = min loadAlign storeAlign
            diff <- bvSub sym off d

            evalMuxValueCtor sym w end varFn subFn $
              symbolicValueLoad pref ltp (signedBVBounds diff) (ValueViewVar stp) align'

-- | Read from a memory with an array store to the same block we are reading.
readMemArrayStore
  :: forall sym w
   . (1 <= w, IsSymInterface sym)
  => sym
  -> NatRepr w
  -> EndianForm
  -> LLVMPtr sym w {- ^ The loaded offset -}
  -> StorageType {- ^ The type we are reading -}
  -> SymBV sym w {- ^ The destination of the mem array store -}
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ The stored array -}
  -> SymBV sym w {- ^ The length of the stored array -}
  -> (StorageType -> LLVMPtr sym w -> IO (PartLLVMVal sym))
  -> IO (PartLLVMVal sym)
readMemArrayStore sym w end (LLVMPointer blk read_off) tp write_off arr size read_prev = do
  let loadFn :: SymBV sym w -> StorageType -> IO (PartLLVMVal sym)
      loadFn base tp' = do
        let loadArrayByteFn :: Offset -> IO (PartLLVMVal sym)
            loadArrayByteFn off = do
              blk0 <- natLit sym 0
              idx <- bvAdd sym base =<< bvLit sym w (bytesToInteger off)
              byte <- arrayLookup sym arr $ Ctx.singleton idx
              return $ PE (truePred sym) $ LLVMValInt blk0 byte
        genValueCtor sym end =<< loadTypedValueFromBytes 0 tp' loadArrayByteFn
  let varFn = (read_off, write_off, size)
  case (asUnsignedBV read_off, asUnsignedBV write_off) of
    -- known read and write offsets
    (Just lo, Just so) -> do
      let subFn :: RangeLoad Addr Addr -> IO (PartLLVMVal sym)
          subFn = \case
            OutOfRange o tp' -> do
              o' <- bvLit sym w $ bytesToInteger o
              read_prev tp' $ LLVMPointer blk o'
            InRange o tp' -> do
              o' <- bvLit sym w $ bytesToInteger o
              loadFn o' tp'
      case asUnsignedBV size of
        Just concrete_size -> do
          let s = R (fromInteger so) (fromInteger (so + concrete_size))
          let vcr = rangeLoad (fromInteger lo) tp s
          genValueCtor sym end =<< traverse subFn vcr
        _ -> evalMuxValueCtor sym w end varFn subFn $
          fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
    -- Symbolic offsets
    _ -> do
      let subFn :: RangeLoad OffsetExpr IntExpr -> IO (PartLLVMVal sym)
          subFn = \case
            OutOfRange o tp' -> do
              o' <- genOffsetExpr sym w varFn o
              read_prev tp' $ LLVMPointer blk o'
            InRange o tp' -> do
              o' <- genIntExpr sym w varFn o
              loadFn o' tp'
      let pref
            | Just{} <- asUnsignedBV write_off = FixedStore
            | Just{} <- asUnsignedBV read_off = FixedLoad
            | otherwise = NeitherFixed
      evalMuxValueCtor sym w end varFn subFn $ symbolicRangeLoad pref tp

readMem ::
  (1 <= w, IsSymInterface sym) => sym ->
  NatRepr w ->
  LLVMPtr sym w ->
  StorageType ->
  Alignment ->
  Mem sym ->
  IO (PartLLVMVal sym)
readMem sym w l tp alignment m =
  do sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
     p1 <- isAllocated sym w alignment l sz m
     p2 <- isAligned sym w l alignment
     p <- andPred sym p1 p2
     val <- readMem' sym w (memEndianForm m) l tp alignment (memWrites m)
     val' <- andPartVal sym p val
     return val'

andPartVal :: IsSymInterface sym => sym -> Pred sym -> PartLLVMVal sym -> IO (PartLLVMVal sym)
andPartVal sym p val =
  case val of
    Unassigned -> return Unassigned
    PE p' v    -> do p'' <- andPred sym p p'
                     return (PE p'' v)

data CacheEntry sym w =
  CacheEntry !(StorageType) !(SymNat sym) !(SymBV sym w)

instance (TestEquality (SymExpr sym)) => Eq (CacheEntry sym w) where
  (CacheEntry tp1 blk1 off1) == (CacheEntry tp2 blk2 off2) =
    tp1 == tp2 && (isJust $ testEquality blk1 blk2) && (isJust $ testEquality off1 off2)

instance IsSymInterface sym => Ord (CacheEntry sym w) where
  compare (CacheEntry tp1 blk1 off1) (CacheEntry tp2 blk2 off2) =
    compare tp1 tp2
      `mappend` toOrdering (compareF blk1 blk2)
      `mappend` toOrdering (compareF off1 off2)

toCacheEntry :: StorageType -> LLVMPtr sym w -> CacheEntry sym w
toCacheEntry tp (llvmPointerView -> (blk, bv)) = CacheEntry tp blk bv


-- | Read a value from memory given a list of writes.
--
-- This represents a predicate indicating if the read was successful, and the value
-- read (which may be anything if read was unsuccessful).
readMem' ::
  forall w sym.
  (1 <= w, IsSymInterface sym) => sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w  {- ^ Address we are reading            -} ->
  StorageType    {- ^ The type to read from memory      -} ->
  Alignment      {- ^ Alignment of pointer to read from -} ->
  [MemWrite sym] {- ^ List of writes                    -} ->
  IO (PartLLVMVal sym)
readMem' sym w end l0 tp0 alignment = go (\_tp _l -> return Unassigned) l0 tp0
  where
    go :: (StorageType -> LLVMPtr sym w -> IO (PartLLVMVal sym)) ->
          LLVMPtr sym w ->
          StorageType ->
          [MemWrite sym] ->
          IO (PartLLVMVal sym)
    go fallback l tp [] = fallback tp l
    go fallback l tp (h : r) =
      do cache <- newIORef Map.empty
         let readPrev :: StorageType -> LLVMPtr sym w -> IO (PartLLVMVal sym)
             readPrev tp' l' = do
               m <- readIORef cache
               case Map.lookup (toCacheEntry tp' l') m of
                 Just x -> return x
                 Nothing -> do
                   x <- go fallback l' tp' r
                   writeIORef cache $ Map.insert (toCacheEntry tp' l') x m
                   return x
         case h of
           WriteMerge _ [] [] ->
             go fallback l tp r
           WriteMerge c xr yr ->
             do x <- go readPrev l tp xr
                y <- go readPrev l tp yr
                muxLLVMVal sym c x y
           MemWrite dst wsrc ->
             case testEquality (ptrWidth dst) w of
               Nothing   -> readPrev tp l
               Just Refl ->
                 do let LLVMPointer blk1 _ = l
                    let LLVMPointer blk2 d = dst
                    let readCurrent =
                          case wsrc of
                            MemCopy src sz -> readMemCopy sym w end l tp d src sz readPrev
                            MemSet v sz    -> readMemSet sym w end l tp d v sz readPrev
                            MemStore v stp storeAlign -> readMemStore sym w end l tp d v stp alignment storeAlign readPrev
                            MemArrayStore arr sz -> readMemArrayStore sym w end l tp d arr sz readPrev
                    sameBlock <- natEq sym blk1 blk2
                    case asConstantPred sameBlock of
                      Just True -> readCurrent
                      Just False -> readPrev tp l
                      Nothing ->
                        do x <- readCurrent
                           y <- readPrev tp l
                           muxLLVMVal sym sameBlock x y

--------------------------------------------------------------------------------

-- | The state of memory represented as a stack of pushes, branches, and merges.
data Mem sym = Mem { memEndianForm :: EndianForm, _memState :: MemState sym }

memState :: Simple Lens (Mem sym) (MemState sym)
memState = lens _memState (\s v -> s { _memState = v })

-- | A state of memory as of a stack push, branch, or merge.
data MemState sym =
    -- | Represents initial memory and changes since then.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
    EmptyMem (MemChanges sym)
    -- | Represents a push of a stack frame, and changes since that stack push.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | StackFrame (MemChanges sym) (MemState sym)
    -- | Represents a push of a branch frame, and changes since that branch.
    -- Changes are stored in order, with more recent changes closer to the head
    -- of the list.
  | BranchFrame (MemChanges sym) (MemState sym)

type MemChanges sym = ([MemAlloc sym], [MemWrite sym])

memStateLastChanges :: Simple Lens (MemState sym) (MemChanges sym)
memStateLastChanges f s0 =
  case s0 of
    EmptyMem l -> EmptyMem <$> f l
    StackFrame l s  -> flip StackFrame s  <$> f l
    BranchFrame l s -> flip BranchFrame s <$> f l

prependChanges :: MemChanges sym -> MemChanges sym -> MemChanges sym
prependChanges (xa,xw) (ya,yw) = (xa ++ ya, xw ++ yw)

muxChanges :: Pred sym -> MemChanges sym -> MemChanges sym -> MemChanges sym
muxChanges c (xa,xw) (ya,yw) = ([AllocMerge c xa ya], [WriteMerge c xw yw])

memChanges :: (MemChanges sym -> [d]) -> Mem sym -> [d]
memChanges f m = go (m^.memState)
  where go (EmptyMem l)      = f l
        go (StackFrame l s)  = f l ++ go s
        go (BranchFrame l s) = f l ++ go s

memAllocs :: Mem sym -> [MemAlloc sym]
memAllocs = memChanges fst

memWrites :: Mem sym -> [MemWrite sym]
memWrites = memChanges snd

memAddAlloc :: MemAlloc sym -> Mem sym -> Mem sym
memAddAlloc x = memState . memStateLastChanges . _1 %~ (x:)

memAddWrite :: MemWrite sym -> Mem sym -> Mem sym
memAddWrite x = memState . memStateLastChanges . _2 %~ (x:)

emptyChanges :: MemChanges sym
emptyChanges = ([],[])

emptyMem :: EndianForm -> Mem sym
emptyMem e = Mem { memEndianForm = e, _memState = EmptyMem emptyChanges }

memEndian :: Mem sym -> EndianForm
memEndian = memEndianForm

--------------------------------------------------------------------------------
-- Pointer validity

-- | This function is parameterized by a predicate on the mutability, so
-- it can optionally be restricted to mutable regions only.
-- It is also parameterized by a required alignment; only allocations
-- with at least this level of alignment are considered.
isAllocatedMut ::
  forall sym w .
  (1 <= w, IsSymInterface sym) =>
  (Mutability -> Bool) ->
  sym -> NatRepr w     ->
  Alignment            ->
  LLVMPtr sym w        ->
  SymBV sym w          ->
  Mem sym              ->
  IO (Pred sym)
isAllocatedMut mutOk sym w minAlign (llvmPointerView -> (blk, off)) sz m = do
   do (ov, end) <- addUnsignedOF sym off sz
      let step :: forall w'. Natural -> SymBV sym w' -> IO (Pred sym) -> IO (Pred sym)
          step a asz fallback
            -- If the allocation is done at pointer width equal to 'w', check if this
            -- allocation covers the required range.
            | Just Refl <- testEquality w (bvWidth asz) =
                 do sameBlock <- natEq sym blk =<< natLit sym a
                    inRange   <- bvUle sym end asz
                    okNow     <- andPred sym sameBlock inRange
                    case asConstantPred okNow of
                      Just True  -> return okNow
                      Just False -> fallback
                      Nothing    -> orPred sym okNow =<< fallback

            -- If the allocation is done at pointer width not equal to 'w', check that
            -- this allocation is distinct from the base pointer.
            | otherwise =
                 do sameBlock <- natEq sym blk =<< natLit sym a
                    case asConstantPred sameBlock of
                      Just True  -> return (falsePred sym)
                      Just False -> fallback
                      Nothing    ->
                        do notSameBlock <- notPred sym sameBlock
                           andPred sym notSameBlock =<< fallback

      let go :: IO (Pred sym) -> [MemAlloc sym] -> IO (Pred sym)
          go fallback [] = fallback
          go fallback (Alloc _ a asz mut alignment _ : r)
            | mutOk mut && alignment >= minAlign = step a asz (go fallback r)
            | otherwise = go fallback r
          go fallback (MemFree a : r) =
            do sameBlock <- natEq sym blk a
               case asConstantPred sameBlock of
                 Just True  -> return (falsePred sym)
                 Just False -> go fallback r
                 Nothing    ->
                   do notSameBlock <- notPred sym sameBlock
                      andPred sym notSameBlock =<< go fallback r
          go fallback (AllocMerge _ [] [] : r) = go fallback r
          go fallback (AllocMerge c xr yr : r) =
            do p <- go fallback r -- TODO: wrap this in a delay
               px <- go (return p) xr
               py <- go (return p) yr
               itePred sym c px py

      -- It is an error if the offset+size calculation overflows.
      case asConstantPred ov of
        Just True  -> return (falsePred sym)
        Just False -> go (pure (falsePred sym)) (memAllocs m)
        Nothing    ->
          do nov <- notPred sym ov
             andPred sym nov =<< go (pure (falsePred sym)) (memAllocs m)

-- | @isAllocated sym w p sz m@ returns condition required to prove range
-- @[p..p+sz)@ lies within a single allocation in @m@.
--
-- NB this algorithm is set up to explicitly allow both zero size allocations
-- and zero-size chunks to be checked for validity.  When 'sz' is 0, every pointer
-- that is inside the range of the allocation OR ONE PAST THE END are considered
-- "allocated"; this is intended, as it captures C's behavior regarding valid
-- pointers.
isAllocated ::
  forall sym w. (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  Alignment        ->
  LLVMPtr sym w    ->
  SymBV sym w      ->
  Mem sym          ->
  IO (Pred sym)
isAllocated = isAllocatedMut (const True)

isAllocatedMutable ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w -> Alignment -> LLVMPtr sym w -> SymBV sym w -> Mem sym -> IO (Pred sym)
isAllocatedMutable = isAllocatedMut (== Mutable)

-- | @isValidPointer sym w b m@ returns condition required to prove range
--   that @p@ is a valid pointer in @m@.  This means that @p@ is in the
--   range of some allocation OR ONE PAST THE END of an allocation.  In other words
--   @p@ is a valid pointer if @b <= p <= b+sz@ for some allocation
--   at base @b@ of size @sz@.  Note that, even though @b+sz@ is outside the
--   allocation range of the allocation (loading through it will fail) it is
--   nonetheless a valid pointer value.  This strange special case is baked into
--   the C standard to allow certain common coding patterns to be defined.
isValidPointer :: (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w -> LLVMPtr sym w -> Mem sym -> IO (Pred sym)
isValidPointer sym w p m = do
   sz <- constOffset sym w 0
   isAllocated sym w noAlignment p sz m
   -- NB We call isAllocated with a size of 0.

-- | Generate a predicate asserting that the given pointer satisfies
-- the specified alignment constraint.
isAligned ::
  forall sym w .
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w ->
  Alignment ->
  IO (Pred sym)
isAligned sym _w _p a
  | a == noAlignment = return (truePred sym)
isAligned sym w (LLVMPointer _blk offset) a
  | Just (Some bits) <- someNat (alignmentToExponent a)
  , Just LeqProof <- isPosNat bits
  , Just LeqProof <- testLeq bits w =
    do lowbits <- bvSelect sym (knownNat :: NatRepr 0) bits offset
       bvEq sym lowbits =<< bvLit sym bits 0
isAligned sym _ _ _ =
  return (falsePred sym)

-- | The LLVM memory model generally does not allow for different
-- memory regions to alias each other: Pointers with different
-- allocation block numbers will compare as definitely unequal.
-- However, it does allow two /immutable/ memory regions to alias each
-- other. To make this sound, equality comparisons between pointers to
-- different immutable memory regions must not evaluate to false.
-- Therefore pointer equality comparisons assert that the pointers are
-- not aliasable: they must not point to two different immutable
-- blocks.
notAliasable ::
  forall sym w .
  (1 <= w, IsSymInterface sym) =>
  sym ->
  LLVMPtr sym w ->
  LLVMPtr sym w ->
  Mem sym ->
  IO (Pred sym)
notAliasable sym (llvmPointerView -> (blk1, _)) (llvmPointerView -> (blk2, _)) mem =
  do p0 <- natEq sym blk1 blk2
     p1 <- isMutable blk1 (memAllocs mem)
     p2 <- isMutable blk2 (memAllocs mem)
     orPred sym p0 =<< orPred sym p1 p2
  where
    isMutable _blk [] = return (falsePred sym)
    isMutable blk (Alloc _ _ _ Immutable _ _ : r) = isMutable blk r
    isMutable blk (Alloc _ a _ Mutable _ _ : r) =
      do p1 <- natEq sym blk =<< natLit sym a
         p2 <- isMutable blk r
         orPred sym p1 p2
    isMutable blk (MemFree _ : r) = isMutable blk r
    isMutable blk (AllocMerge c x y : r) =
      do px <- isMutable blk x
         py <- isMutable blk y
         p1 <- itePred sym c px py
         p2 <- isMutable blk r
         orPred sym p1 p2

--------------------------------------------------------------------------------
-- Other memory operations

-- | Write a value to memory.
--
-- The returned predicates assert (in this order):
--  * the pointer falls within an allocated, mutable memory region
--  * the pointer's alignment is correct
writeMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtr sym w
         -> StorageType
         -> Alignment
         -> LLVMVal sym
         -> Mem sym
         -> IO (Mem sym, Pred sym, Pred sym)
writeMem sym w ptr tp alignment v m =
  do sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
     p1 <- isAllocatedMutable sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     return (memAddWrite (MemWrite ptr (MemStore v tp alignment)) m, p1, p2)

-- | Write a value to any memory region, mutable or immutable.
--
-- The returned predicates assert (in this order):
--  * the pointer falls within an allocated memory region
--  * the pointer's alignment is correct
writeConstMem ::
  (1 <= w, IsSymInterface sym) =>
  sym           ->
  NatRepr w     ->
  LLVMPtr sym w ->
  StorageType   ->
  Alignment     ->
  LLVMVal sym   ->
  Mem sym       ->
  IO (Mem sym, Pred sym, Pred sym)
writeConstMem sym w ptr tp alignment v m =
  do sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
     p1 <- isAllocated sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     return (memAddWrite (MemWrite ptr (MemStore v tp alignment)) m, p1, p2)

-- | Perform a mem copy (a la @memcpy@ in C).
--
-- The returned predicates assert (in this order):
--  * the source pointer falls within an allocated memory region
--  * the dest pointer falls within an allocated, mutable memory region
copyMem ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Dest   -} ->
  LLVMPtr sym w {- ^ Source -} ->
  SymBV sym w   {- ^ Size   -} ->
  Mem sym -> IO (Mem sym, Pred sym, Pred sym)
copyMem sym w dst src sz m =
  do p1 <- isAllocated sym w noAlignment src sz m
     p2 <- isAllocatedMutable sym w noAlignment dst sz m
     return (memAddWrite (MemWrite dst (MemCopy src sz)) m, p1, p2)

-- | Perform a mem set, filling a number of bytes with a given 8-bit
-- value. The returned 'Pred' asserts that the pointer falls within an
-- allocated, mutable memory region.
setMem ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Pointer -} ->
  SymBV sym 8 {- ^ Byte value -} ->
  SymBV sym w {- ^ Number of bytes to set -} ->
  Mem sym -> IO (Mem sym, Pred sym)

setMem sym w ptr val sz m =
  do p <- isAllocatedMutable sym w noAlignment ptr sz m
     return (memAddWrite (MemWrite ptr (MemSet val sz)) m, p)

-- | Write an array to memory.
--
-- The returned predicates assert (in this order):
--  * the pointer falls within an allocated, mutable memory region
--  * the pointer has the proper alignment
writeArrayMem ::
  (IsSymInterface sym, 1 <= w) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Pointer -} ->
  Alignment ->
  SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ Array value -} ->
  SymBV sym w {- ^ Array size -} ->
  Mem sym -> IO (Mem sym, Pred sym, Pred sym)
writeArrayMem sym w ptr alignment arr sz m =
  do p1 <- isAllocatedMutable sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     return (memAddWrite (MemWrite ptr (MemArrayStore arr sz)) m, p1, p2)

-- | Write an array to memory.
--
-- The returned predicates assert (in this order):
--  * the pointer falls within an allocated memory region
--  * the pointer has the proper alignment
writeArrayConstMem ::
  (IsSymInterface sym, 1 <= w) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Pointer -} ->
  Alignment ->
  SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ Array value -} ->
  SymBV sym w {- ^ Array size -} ->
  Mem sym -> IO (Mem sym, Pred sym, Pred sym)
writeArrayConstMem sym w ptr alignment arr sz m =
  do p1 <- isAllocated sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     return (memAddWrite (MemWrite ptr (MemArrayStore arr sz)) m, p1, p2)

-- | Allocate a new empty memory region.
allocMem :: AllocType -- ^ Type of allocation
         -> Natural -- ^ Block id for allocation
         -> SymBV sym w -- ^ Size
         -> Alignment
         -> Mutability -- ^ Is block read-only
         -> String -- ^ Source location
         -> Mem sym
         -> Mem sym
allocMem a b sz alignment mut loc = memAddAlloc (Alloc a b sz mut alignment loc)

-- | Allocate and initialize a new memory region.
allocAndWriteMem ::
  (1 <= w, IsExprBuilder sym) =>
  sym -> NatRepr w ->
  AllocType   {- ^ Type of allocation -}      ->
  Natural     {- ^ Block id for allocation -} ->
  StorageType                                 ->
  Alignment                                   ->
  Mutability  {- ^ Is block read-only -}      ->
  String      {- ^ Source location -}         ->
  LLVMVal sym {- ^ Value to write -}          ->
  Mem sym -> IO (Mem sym)
allocAndWriteMem sym w a b tp alignment mut loc v m =
  do sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
     base <- natLit sym b
     off <- bvLit sym w 0
     let p = LLVMPointer base off
     return (m & memAddAlloc (Alloc a b sz mut alignment loc)
               & memAddWrite (MemWrite p (MemStore v tp alignment)))

pushStackFrameMem :: Mem sym -> Mem sym
pushStackFrameMem = memState %~ StackFrame emptyChanges

popStackFrameMem :: Mem sym -> Mem sym
popStackFrameMem m = m & memState %~ popf
  where popf (StackFrame (a,w) s) = s & memStateLastChanges %~ prependChanges c
          where c = (mapMaybe pa a, w)

        -- WARNING: The following code executes a stack pop underneath a branch
        -- frame.  This is necessary to get merges to work correctly
        -- when they propagate all the way to function returns.
        -- However, it is not clear that the following code is
        -- precisely correct because it may leave in place writes to
        -- memory locations that have just been popped off the stack.
        -- This does not appear to be causing problems for our
        -- examples, but may be a source of subtle errors.
        popf (BranchFrame (a,w) s) = BranchFrame c $ popf s
          where c = (mapMaybe pa a, w)

        popf _ = error "popStackFrameMem given unexpected memory"

        pa (Alloc StackAlloc _ _ _ _ _) = Nothing
        pa a@(Alloc HeapAlloc _ _ _ _ _) = Just a
        pa a@(Alloc GlobalAlloc _ _ _ _ _) = Just a
        pa a@(MemFree _) = Just a
        pa (AllocMerge c x y) = Just (AllocMerge c (mapMaybe pa x) (mapMaybe pa y))

-- | Free a heap-allocated block of memory.
--
-- The returned predicates assert (in this order):
--  * the pointer points to the base of a block
--  * said block is valid, heap-allocated, and mutable
--
-- Because the LLVM memory model allows immutable blocks to alias each other,
-- freeing an immutable block could lead to unsoundness.
freeMem :: forall sym w .
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Base of allocation to free -} ->
  Mem sym ->
  IO (Mem sym, Pred sym, Pred sym)
freeMem sym w (LLVMPointer blk off) m =
  do p1 <- bvEq sym off =<< bvLit sym w 0
     p2 <- isHeapAllocated (return (falsePred sym)) (memAllocs m)
     return (memAddAlloc (MemFree blk) m, p1, p2)
  where
    isHeapAllocated :: IO (Pred sym) -> [MemAlloc sym] -> IO (Pred sym)
    isHeapAllocated fallback [] = fallback
    isHeapAllocated fallback (alloc : r) =
      case alloc of
        Alloc HeapAlloc a _ Mutable _ _ ->
          do sameBlock <- natEq sym blk =<< natLit sym a
             case asConstantPred sameBlock of
               Just True  -> return (truePred sym)
               Just False -> isHeapAllocated fallback r
               Nothing    -> orPred sym sameBlock =<< isHeapAllocated fallback r
        Alloc _ _ _ _ _ _ ->
          isHeapAllocated fallback r
        MemFree a ->
          do sameBlock <- natEq sym blk a
             case asConstantPred sameBlock of
               Just True  -> return (falsePred sym)
               Just False -> isHeapAllocated fallback r
               Nothing    ->
                 do notSameBlock <- notPred sym sameBlock
                    andPred sym notSameBlock =<< isHeapAllocated fallback r
        AllocMerge _ [] [] ->
          isHeapAllocated fallback r
        AllocMerge c xr yr ->
          do p <- isHeapAllocated fallback r -- TODO: wrap this in a delay
             px <- isHeapAllocated (return p) xr
             py <- isHeapAllocated (return p) yr
             itePred sym c px py


branchMem :: Mem sym -> Mem sym
branchMem = memState %~ BranchFrame emptyChanges

branchAbortMem :: Mem sym -> Mem sym
branchAbortMem = memState %~ popf
  where popf (BranchFrame c s) = s & memStateLastChanges %~ prependChanges c
        popf _ = error "branchAbortMem given unexpected memory"

mergeMem :: Pred sym -> Mem sym -> Mem sym -> Mem sym
mergeMem c x y =
  case (x^.memState, y^.memState) of
    (BranchFrame a s, BranchFrame b _) ->
      let s' = s & memStateLastChanges %~ prependChanges (muxChanges c a b)
      in x & memState .~ s'
    _ -> error "mergeMem given unexpected memories"


--------------------------------------------------------------------------------
-- Pretty printing


ppTermExpr
  :: forall sym. IsExprBuilder sym
  => LLVMVal sym
  -> Doc
ppTermExpr t = -- FIXME, do something with the predicate?
  case t of
    LLVMValZero _tp -> text "0"
    LLVMValInt base off -> ppPtr @sym (LLVMPointer base off)
    LLVMValFloat _ v -> printSymExpr v
    LLVMValStruct v -> encloseSep lbrace rbrace comma v''
      where v'  = fmap (over _2 ppTermExpr) (V.toList v)
            v'' = map (\(fld,doc) ->
                        group (text "base+" <> text (show $ fieldOffset fld) <+> equals <+> doc))
                      v'
    LLVMValArray _tp v -> encloseSep lbracket rbracket comma v'
      where v' = ppTermExpr <$> V.toList v

-- | Pretty print type.
ppType :: StorageType -> Doc
ppType tp =
  case storageTypeF tp of
    Bitvector w -> text ('i': show (bytesToBits w))
    Float -> text "float"
    Double -> text "double"
    X86_FP80 -> text "long double"
    Array n etp -> brackets (text (show n) <+> char 'x' <+> ppType etp)
    Struct flds -> braces $ hsep $ punctuate (char ',') $ V.toList $ ppFld <$> flds
      where ppFld f = ppType (f^.fieldVal)

ppMerge :: IsExpr e
        => (v -> Doc)
        -> e tp
        -> [v]
        -> [v]
        -> Doc
ppMerge vpp c x y =
  indent 2 $
    text "Condition:" <$$>
    indent 2 (printSymExpr c) <$$>
    text "True Branch:"  <$$>
    indent 2 (vcat $ map vpp x) <$$>
    text "False Branch:" <$$>
    indent 2 (vcat $ map vpp y)

ppAlloc :: IsExprBuilder sym => MemAlloc sym -> Doc
ppAlloc (Alloc atp base sz mut _alignment loc) =
  text (show atp) <+> text (show base) <+> printSymExpr sz <+> text (show mut) <+> text loc
ppAlloc (MemFree base) =
  text "free" <+> printSymExpr base
ppAlloc (AllocMerge c x y) = do
  text "merge" <$$> ppMerge ppAlloc c x y

ppAllocs :: IsExprBuilder sym => [MemAlloc sym] -> Doc
ppAllocs xs = vcat $ map ppAlloc xs

ppWrite :: IsExprBuilder sym => MemWrite sym -> Doc
ppWrite (MemWrite d (MemCopy s l)) = do
  text "memcopy" <+> ppPtr d <+> ppPtr s <+> printSymExpr l
ppWrite (MemWrite d (MemSet v l)) = do
  text "memset" <+> ppPtr d <+> printSymExpr v <+> printSymExpr l
ppWrite (MemWrite d (MemStore v _ _)) = do
  char '*' <> ppPtr d <+> text ":=" <+> ppTermExpr v
ppWrite (MemWrite d (MemArrayStore arr _)) = do
  char '*' <> ppPtr d <+> text ":=" <+> printSymExpr arr
ppWrite (WriteMerge c x y) = do
  text "merge" <$$> ppMerge ppWrite c x y

ppMemChanges :: IsExprBuilder sym => MemChanges sym -> Doc
ppMemChanges (al,wl) =
  text "Allocations:" <$$>
  indent 2 (vcat (map ppAlloc al)) <$$>
  text "Writes:" <$$>
  indent 2 (vcat (map ppWrite wl))

ppMemState :: (MemChanges sym -> Doc) -> MemState sym -> Doc
ppMemState f (EmptyMem d) = do
  text "Base memory" <$$> indent 2 (f d)
ppMemState f (StackFrame d ms) = do
  text "Stack frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms
ppMemState f (BranchFrame d ms) = do
  text "Branch frame" <$$>
    indent 2 (f d) <$$>
    ppMemState f ms

ppMem :: IsExprBuilder sym => Mem sym -> Doc
ppMem m = ppMemState ppMemChanges (m^.memState)
