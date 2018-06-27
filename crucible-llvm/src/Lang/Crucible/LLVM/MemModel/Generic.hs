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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
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
import Data.Parameterized.Some

import What4.Interface
import What4.Partial

import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.LLVM.MemModel.Type
import Lang.Crucible.LLVM.MemModel.Common
import Lang.Crucible.LLVM.MemModel.Pointer
import Lang.Crucible.Backend


--import Debug.Trace as Debug

adrVar :: AddrDecomposeResult sym w -> Maybe Natural
adrVar Symbolic{} = Nothing
adrVar (ConcreteOffset v _) = Just v
adrVar (SymbolicOffset v _) = Just v

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
   = forall w. Alloc AllocType Natural (SymBV sym w) Mutability String
     -- | Freeing of the given block ID.
   | MemFree (SymNat sym)
     -- | The merger of two allocations.
   | AllocMerge (Pred sym) [MemAlloc sym] [MemAlloc sym]

data MemWrite sym
    -- | @MemCopy dst src len@ represents a copy from [src..src+len) to
    -- [dst..dst+len).
  = forall w. MemCopy (LLVMPtr sym w) (LLVMPtr sym w) (SymBV sym w)
    -- | Memstore is given address was written, value, and type of value.
  | forall w. MemStore (LLVMPtr sym w) (LLVMVal sym) Type
    -- | The merger of two memories.
  | WriteMerge (Pred sym) [MemWrite sym] [MemWrite sym]

--------------------------------------------------------------------------------
-- Reading from memory

tgAddPtrC :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> LLVMPtr sym w -> Addr -> IO (LLVMPtr sym w)
tgAddPtrC sym w x y = ptrAdd sym w x =<< constOffset sym w y

badLoad :: (IsExprBuilder sym) => sym -> Type -> IO (PartLLVMVal sym)
badLoad _sym _tp = return Unassigned

genPtrExpr :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w
           -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
           -> PtrExpr
           -> IO (LLVMPtr sym w)
genPtrExpr sym w f@(load, store, _size) expr =
  case expr of
    PtrAdd pe ie -> do
      pe' <- genPtrExpr sym w f pe
      ie' <- genIntExpr sym w f ie
      ptrAdd sym w pe' ie'
    Load -> return load
    Store -> return store

genIntExpr :: (1 <= w, IsSymInterface sym) => sym -> NatRepr w
           -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
           -> IntExpr
           -> IO (SymBV sym w)
genIntExpr sym w f@(_load, _store, size) expr =
  case expr of
    PtrDiff e1 e2 -> do
      e1' <- genPtrExpr sym w f e1
      e2' <- genPtrExpr sym w f e2
      ptrDiff sym w e1' e2'
    IntAdd e1 e2 -> do
      e1' <- genIntExpr sym w f e1
      e2' <- genIntExpr sym w f e2
      bvAdd sym e1' e2'
    CValue i -> bvLit sym w (toInteger i)
    StoreSize -> return size

genCondVar :: (1 <= w, IsSymInterface sym)
              => sym -> NatRepr w
              -> (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w)
              -> Cond -> IO (Pred sym)
genCondVar sym w inst c =
  case c of
    PtrComparable x y -> join $ ptrComparable sym w <$> genPtrExpr sym w inst x <*> genPtrExpr sym w inst y
    PtrOffsetEq x y   -> join $ ptrOffsetEq sym w <$> genPtrExpr sym w inst x <*> genPtrExpr sym w inst y
    PtrOffsetLe x y   -> join $ ptrOffsetLe sym w <$> genPtrExpr sym w inst x <*> genPtrExpr sym w inst y
    IntEq x y         -> join $ bvEq sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    IntLe x y         -> join $ bvSle sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    And x y           -> join $ andPred sym <$> genCondVar sym w inst x <*> genCondVar sym w inst y

genValueCtor :: forall sym .
  IsSymInterface sym => sym ->
  EndianForm ->
  ValueCtor (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
genValueCtor sym end v =
  case v of
    ValueCtorVar x -> return x
    ConcatBV low_w vcl high_w vch ->
      do vl <- genValueCtor sym end vcl
         vh <- genValueCtor sym end vch
         case end of
           BigEndian    -> bvConcatPartLLVMVal sym high_w vh low_w vl
           LittleEndian -> bvConcatPartLLVMVal sym low_w vl high_w vh
    ConsArray tp vc1 n vc2 ->
      do lv1 <- genValueCtor sym end vc1
         lv2 <- genValueCtor sym end vc2
         consArrayPartLLVMVal sym tp lv1 n lv2
    AppendArray tp n1 vc1 n2 vc2 ->
      do lv1 <- genValueCtor sym end vc1
         lv2 <- genValueCtor sym end vc2
         appendArrayPartLLVMVal sym tp n1 lv1 n2 lv2
    MkArray tp vv ->
      do vec <- traverse (genValueCtor sym end) vv
         mkArrayPartLLVMVal sym tp vec
    MkStruct vv ->
      do vec <- traverse (traverse (genValueCtor sym end)) vv
         mkStructPartLLVMVal sym vec
    BVToFloat _ ->
      return Unassigned
      -- fail "genValueCtor: Floating point values not supported"
    BVToDouble _ ->
      return Unassigned
      -- fail "genValueCtor: Floating point values not supported"

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
    ArrayElt sz tp idx v ->
      arrayEltPartLLVMVal sz tp idx =<< applyView sym end t v
    FieldVal flds idx v ->
      fieldValPartLLVMVal flds idx =<< applyView sym end t v

evalMuxValueCtor ::
  forall u sym w .
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  EndianForm ->
  (LLVMPtr sym w, LLVMPtr sym w, SymBV sym w) {- ^ Evaluation function -} ->
  (u -> IO (PartLLVMVal sym)) {- ^ Function for reading specific subranges -} ->
  Mux (ValueCtor u) ->
  IO (PartLLVMVal sym)
evalMuxValueCtor sym _w end _vf subFn (MuxVar v) =
  do v' <- traverse subFn v
     genValueCtor sym end v'
evalMuxValueCtor sym w end vf subFn (Mux c t1 t2) =
  do c' <- genCondVar sym w vf c
     t1' <- evalMuxValueCtor sym w end vf subFn t1
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
      do c' <- genCondVar sym w vf (PtrOffsetEq (aOffset n) b)
         t2 <- k
         muxLLVMVal sym c' t1 t2

    aOffset :: Bytes -> PtrExpr
    aOffset n = PtrAdd a (CValue (bytesToInteger n))

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
                 then PtrOffsetEq (aOffset n) b
                 else And (PtrOffsetLe (aOffset n) b)
                          (PtrOffsetLe b (aOffset (fst (last xps1))))
         c' <- genCondVar sym w vf c
         p' <- simplPred xps2 p0
         itePred sym c' p p'


readMemCopy :: forall sym w .
               (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w
            -> EndianForm
            -> (LLVMPtr sym w, AddrDecomposeResult sym w)
            -> Type
            -> LLVMPtr sym w
            -> LLVMPtr sym w
            -> SymBV sym w
            -> (Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (PartLLVMVal sym))
            -> IO (PartLLVMVal sym)
readMemCopy sym w end (l,ld) tp d src sz readPrev' = do
  let dd = ptrDecompose sym w d
  let readPrev tp' p = readPrev' tp' (p, ptrDecompose sym w p)
  let varFn = (l, d, sz)
  case (ld, dd) of
    -- Offset if known
    (ConcreteOffset lv lo, ConcreteOffset sv so)
      | lv == sv -> do
      let subFn :: RangeLoad Addr Addr -> IO (PartLLVMVal sym)
          subFn (OutOfRange o tp') = do lv' <- natLit sym lv
                                        o' <- bvLit sym w (bytesToInteger o)
                                        readPrev tp' (LLVMPointer lv' o')
          subFn (InRange    o tp') = readPrev tp' =<< tgAddPtrC sym w src o
      case asUnsignedBV sz of
        Just csz -> do
          let s = R (fromInteger so) (fromInteger (so + csz))
          let vcr = rangeLoad (fromInteger lo) tp s
          genValueCtor sym end =<< traverse subFn vcr
        _ ->
          evalMuxValueCtor sym w end varFn subFn $
            fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , lv /= sv -> readPrev' tp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: RangeLoad PtrExpr IntExpr -> IO (PartLLVMVal sym)
          subFn (OutOfRange o tp') =
            readPrev tp' =<< genPtrExpr sym w varFn o
          subFn (InRange o tp') =
            readPrev tp' =<< ptrAdd sym w src =<< genIntExpr sym w varFn o
      let pref | ConcreteOffset{} <- dd = FixedStore
               | ConcreteOffset{} <- ld = FixedLoad
               | otherwise = NeitherFixed
      let mux0 | Just csz <- asUnsignedBV sz =
                   fixedSizeRangeLoad pref tp (fromInteger csz)
               | otherwise =
                   symbolicRangeLoad pref tp
      evalMuxValueCtor sym w end varFn subFn mux0

readMemStore :: forall sym w .
               (1 <= w, IsSymInterface sym)
            => sym -> NatRepr w
            -> EndianForm
            -> (LLVMPtr sym w, AddrDecomposeResult sym w)
               -- ^ The loaded address and information
            -> Type
               -- ^ The type we are reading.
            -> LLVMPtr sym w
               -- ^ The store we are reading from.
            -> LLVMVal sym
               -- ^ The value that was stored.
            -> Type
               -- ^ The type of value that was written.
            -> Alignment
               -- ^ The alignment of the pointer we are reading from
            -> (Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (PartLLVMVal sym))
               -- ^ A callback function for when reading fails.
            -> IO (PartLLVMVal sym)
readMemStore sym w end (l,ld) ltp d t stp loadAlign readPrev' = do
  ssz <- bvLit sym w (bytesToInteger (typeSize stp))
  let varFn = (l, d, ssz)
  let readPrev tp p = readPrev' tp (p, ptrDecompose sym w p)
  let dd = ptrDecompose sym w d
  case (ld, dd) of
    -- Offset if known
    (ConcreteOffset lv lo, ConcreteOffset sv so)
      | lv == sv -> do
      let subFn :: ValueLoad Addr -> IO (PartLLVMVal sym)
          subFn (OldMemory o tp')   = do lv' <- natLit sym lv
                                         o' <- bvLit sym w (bytesToInteger o)
                                         readPrev tp' (LLVMPointer lv' o')
          subFn (LastStore v)       = applyView sym end (PE (truePred sym) t) v
          subFn (InvalidMemory tp') = badLoad sym tp'
      let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (ValueViewVar stp)
      genValueCtor sym end =<< traverse subFn vcr
    -- We know variables are disjoint.
    _ | Just lv <- adrVar ld
      , Just sv <- adrVar dd
      , lv /= sv -> readPrev' ltp (l,ld)
      -- Symbolic offsets
    _ -> do
      let subFn :: ValueLoad PtrExpr -> IO (PartLLVMVal sym)
          subFn (OldMemory o tp')   = readPrev tp' =<< genPtrExpr sym w varFn o
          subFn (LastStore v)       = applyView sym end (PE (truePred sym) t) v
          subFn (InvalidMemory tp') = badLoad sym tp'
      let pref | ConcreteOffset{} <- dd = FixedStore
               | ConcreteOffset{} <- ld = FixedLoad
               | otherwise = NeitherFixed
      let ctz :: Integer -> Alignment
          ctz x | x == 0 = 64 -- maximum alignment
                | odd x = 0
                | otherwise = 1 + ctz (x `div` 2)
      let storeAlign =
            case dd of
              ConcreteOffset _ x -> ctz x
              _                  -> 0
      let align' = min loadAlign storeAlign
      evalMuxValueCtor sym w end varFn subFn $
        symbolicValueLoad pref ltp (ValueViewVar stp) align'

readMem :: (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w
        -> LLVMPtr sym w
        -> Type
        -> Alignment
        -> Mem sym
        -> IO (PartLLVMVal sym)
readMem sym w l tp alignment m = do
  let ld = ptrDecompose sym w l
  sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
  p1 <- isAllocated sym w l sz m
  p2 <- isAligned sym w l alignment
  p <- andPred sym p1 p2
  val <- readMem' sym w (memEndianForm m) (l,ld) tp alignment (memWrites m)
  val' <- andPartVal sym p val
  return val'

andPartVal :: IsSymInterface sym => sym -> Pred sym -> PartLLVMVal sym -> IO (PartLLVMVal sym)
andPartVal sym p val =
  case val of
    Unassigned -> return Unassigned
    PE p' v    -> do p'' <- andPred sym p p'
                     return (PE p'' v)

data CacheEntry sym w =
  CacheEntry !(Type) !(SymNat sym) !(SymBV sym w)

instance (TestEquality (SymExpr sym)) => Eq (CacheEntry sym w) where
  (CacheEntry tp1 blk1 off1) == (CacheEntry tp2 blk2 off2) =
    tp1 == tp2 && (isJust $ testEquality blk1 blk2) && (isJust $ testEquality off1 off2)

instance IsSymInterface sym => Ord (CacheEntry sym w) where
  compare (CacheEntry tp1 blk1 off1) (CacheEntry tp2 blk2 off2) =
    compare tp1 tp2
      `mappend` toOrdering (compareF blk1 blk2)
      `mappend` toOrdering (compareF off1 off2)


toCacheEntry :: Type -> LLVMPtr sym w -> CacheEntry sym w
toCacheEntry tp (llvmPointerView -> (blk, bv)) = CacheEntry tp blk bv

-- | Read a value from memory given a list of writes.
--
-- This represents a predicate indicating if the read was successful, and the value
-- read (which may be anything if read was unsuccessful).
readMem' :: forall w sym . (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> EndianForm
         -> (LLVMPtr sym w, AddrDecomposeResult sym w)
            -- ^ Address we are reading along with information about how it was constructed.
         -> Type
            -- ^ The type to read from memory.
         -> Alignment -- ^ Alignment of pointer to read from
         -> [MemWrite sym]
            -- ^ List of writes.
         -> IO (PartLLVMVal sym)
readMem' sym w end l0 tp0 alignment = go (\tp _l -> badLoad sym tp) l0 tp0
  where
    go :: (Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (PartLLVMVal sym)) ->
          (LLVMPtr sym w, AddrDecomposeResult sym w) ->
          Type ->
          [MemWrite sym] ->
          IO (PartLLVMVal sym)
    go fallback l tp [] = fallback tp l
    go fallback l tp (h : r) =
      do cache <- newIORef Map.empty
         let readPrev :: Type -> (LLVMPtr sym w, AddrDecomposeResult sym w) -> IO (PartLLVMVal sym)
             readPrev tp' l' = do
               m <- readIORef cache
               case Map.lookup (toCacheEntry tp' (fst l')) m of
                 Just x -> return x
                 Nothing -> do
                   x <- go fallback l' tp' r
                   writeIORef cache $ Map.insert (toCacheEntry tp' (fst l')) x m
                   return x
         case h of
           MemCopy dst src sz ->
             case testEquality (ptrWidth dst) w of
               Just Refl -> readMemCopy sym w end l tp dst src sz readPrev
               Nothing   -> readPrev tp l
           MemStore dst v stp ->
             case testEquality (ptrWidth dst) w of
               Just Refl -> readMemStore sym w end l tp dst v stp alignment readPrev
               Nothing   -> readPrev tp l
           WriteMerge _ [] [] ->
             go fallback l tp r
           WriteMerge c xr yr ->
             do x <- go readPrev l tp xr
                y <- go readPrev l tp yr
                muxLLVMVal sym c x y

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

-- This function is parameterized by a predicate on the mutability, so
-- it can optionally be restricted to mutable regions only.
isAllocatedMut ::
  forall sym w .
  (1 <= w, IsSymInterface sym) =>
  (Mutability -> Bool) ->
  sym -> NatRepr w     ->
  LLVMPtr sym w        ->
  SymBV sym w          ->
  Mem sym              ->
  IO (Pred sym)
isAllocatedMut mutOk sym w (llvmPointerView -> (blk, off)) sz m = do
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
          go fallback (Alloc _ a asz mut _ : r)
            | mutOk mut = step a asz (go fallback r)
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
isAllocated :: forall sym w. (1 <= w, IsSymInterface sym)
            => sym
            -> NatRepr w
            -> LLVMPtr sym w
            -> SymBV sym w
            -> Mem sym
            -> IO (Pred sym)
isAllocated = isAllocatedMut (const True)

isAllocatedMutable ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w -> LLVMPtr sym w -> SymBV sym w -> Mem sym -> IO (Pred sym)
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
   isAllocated sym w p sz m
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
  | a == 0 = return (truePred sym)
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
    isMutable blk (Alloc _ _ _ Immutable _ : r) = isMutable blk r
    isMutable blk (Alloc _ a _ Mutable _ : r) =
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

-- | Write a value to memory. The returned 'Pred' asserts that the
-- pointer falls within an allocated mutable memory region.
writeMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtr sym w
         -> Type
         -> LLVMVal sym
         -> Mem sym
         -> IO (Pred sym, Mem sym)
writeMem sym w ptr tp v m =
  do sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
     p <- isAllocatedMutable sym w ptr sz m
     return (p, memAddWrite (MemStore ptr v tp) m)

-- | Write a value to any memory region, mutable or immutable. The
-- returned 'Pred' asserts that the pointer falls within an allocated
-- memory region.
writeConstMem ::
  (1 <= w, IsSymInterface sym) =>
  sym           ->
  NatRepr w     ->
  LLVMPtr sym w ->
  Type          ->
  LLVMVal sym   ->
  Mem sym       ->
  IO (Pred sym, Mem sym)
writeConstMem sym w ptr tp v m =
  do sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
     p <- isAllocated sym w ptr sz m
     return (p, memAddWrite (MemStore ptr v tp) m)

-- | Perform a mem copy. The returned 'Pred' asserts that the source
-- and destination pointers both fall within allocated memory regions.
copyMem :: (1 <= w, IsSymInterface sym)
         => sym -> NatRepr w
         -> LLVMPtr sym w -- ^ Dest
         -> LLVMPtr sym w -- ^ Source
         -> SymBV sym w -- ^ Size
         -> Mem sym
         -> IO (Pred sym, Mem sym)
copyMem sym w dst src sz m = do
  (,) <$> (join $ andPred sym <$> isAllocated sym w dst sz m
                              <*> isAllocated sym w src sz m)
      <*> (return $ m & memAddWrite (MemCopy dst src sz))


-- | Allocate a new empty memory region.
allocMem :: AllocType -- ^ Type of allocation
         -> Natural -- ^ Block id for allocation
         -> SymBV sym w -- ^ Size
         -> Mutability -- ^ Is block read-only
         -> String -- ^ Source location
         -> Mem sym
         -> Mem sym
allocMem a b sz mut loc = memAddAlloc (Alloc a b sz mut loc)

-- | Allocate and initialize a new memory region.
allocAndWriteMem :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w
                 -> AllocType -- ^ Type of allocation
                 -> Natural -- ^ Block id for allocation
                 -> Type
                 -> Mutability -- ^ Is block read-only
                 -> String -- ^ Source location
                 -> LLVMVal sym -- ^ Value to write
                 -> Mem sym
                 -> IO (Mem sym)
allocAndWriteMem sym w a b tp mut loc v m = do
  sz <- bvLit sym w (bytesToInteger (typeEnd 0 tp))
  base <- natLit sym b
  off <- bvLit sym w 0
  let p = LLVMPointer base off
  return (m & memAddAlloc (Alloc a b sz mut loc)
            & memAddWrite (MemStore p v tp))

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

        pa (Alloc StackAlloc _ _ _ _) = Nothing
        pa a@(Alloc HeapAlloc _ _ _ _) = Just a
        pa a@(Alloc GlobalAlloc _ _ _ _) = Just a
        pa a@(MemFree _) = Just a
        pa (AllocMerge c x y) = Just (AllocMerge c (mapMaybe pa x) (mapMaybe pa y))

-- | Free a heap-allocated block of memory. The returned 'Pred'
-- asserts that the pointer points to the base of a valid
-- heap-allocated block.
freeMem :: forall sym w .
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Base of allocation to free -} ->
  Mem sym ->
  IO (Pred sym, Mem sym)
freeMem sym w (LLVMPointer blk off) m =
  do z <- bvLit sym w 0
     p1 <- bvEq sym off z
     p2 <- isHeapAllocated (return (falsePred sym)) (memAllocs m)
     p <- andPred sym p1 p2
     return (p, memAddAlloc (MemFree blk) m)
  where
    isHeapAllocated :: IO (Pred sym) -> [MemAlloc sym] -> IO (Pred sym)
    isHeapAllocated fallback [] = fallback
    isHeapAllocated fallback (alloc : r) =
      case alloc of
        Alloc HeapAlloc a _ _ _ ->
          do sameBlock <- natEq sym blk =<< natLit sym a
             case asConstantPred sameBlock of
               Just True  -> return (truePred sym)
               Just False -> isHeapAllocated fallback r
               Nothing    -> orPred sym sameBlock =<< isHeapAllocated fallback r
        Alloc _ _ _ _ _ ->
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
    LLVMValInt base off -> ppPtr @sym (LLVMPointer base off)
    LLVMValReal _ v -> printSymExpr v
    LLVMValStruct v -> encloseSep lbrace rbrace comma v''
      where v'  = fmap (over _2 ppTermExpr) (V.toList v)
            v'' = map (\(fld,doc) ->
                        group (text "base+" <> text (show $ fieldOffset fld) <+> equals <+> doc))
                      v'
    LLVMValArray _tp v -> encloseSep lbracket rbracket comma v'
      where v' = ppTermExpr <$> V.toList v

-- | Pretty print type.
ppType :: Type -> Doc
ppType tp =
  case typeF tp of
    Bitvector w -> text ('i': show (bytesToBits w))
    Float -> text "float"
    Double -> text "double"
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
ppAlloc (Alloc atp base sz mut loc) =
  text (show atp) <+> text (show base) <+> printSymExpr sz <+> text (show mut) <+> text loc
ppAlloc (MemFree base) =
  text "free" <+> printSymExpr base
ppAlloc (AllocMerge c x y) = do
  text "merge" <$$> ppMerge ppAlloc c x y

ppAllocs :: IsExprBuilder sym => [MemAlloc sym] -> Doc
ppAllocs xs = vcat $ map ppAlloc xs

ppWrite :: IsExprBuilder sym => MemWrite sym -> Doc
ppWrite (MemCopy d s l) = do
  text "memcopy" <+> ppPtr d <+> ppPtr s <+> printSymExpr l
ppWrite (MemStore d v _) = do
  char '*' <> ppPtr d <+> text ":=" <+> ppTermExpr v
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
