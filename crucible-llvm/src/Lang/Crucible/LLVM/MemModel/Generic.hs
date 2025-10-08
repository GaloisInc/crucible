------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Generic
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.LLVM.MemModel.Generic
  ( Mem
  , emptyMem
  , AllocType(..)
  , Mutability(..)
  , AllocInfo(..)
  , MemAllocs
  , memAllocs
  , memEndian
  , memAllocCount
  , memWriteCount
  , allocMem
  , allocAndWriteMem
  , readMem
  , isValidPointer
  , isAllocatedMutable
  , isAllocatedAlignedPointer
  , notAliasable
  , writeMem
  , writeConstMem
  , copyMem
  , setMem
  , invalidateMem
  , writeArrayMem
  , writeArrayConstMem
  , pushStackFrameMem
  , popStackFrameMem
  , freeMem
  , branchMem
  , branchAbortMem
  , mergeMem
  , asMemAllocationArrayStore
  , asMemMatchingArrayStore
  , isAligned

  , SomeAlloc(..)
  , possibleAllocs
  , possibleAllocInfo
  , ppSomeAlloc

    -- * Pretty printing
  , ppType
  , ppPtr
  , ppAllocs
  , ppMem
  , ppTermExpr
  ) where

import           Prelude hiding (pred)

import qualified Control.Exception as X
import           Control.Lens
import           Control.Monad
import           Control.Monad.State.Strict
import           Control.Monad.Trans.Maybe
import           Data.IORef
import           Data.Maybe
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Monoid
import           Data.Text (Text)
import           Numeric.Natural
import           Prettyprinter
import           Lang.Crucible.Panic (panic)
import qualified Data.Vector as V

import           Data.BitVector.Sized (BV)
import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx (SingleCtx)
import           Data.Parameterized.Some

import           What4.Interface
import qualified What4.Concrete as W4

import           Lang.Crucible.Backend
import           Lang.Crucible.LLVM.Bytes
import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.Errors.MemoryError (MemErrContext, MemoryErrorReason(..), MemoryOp(..))
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.CallStack (getCallStack)
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.Options
import           Lang.Crucible.LLVM.MemModel.MemLog
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Value
import           Lang.Crucible.LLVM.MemModel.Partial (PartLLVMVal, HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial
import           Lang.Crucible.LLVM.Utils
import           Lang.Crucible.Simulator.RegMap (RegValue'(..))

--------------------------------------------------------------------------------
-- Reading from memory

tgAddPtrC :: (1 <= w, IsExprBuilder sym) => sym -> NatRepr w -> LLVMPtr sym w -> Addr -> IO (LLVMPtr sym w)
tgAddPtrC sym w x y = ptrAdd sym w x =<< constOffset sym w y

-- | An environment used to interpret 'OffsetExpr's, 'IntExpr's, and 'Cond's.
-- These data structures may contain uninterpreted variables to be filled in
-- with the offset address of a load or store, or the size of the current
-- region. Since regions may be unbounded in size, the size argument is a
-- 'Maybe' type.
data ExprEnv sym w = ExprEnv { loadOffset  :: SymBV sym w
                             , storeOffset :: SymBV sym w
                             , sizeData    :: Maybe (SymBV sym w) }

ppExprEnv :: IsExprBuilder sym => ExprEnv sym w -> Doc ann
ppExprEnv f =
  vcat
  [ "ExprEnv"
  , indent 4 $ vcat
    [ "loadOffset:"  <+> printSymExpr (loadOffset f)
    , "storeOffset:" <+> printSymExpr (storeOffset f)
    , "sizeData:"    <+> maybe mempty printSymExpr (sizeData f)
    ]
  ]

-- | Interpret an 'OffsetExpr' as a 'SymBV'. Although 'OffsetExpr's may contain
-- 'IntExpr's, which may be undefined if they refer to the size of an unbounded
-- memory region, this function will panic if both (1) the 'sizeData'
-- in the 'ExprEnv' is 'Nothing' and (2) 'StoreSize' occurs anywhere in the
-- 'OffsetExpr'.
genOffsetExpr ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  ExprEnv sym w ->
  OffsetExpr ->
  IO (SymBV sym w)
genOffsetExpr sym w f@(ExprEnv load store _size) expr =
  case expr of
    OffsetAdd pe ie -> do
      pe' <- genOffsetExpr sym w f pe
      ie' <- genIntExpr sym w f ie
      case ie' of
        Nothing -> panic "Generic.genOffsetExpr"
                     [ "Cannot construct an offset that references the size of an unbounded region"
                     , "*** Invalid offset expression:  " ++ show expr
                     , "*** Under environment:  " ++ show (ppExprEnv f)
                     ]
        Just ie'' -> bvAdd sym pe' ie''
    Load  -> return load
    Store -> return store

-- | Interpret an 'IntExpr' as a 'SymBV'. If the 'IntExpr' contains an
-- occurrence of 'StoreSize' and the store size in the 'ExprEnv' is unbounded,
-- will return 'Nothing'.
genIntExpr ::
  (1 <= w, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  ExprEnv sym w ->
  IntExpr ->
  IO (Maybe (SymBV sym w))
genIntExpr sym w f@(ExprEnv _load _store size) expr =
  case expr of
    OffsetDiff e1 e2 -> do
      e1' <- genOffsetExpr sym w f e1
      e2' <- genOffsetExpr sym w f e2
      Just <$> bvSub sym e1' e2'
    IntAdd e1 e2 -> do
      e1' <- genIntExpr sym w f e1
      e2' <- genIntExpr sym w f e2
      case (e1', e2') of
        (Just e1'', Just e2'') -> Just <$> bvAdd sym e1'' e2''
        _                      -> return Nothing -- Unbounded space added to anything is unbounded
    CValue i -> Just <$> bvLit sym w (bytesToBV w i)
    StoreSize -> return size

-- | Interpret a conditional as a symbolic predicate.
genCondVar :: forall sym w.
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  ExprEnv sym w ->
  Cond ->
  IO (Pred sym)
genCondVar sym w inst c =
  case c of
    OffsetEq x y   -> join $ bvEq sym <$> genOffsetExpr sym w inst x <*> genOffsetExpr sym w inst y
    OffsetLe x y   -> join $ bvUle sym <$> genOffsetExpr sym w inst x <*> genOffsetExpr sym w inst y
    IntEq x y      -> join $ maybeBVEq sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    IntLe x y      -> join $ maybeBVLe sym <$> genIntExpr sym w inst x <*> genIntExpr sym w inst y
    And x y        -> join $ andPred sym <$> genCondVar sym w inst x <*> genCondVar sym w inst y
    Or x y         -> join $ orPred sym <$> genCondVar sym w inst x <*> genCondVar sym w inst y

-- | Compare the equality of two @Maybe SymBV@s
maybeBVEq :: (1 <= w, IsExprBuilder sym)
          => sym -> Maybe (SymBV sym w) -> Maybe (SymBV sym w) -> IO (Pred sym)
maybeBVEq sym (Just x) (Just y) = bvEq sym x y
maybeBVEq sym Nothing  Nothing  = return $ truePred sym
maybeBVEq sym _        _        = return $ falsePred sym

-- | Compare two @Maybe SymBV@s
maybeBVLe :: (1 <= w, IsExprBuilder sym)
          => sym -> Maybe (SymBV sym w) -> Maybe (SymBV sym w) -> IO (Pred sym)
maybeBVLe sym (Just x) (Just y) = bvSle sym x y
maybeBVLe sym _        Nothing  = return $ truePred sym
maybeBVLe sym Nothing  (Just _) = return $ falsePred sym

-- | Given a 'ValueCtor' (of partial LLVM values), recursively traverse the
-- 'ValueCtor' to reconstruct the partial value as directed (while respecting
-- endianness)
genValueCtor :: forall sym w.
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  EndianForm ->
  MemoryOp sym w ->
  ValueCtor (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
genValueCtor sym end errCtx v =
  case v of
    ValueCtorVar x -> return x
    ConcatBV vcl vch ->
      do vl <- genValueCtor sym end errCtx vcl
         vh <- genValueCtor sym end errCtx vch
         case end of
           BigEndian    -> Partial.bvConcat sym errCtx vh vl
           LittleEndian -> Partial.bvConcat sym errCtx vl vh
    ConsArray vc1 vc2 ->
      do lv1 <- genValueCtor sym end errCtx vc1
         lv2 <- genValueCtor sym end errCtx vc2
         Partial.consArray sym errCtx lv1 lv2
    AppendArray vc1 vc2 ->
      do lv1 <- genValueCtor sym end errCtx vc1
         lv2 <- genValueCtor sym end errCtx vc2
         Partial.appendArray sym errCtx lv1 lv2
    MkArray tp vv ->
      Partial.mkArray sym tp =<<
        traverse (genValueCtor sym end errCtx) vv
    MkStruct vv ->
      Partial.mkStruct sym =<<
        traverse (traverse (genValueCtor sym end errCtx)) vv
    BVToFloat x ->
      Partial.bvToFloat sym errCtx =<< genValueCtor sym end errCtx x
    BVToDouble x ->
      Partial.bvToDouble sym errCtx =<< genValueCtor sym end errCtx x
    BVToX86_FP80 x ->
      Partial.bvToX86_FP80 sym errCtx =<< genValueCtor sym end errCtx x

-- | Compute the actual value of a value deconstructor expression.
applyView ::
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  sym ->
  EndianForm ->
  MemErrContext sym w ->
  PartLLVMVal sym ->
  ValueView ->
  IO (PartLLVMVal sym)
applyView sym end errCtx t val =
  case val of
    ValueViewVar _ ->
      return t
    SelectPrefixBV i j v ->
      do t' <- applyView sym end errCtx t v
         case end of
           BigEndian    -> Partial.selectHighBv sym errCtx j i t'
           LittleEndian -> Partial.selectLowBv sym errCtx i j t'
    SelectSuffixBV i j v ->
      do t' <- applyView sym end errCtx t v
         case end of
           BigEndian -> Partial.selectLowBv sym errCtx j i t'
           LittleEndian -> Partial.selectHighBv sym errCtx i j t'
    FloatToBV v ->
      Partial.floatToBV sym errCtx =<< applyView sym end errCtx t v
    DoubleToBV v ->
      Partial.doubleToBV sym errCtx =<< applyView sym end errCtx t v
    X86_FP80ToBV v ->
      Partial.fp80ToBV sym errCtx =<< applyView sym end errCtx t v
    ArrayElt sz tp idx v ->
      Partial.arrayElt sym errCtx sz tp idx =<< applyView sym end errCtx t v
    FieldVal flds idx v ->
      Partial.fieldVal sym errCtx flds idx =<< applyView sym end errCtx t v

evalMuxValueCtor ::
  forall u sym w .
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  MemErrContext sym w ->
  ExprEnv sym w {- ^ Evaluation function -} ->
  (u -> ReadMem sym (PartLLVMVal sym)) {- ^ Function for reading specific subranges -} ->
  Mux (ValueCtor u) ->
  ReadMem sym (PartLLVMVal sym)
evalMuxValueCtor sym _w end errCtx _vf subFn (MuxVar v) =
  do v' <- traverse subFn v
     liftIO $ genValueCtor sym end errCtx v'
evalMuxValueCtor sym w end errCtx vf subFn (Mux c t1 t2) =
  do c' <- liftIO $ genCondVar sym w vf c
     case asConstantPred c' of
       Just True  -> evalMuxValueCtor sym w end errCtx vf subFn t1
       Just False -> evalMuxValueCtor sym w end errCtx vf subFn t2
       Nothing ->
        do t1' <- evalMuxValueCtor sym w end errCtx vf subFn t1
           t2' <- evalMuxValueCtor sym w end errCtx vf subFn t2
           liftIO $ Partial.muxLLVMVal sym c' t1' t2'

evalMuxValueCtor sym w end errCtx vf subFn (MuxTable a b m t) =
  do m' <- traverse (evalMuxValueCtor sym w end errCtx vf subFn) m
     t' <- evalMuxValueCtor sym w end errCtx vf subFn t
     -- TODO: simplification?
     Map.foldrWithKey f (return t') m'
  where
    f :: Bytes -> PartLLVMVal sym -> ReadMem sym (PartLLVMVal sym) -> ReadMem sym (PartLLVMVal sym)
    f n t1 k =
      do c' <- liftIO $ genCondVar sym w vf (OffsetEq (aOffset n) b)
         case asConstantPred c' of
           Just True  -> return t1
           Just False -> k
           Nothing    -> liftIO . Partial.muxLLVMVal sym c' t1 =<< k

    aOffset :: Bytes -> OffsetExpr
    aOffset n = OffsetAdd a (CValue n)

-- | Read from a memory with a memcopy to the same block we are reading.
readMemCopy ::
  forall sym w.
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  MemoryOp sym w ->
  LLVMPtr sym w  {- ^ The loaded offset               -} ->
  StorageType    {- ^ The type we are reading         -} ->
  SymBV sym w    {- ^ The destination of the memcopy  -} ->
  LLVMPtr sym w  {- ^ The source of the copied region -} ->
  SymBV sym w    {- ^ The length of the copied region -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
  ReadMem sym (PartLLVMVal sym)
readMemCopy sym w end mop (LLVMPointer blk off) tp d src sz readPrev =
  do let ld = BV.asUnsigned <$> asBV off
     let dd = BV.asUnsigned <$> asBV d
     let varFn = ExprEnv off d (Just sz)

     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: RangeLoad Addr Addr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do
                  o' <- liftIO $ bvLit sym w (bytesToBV w o)
                  readPrev tp' (LLVMPointer blk o')
                subFn (InRange o tp') =
                  readPrev tp' =<< liftIO (tgAddPtrC sym w src o)
            case BV.asUnsigned <$> asBV sz of
              Just csz -> do
                let s = R (fromInteger so) (fromInteger (so + csz))
                let vcr = rangeLoad (fromInteger lo) tp s
                liftIO . genValueCtor sym end mop =<< traverse subFn vcr
              _ ->
                evalMuxValueCtor sym w end mop varFn subFn $
                  fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
         -- Symbolic offsets
       _ ->
         do let subFn :: RangeLoad OffsetExpr IntExpr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') =
                  do o' <- liftIO $ genOffsetExpr sym w varFn o
                     readPrev tp' (LLVMPointer blk o')
                subFn (InRange o tp') = do
                  oExpr <- liftIO $ genIntExpr sym w varFn o
                  srcPlusO <- case oExpr of
                                Just oExpr' -> liftIO $ ptrAdd sym w src oExpr'
                                Nothing     -> panic "Generic.readMemCopy"
                                                ["Cannot use an unbounded bitvector expression as an offset"
                                                ,"*** In offset epxression:  " ++ show o
                                                ,"*** Under environment:  " ++ show (ppExprEnv varFn)
                                                ]
                  readPrev tp' srcPlusO
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- BV.asUnsigned <$> asBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end mop varFn subFn mux0

readMemSet ::
  forall sym w .
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  MemoryOp sym w ->
  LLVMPtr sym w {- ^ The loaded offset             -} ->
  StorageType   {- ^ The type we are reading       -} ->
  SymBV sym w   {- ^ The destination of the memset -} ->
  SymBV sym 8   {- ^ The fill byte that was set    -} ->
  SymBV sym w   {- ^ The length of the set region  -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
  ReadMem sym (PartLLVMVal sym)
readMemSet sym w end mop (LLVMPointer blk off) tp d byte sz readPrev =
  do let ld = BV.asUnsigned <$> asBV off
     let dd = BV.asUnsigned <$> asBV d
     let varFn = ExprEnv off d (Just sz)
     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: RangeLoad Addr Addr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do
                  o' <- liftIO $ bvLit sym w (bytesToBV w o)
                  readPrev tp' (LLVMPointer blk o')
                subFn (InRange   _o tp') = do
                  blk0 <- liftIO $ natLit sym 0
                  let val = LLVMValInt blk0 byte
                  let b   = Partial.totalLLVMVal sym val
                  liftIO $ genValueCtor sym end mop (memsetValue b tp')
            case BV.asUnsigned <$> asBV sz of
              Just csz -> do
                let s = R (fromInteger so) (fromInteger (so + csz))
                let vcr = rangeLoad (fromInteger lo) tp s
                liftIO . genValueCtor sym end mop =<< traverse subFn vcr
              _ -> evalMuxValueCtor sym w end mop varFn subFn $
                     fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
       -- Symbolic offsets
       _ ->
         do let subFn :: RangeLoad OffsetExpr IntExpr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') =
                  do o' <- liftIO $ genOffsetExpr sym w varFn o
                     readPrev tp' (LLVMPointer blk o')
                subFn (InRange _o tp') = liftIO $
                  do blk0 <- natLit sym 0
                     let val = LLVMValInt blk0 byte
                     let b = Partial.totalLLVMVal sym val
                     genValueCtor sym end mop (memsetValue b tp')
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- BV.asUnsigned <$> asBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end mop varFn subFn mux0

-- | Read from a memory with a store to the same block we are reading.
readMemStore ::
  forall sym w.
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  MemoryOp sym w ->
  LLVMPtr sym w {- ^ The loaded address                 -} ->
  StorageType   {- ^ The type we are reading            -} ->
  SymBV sym w   {- ^ The destination of the store       -} ->
  LLVMVal sym   {- ^ The value that was stored          -} ->
  StorageType   {- ^ The type of value that was written -} ->
  Alignment     {- ^ The alignment of the pointer we are reading from -} ->
  Alignment     {- ^ The alignment of the store from which we are reading -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym))
  {- ^ A callback function for when reading fails -} ->
  ReadMem sym (PartLLVMVal sym)
readMemStore sym w end mop (LLVMPointer blk off) ltp d t stp loadAlign storeAlign readPrev =
  do ssz <- liftIO $ bvLit sym w (bytesToBV w (storageTypeSize stp))
     let varFn = ExprEnv off d (Just ssz)
     let ld = BV.asUnsigned <$> asBV off
     let dd = BV.asUnsigned <$> asBV d
     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: ValueLoad Addr -> ReadMem sym (PartLLVMVal sym)
                subFn (OldMemory o tp')  =
                  readPrev tp' . LLVMPointer blk =<<
                    liftIO (bvLit sym w (bytesToBV w o))
                subFn (LastStore v)      = liftIO $
                  applyView sym end mop (Partial.totalLLVMVal sym t) v
                subFn (InvalidMemory tp) = liftIO (Partial.partErr sym mop $ Invalid tp)
            let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (ValueViewVar stp)
            liftIO . genValueCtor sym end mop =<< traverse subFn vcr
       -- Symbolic offsets
       _ ->
         do let subFn :: ValueLoad OffsetExpr -> ReadMem sym (PartLLVMVal sym)
                subFn (OldMemory o tp')  = do
                  o' <- liftIO $ genOffsetExpr sym w varFn o
                  readPrev tp' (LLVMPointer blk o')
                subFn (LastStore v)      = liftIO $
                  applyView sym end mop (Partial.totalLLVMVal sym t) v
                subFn (InvalidMemory tp) = liftIO (Partial.partErr sym mop $ Invalid tp)
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed

            let alignStride = fromAlignment $ min loadAlign storeAlign

            -- compute the linear form of (load offset - store offset)
            let (diffStride, diffDelta)
                  | Just (load_a, _x, load_b) <- asAffineVar off
                  , Just (store_a, _y, store_b) <- asAffineVar d = do
                    let stride' = gcd
                          (BV.asUnsigned (W4.fromConcreteBV load_a))
                          (BV.asUnsigned (W4.fromConcreteBV store_a))
                    -- mod returns a non-negative integer
                    let delta' = mod
                          (BV.asUnsigned (W4.fromConcreteBV load_b) -
                           BV.asUnsigned (W4.fromConcreteBV store_b))
                          stride'
                    (fromInteger stride', fromInteger delta')
                  | Just (load_a, _x, load_b) <- asAffineVar off
                  , Just store_b <- BV.asUnsigned <$> asBV d = do
                    let stride' = BV.asUnsigned (W4.fromConcreteBV load_a)
                    let delta' = mod (BV.asUnsigned (W4.fromConcreteBV load_b) - store_b) stride'
                    (fromInteger stride', fromInteger delta')
                  | Just load_b <- BV.asUnsigned <$> asBV off
                  , Just (store_a, _y, store_b) <- asAffineVar d = do
                    let stride' = BV.asUnsigned (W4.fromConcreteBV store_a)
                    let delta' = mod (load_b - BV.asUnsigned (W4.fromConcreteBV store_b)) stride'
                    (fromInteger stride', fromInteger delta')
                  | otherwise = (1, 0)

            let (stride, delta) = if diffStride >= alignStride
                  then (diffStride, diffDelta)
                  else (alignStride, 0)

            diff <- liftIO $ bvSub sym off d

            -- skip computing the mux tree if it would be empty
            if storageTypeSize stp <= delta && (typeEnd 0 ltp) <= (stride - delta)
              then readPrev ltp $ LLVMPointer blk off
              else evalMuxValueCtor sym w end mop varFn subFn $
                symbolicValueLoad
                  pref
                  ltp
                  (signedBVBounds diff)
                  (ValueViewVar stp)
                  (LinearLoadStoreOffsetDiff stride delta)

-- | Read from a memory with an array store to the same block we are reading.
--
-- NOTE: This case should only fire if a write is straddling an array store and
-- another write, as the top-level case of 'readMem' should handle the case
-- where a read is completely covered by a write to an array.
readMemArrayStore
  :: forall sym w
   . (1 <= w, IsSymInterface sym, HasLLVMAnn sym)
  => sym
  -> NatRepr w
  -> EndianForm
  -> MemoryOp sym w
  -> LLVMPtr sym w {- ^ The loaded offset -}
  -> StorageType {- ^ The type we are reading -}
  -> SymBV sym w {- ^ The offset of the mem array store from the base pointer -}
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ The stored array -}
  -> Maybe (SymBV sym w) {- ^ The length of the stored array -}
  -> (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym))
  -> ReadMem sym (PartLLVMVal sym)
readMemArrayStore sym w end mop (LLVMPointer blk read_off) tp write_off arr size read_prev = do
  let loadFn :: SymBV sym w -> StorageType -> ReadMem sym (PartLLVMVal sym)
      loadFn base tp' = liftIO $ do
        let loadArrayByteFn :: Offset -> IO (PartLLVMVal sym)
            loadArrayByteFn off = do
              blk0 <- natLit sym 0
              idx <- bvAdd sym base =<< bvLit sym w (bytesToBV w off)
              byte <- arrayLookup sym arr $ Ctx.singleton idx
              return $ Partial.totalLLVMVal sym $ LLVMValInt blk0 byte
        genValueCtor sym end mop =<< loadTypedValueFromBytes 0 tp' loadArrayByteFn
  let varFn = ExprEnv read_off write_off size
  case (BV.asUnsigned <$> asBV read_off, BV.asUnsigned <$> asBV write_off) of
    -- In this case, both the read and write offsets are concrete
    (Just lo, Just so) -> do
      let subFn :: RangeLoad Addr Addr -> ReadMem sym (PartLLVMVal sym)
          subFn = \case
            OutOfRange o tp' -> do
              o' <- liftIO $ bvLit sym w $ bytesToBV w o
              read_prev tp' $ LLVMPointer blk o'
            InRange o tp' -> do
              o' <- liftIO $ bvLit sym w $ bytesToBV w o
              loadFn o' tp'
      case BV.asUnsigned <$> (asBV =<< size) of
        -- The size of the backing SMT array is also concrete, so we can generate a mux-free value
        Just concrete_size -> do
          let s = R (fromInteger so) (fromInteger (so + concrete_size))
          let vcr = rangeLoad (fromInteger lo) tp s
          liftIO . genValueCtor sym end mop =<< traverse subFn vcr
        -- Otherwise, the size of the array is unbounded or symbolic
        --
        -- The generated mux covers the possible cases where the read straddles
        -- the store in various configurations
        --
        -- FIXME/Question: Does this properly handle the unbounded array case? Does it
        -- need special handling of that case at all?
        _ -> evalMuxValueCtor sym w end mop varFn subFn $
          fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
    -- Otherwise, at least one of the offsets is symbolic (and we will have to generate additional muxes)
    _ -> do
      let subFn :: RangeLoad OffsetExpr IntExpr -> ReadMem sym (PartLLVMVal sym)
          subFn = \case
            OutOfRange o tp' -> do
              o' <- liftIO $ genOffsetExpr sym w varFn o
              read_prev tp' $ LLVMPointer blk o'
            InRange o tp' -> do
              o' <- liftIO $ genIntExpr sym w varFn o
              -- should always produce a defined value
              case o' of
                Just o'' -> loadFn o'' tp'
                Nothing  -> panic "Generic.readMemArrayStore"
                              [ "Unexpected unbounded size in RangeLoad"
                              , "*** Integer expression:  " ++ show o
                              , "*** Under environment:  " ++ show (ppExprEnv varFn)
                              ]
      let pref
            | Just{} <- BV.asUnsigned <$> asBV write_off = FixedStore
            | Just{} <- BV.asUnsigned <$> asBV read_off = FixedLoad
            | otherwise = NeitherFixed
      let rngLd
            -- if the size of the data is bounded, use symbolicRangeLoad
            | Just _  <- size = symbolicRangeLoad pref tp
            -- otherwise, use symbolicUnboundedRangeLoad
            | Nothing <- size = symbolicUnboundedRangeLoad pref tp
      evalMuxValueCtor sym w end mop varFn subFn rngLd

readMemInvalidate ::
  forall sym w .
  ( 1 <= w, IsSymInterface sym, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  sym -> NatRepr w ->
  EndianForm ->
  MemoryOp sym w ->
  LLVMPtr sym w {- ^ The loaded offset                   -} ->
  StorageType   {- ^ The type we are reading             -} ->
  SymBV sym w   {- ^ The destination of the invalidation -} ->
  Text          {- ^ The error message                   -} ->
  SymBV sym w   {- ^ The length of the set region        -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
  ReadMem sym (PartLLVMVal sym)
readMemInvalidate sym w end mop (LLVMPointer blk off) tp d msg sz readPrev =
  do let ld = BV.asUnsigned <$> asBV off
     let dd = BV.asUnsigned <$> asBV d
     let varFn = ExprEnv off d (Just sz)
     case (ld, dd) of
       -- Offset if known
       (Just lo, Just so) ->
         do let subFn :: RangeLoad Addr Addr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do
                  o' <- liftIO $ bvLit sym w (bytesToBV w o)
                  readPrev tp' (LLVMPointer blk o')
                subFn (InRange _o tp') =
                  readInRange tp'
            case BV.asUnsigned <$> asBV sz of
              Just csz -> do
                let s = R (fromInteger so) (fromInteger (so + csz))
                let vcr = rangeLoad (fromInteger lo) tp s
                liftIO . genValueCtor sym end mop =<< traverse subFn vcr
              _ -> evalMuxValueCtor sym w end mop varFn subFn $
                     fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
       -- Symbolic offsets
       _ ->
         do let subFn :: RangeLoad OffsetExpr IntExpr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do
                  o' <- liftIO $ genOffsetExpr sym w varFn o
                  readPrev tp' (LLVMPointer blk o')
                subFn (InRange _o tp') =
                  readInRange tp'
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- BV.asUnsigned <$> asBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end mop varFn subFn mux0
  where
    readInRange :: StorageType -> ReadMem sym (PartLLVMVal sym)
    readInRange tp'
      | laxLoadsAndStores ?memOpts &&
        indeterminateLoadBehavior ?memOpts == UnstableSymbolic
      = liftIO (Partial.totalLLVMVal sym <$> freshLLVMVal sym tp')
      | otherwise
      = liftIO (Partial.partErr sym mop $ Invalidated msg)

-- | Construct a value of a type that has no in-memory representation at all
buildEmptyVal :: StorageType -> Maybe (LLVMVal sym)
buildEmptyVal t =
  case storageTypeF t of
    Struct fields   -> LLVMValStruct <$> traverse emptyStorageField fields
    Array n eltTy
      | n == 0      -> Just (LLVMValArray eltTy V.empty)
      | otherwise   -> LLVMValArray eltTy . V.replicate (fromIntegral n) <$> buildEmptyVal eltTy
    X86_FP80        -> Nothing
    Float           -> Nothing
    Double          -> Nothing
    Bitvector {}    -> Nothing -- Bitvectors can't be empty; they have a non-zero size invariant
  where
    emptyStorageField field = (,) field <$> buildEmptyVal (field ^. fieldVal)

-- | Read a value from memory.
readMem :: forall sym w.
  ( 1 <= w, IsSymInterface sym, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  sym ->
  NatRepr w ->
  Maybe String ->
  LLVMPtr sym w ->
  StorageType ->
  Alignment ->
  Mem sym ->
  IO (PartLLVMVal sym)
readMem sym _ _ _ tp _ _
  -- no actual memory read happens when reading a value with
  -- no memory representation. This check comes up in
  -- particular when evaluating llvm_points_to statements
  -- in SAW script.
  | Just v <- buildEmptyVal tp = pure (Partial.totalLLVMVal sym v)
readMem sym w gsym l tp alignment m = do
  sz         <- bvLit sym w (bytesToBV w (typeEnd 0 tp))
  p1         <- isAllocated sym w alignment l (Just sz) m
  p2         <- isAligned sym w l alignment
  maybe_allocation_array <- asMemAllocationArrayStore sym w l m

  let mop = MemLoadOp tp gsym l m

  part_val <- case maybe_allocation_array of
    -- If this read is inside an allocation backed by a SMT array store,
    -- then decompose this read into reading the individual bytes and
    -- assembling them to obtain the value, without introducing any
    -- ite operations
    Just (ok, arr, _arr_sz) | Just True <- asConstantPred ok -> do
      let loadArrayByteFn :: Offset -> IO (PartLLVMVal sym)
          loadArrayByteFn off = do
            blk0 <- natLit sym 0
            idx <- bvAdd sym (llvmPointerOffset l)
              =<< bvLit sym w (bytesToBV w off)
            byte <- arrayLookup sym arr $ Ctx.singleton idx
            return $ Partial.totalLLVMVal sym $ LLVMValInt blk0 byte
      genValueCtor sym (memEndianForm m) mop
        =<< loadTypedValueFromBytes 0 tp loadArrayByteFn
    -- Otherwise, fall back to the less-optimized read case
    _ -> readMem' sym w (memEndianForm m) gsym l m tp alignment (memWrites m)

  let stack = getCallStack (m ^. memState)
  part_val' <- applyUnless (laxLoadsAndStores ?memOpts)
                           (Partial.attachSideCondition sym stack p2 (UB.ReadBadAlignment (RV l) alignment))
                           part_val
  applyUnless (laxLoadsAndStores ?memOpts)
              (Partial.attachMemoryError sym p1 mop UnreadableRegion)
              part_val'

data CacheEntry sym w =
  CacheEntry !(StorageType) !(SymNat sym) !(SymBV sym w)

instance (TestEquality (SymExpr sym)) => Eq (CacheEntry sym w) where
  (CacheEntry tp1 blk1 off1) == (CacheEntry tp2 blk2 off2) =
    tp1 == tp2 && (blk1 == blk2) && (isJust $ testEquality off1 off2)

instance IsSymInterface sym => Ord (CacheEntry sym w) where
  compare (CacheEntry tp1 blk1 off1) (CacheEntry tp2 blk2 off2) =
    compare tp1 tp2
      `mappend` compare blk1 blk2
      `mappend` toOrdering (compareF off1 off2)

toCacheEntry :: StorageType -> LLVMPtr sym w -> CacheEntry sym w
toCacheEntry tp (llvmPointerView -> (blk, bv)) = CacheEntry tp blk bv


-- | Read a value from memory given a list of writes.
--
-- Note that the case where a read is entirely backed by an SMT array store is
-- handled in 'readMem'.
readMem' ::
  forall w sym.
  ( 1 <= w, IsSymInterface sym, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  Maybe String ->
  LLVMPtr sym w  {- ^ Address we are reading            -} ->
  Mem sym        {- ^ The original memory state         -} ->
  StorageType    {- ^ The type to read from memory      -} ->
  Alignment      {- ^ Alignment of pointer to read from -} ->
  MemWrites sym  {- ^ List of writes                    -} ->
  IO (PartLLVMVal sym)
readMem' sym w end gsym l0 origMem tp0 alignment (MemWrites ws) =
   do runReadMem (go fallback0 l0 tp0 [] ws)
  where
    mop = MemLoadOp tp0 gsym l0 origMem

    fallback0 ::
      StorageType ->
      LLVMPtr sym w ->
      ReadMem sym (PartLLVMVal sym)
    fallback0 tp _l =
      liftIO $
        if laxLoadsAndStores ?memOpts
           && indeterminateLoadBehavior ?memOpts == UnstableSymbolic
        then Partial.totalLLVMVal sym <$> freshLLVMVal sym tp
        else do -- We're playing a trick here.  By making a fresh constant a proof obligation, we can be
                -- sure it always fails.  But, because it's a variable, it won't be constant-folded away
                -- and we can be relatively sure the annotation will survive.
                b <- if noSatisfyingWriteFreshConstant ?memOpts
                  then freshConstant sym (safeSymbol "noSatisfyingWrite") BaseBoolRepr
                  else return $ falsePred sym
                Partial.Err <$>
                  Partial.annotateME sym mop (NoSatisfyingWrite tp) b

    go :: (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
          LLVMPtr sym w ->
          StorageType ->
          [MemWrite sym] ->
          [MemWritesChunk sym] ->
          ReadMem sym (PartLLVMVal sym)
    go fallback l tp [] [] = fallback tp l
    go fallback l tp [] (head_chunk : tail_chunks) =
      go fallback l tp (memWritesChunkAt l head_chunk) tail_chunks
    go fallback l tp (h : r) rest_chunks =
      do cache <- liftIO $ newIORef Map.empty
         let readPrev ::
               StorageType ->
               LLVMPtr sym w ->
               ReadMem sym (PartLLVMVal sym)
             readPrev tp' l' = do
               m <- liftIO $ readIORef cache
               case Map.lookup (toCacheEntry tp' l') m of
                 Just x -> return x
                 Nothing -> do
                   x <- go fallback l' tp' r rest_chunks
                   liftIO $ writeIORef cache $ Map.insert (toCacheEntry tp' l') x m
                   return x
         case h of
           WriteMerge _ (MemWrites []) (MemWrites []) ->
             go fallback l tp r rest_chunks
           WriteMerge c (MemWrites xr) (MemWrites yr) ->
             do x <- go readPrev l tp [] xr
                y <- go readPrev l tp [] yr
                liftIO $ Partial.muxLLVMVal sym c x y
           MemWrite dst wsrc ->
             case testEquality (ptrWidth dst) w of
               Nothing   -> readPrev tp l
               Just Refl ->
                 do let LLVMPointer blk1 _ = l
                    let LLVMPointer blk2 d = dst
                    let readCurrent =
                          case wsrc of
                            MemCopy src sz -> readMemCopy sym w end mop l tp d src sz readPrev
                            MemSet v sz    -> readMemSet sym w end mop l tp d v sz readPrev
                            MemStore v stp storeAlign -> readMemStore sym w end mop l tp d v stp alignment storeAlign readPrev
                            MemArrayStore arr sz -> readMemArrayStore sym w end mop l tp d arr sz readPrev
                            MemInvalidate msg sz -> readMemInvalidate sym w end mop l tp d msg sz readPrev
                    sameBlock <- liftIO $ natEq sym blk1 blk2
                    case asConstantPred sameBlock of
                      Just True  -> do
                        result <- readCurrent
                        pure result
                      Just False -> readPrev tp l
                      Nothing ->
                        do x <- readCurrent
                           y <- readPrev tp l
                           liftIO $ Partial.muxLLVMVal sym sameBlock x y

--------------------------------------------------------------------------------

-- | Dummy newtype for now...
--   It may be useful later to add additional plumbing
--   to this monad.
newtype ReadMem sym a = ReadMem { runReadMem :: IO a }
  deriving (Applicative, Functor, Monad, MonadIO)


--------------------------------------------------------------------------------

memWritesSize :: MemWrites sym -> Int
memWritesSize (MemWrites writes) = getSum $ foldMap
  (\case
    MemWritesChunkIndexed indexed_writes ->
      foldMap (Sum . length) indexed_writes
    MemWritesChunkFlat flat_writes -> Sum $ length flat_writes)
  writes

muxChanges :: IsExpr (SymExpr sym) => Pred sym -> MemChanges sym -> MemChanges sym -> MemChanges sym
muxChanges c (left_allocs, lhs_writes) (rhs_allocs, rhs_writes) =
  ( muxMemAllocs c left_allocs rhs_allocs
  , muxWrites c lhs_writes rhs_writes
  )

muxWrites :: IsExpr (SymExpr sym) => Pred sym -> MemWrites sym -> MemWrites sym -> MemWrites sym
muxWrites _ (MemWrites []) (MemWrites []) = MemWrites []

muxWrites c lhs_writes rhs_writes
  | Just b <- asConstantPred c = if b then lhs_writes else rhs_writes

muxWrites c lhs_writes rhs_writes
  | Just lhs_indexed_writes <- asIndexedChunkMap lhs_writes
  , Just rhs_indexed_writes <- asIndexedChunkMap rhs_writes =
      MemWrites
        [ MemWritesChunkIndexed $
            mergeMemWritesChunkIndexed
              (\lhs rhs ->
                 [ WriteMerge
                     c
                     (MemWrites [MemWritesChunkFlat lhs])
                     (MemWrites [MemWritesChunkFlat rhs])
                 ])
              lhs_indexed_writes
              rhs_indexed_writes
        ]
  | otherwise =
    MemWrites [MemWritesChunkFlat [WriteMerge c lhs_writes rhs_writes]]
  where asIndexedChunkMap :: MemWrites sym -> Maybe (IntMap [MemWrite sym])
        asIndexedChunkMap (MemWrites [MemWritesChunkIndexed m]) = Just m
        asIndexedChunkMap (MemWrites []) = Just IntMap.empty
        asIndexedChunkMap _ = Nothing

mergeMemWritesChunkIndexed ::
  ([MemWrite sym] -> [MemWrite sym] -> [MemWrite sym]) ->
  IntMap [MemWrite sym] ->
  IntMap [MemWrite sym] ->
  IntMap [MemWrite sym]
mergeMemWritesChunkIndexed merge_func = IntMap.mergeWithKey
  (\_ lhs_alloc_writes rhs_alloc_writes -> Just $
    merge_func lhs_alloc_writes rhs_alloc_writes)
  (IntMap.map $ \lhs_alloc_writes -> merge_func lhs_alloc_writes [])
  (IntMap.map $ \rhs_alloc_writes -> merge_func [] rhs_alloc_writes)

memChanges :: Monoid m => (MemChanges sym -> m) -> Mem sym -> m
memChanges f m = go (m^.memState)
  where go (EmptyMem _ _ l)      = f l
        go (StackFrame _ _ _ l s)  = f l <> go s
        go (BranchFrame _ _ l s) = f l <> go s

memAllocs :: Mem sym -> MemAllocs sym
memAllocs = memChanges fst

memWrites :: Mem sym -> MemWrites sym
memWrites = memChanges snd

memWritesChunkAt ::
  IsExprBuilder sym =>
  LLVMPtr sym w ->
  MemWritesChunk sym ->
  [MemWrite sym]
memWritesChunkAt ptr = \case
  MemWritesChunkIndexed indexed_writes
    | Just blk <- asNat (llvmPointerBlock ptr) ->
      IntMap.findWithDefault [] (fromIntegral blk) indexed_writes
    | otherwise -> IntMap.foldr (++) [] indexed_writes
  MemWritesChunkFlat flat_writes -> flat_writes

memWritesAtConstant :: Natural -> MemWrites sym -> [MemWrite sym]
memWritesAtConstant blk (MemWrites writes) = foldMap
  (\case
    MemWritesChunkIndexed indexed_writes ->
      IntMap.findWithDefault [] (fromIntegral blk) indexed_writes
    MemWritesChunkFlat flat_writes -> flat_writes)
  writes

memStateAllocCount :: MemState sym -> Int
memStateAllocCount s = case s of
  EmptyMem ac _ _ -> ac
  StackFrame ac _ _ _ _ -> ac
  BranchFrame ac _ _ _ -> ac

memStateWriteCount :: MemState sym -> Int
memStateWriteCount s = case s of
  EmptyMem _ wc _ -> wc
  StackFrame _ wc _ _ _ -> wc
  BranchFrame _ wc _ _ -> wc

memAllocCount :: Mem sym -> Int
memAllocCount m = memStateAllocCount (m ^. memState)

memWriteCount :: Mem sym -> Int
memWriteCount m = memStateWriteCount (m ^. memState)

memAddAlloc :: (MemAllocs sym -> MemAllocs sym) -> Mem sym -> Mem sym
memAddAlloc f = memState %~ \case
  EmptyMem ac wc (a, w) -> EmptyMem (ac+1) wc (f a, w)
  StackFrame ac wc nm (a, w) s -> StackFrame (ac+1) wc nm (f a, w) s
  BranchFrame ac wc (a, w) s -> BranchFrame (ac+1) wc (f a, w) s

memAddWrite ::
  (IsExprBuilder sym, 1 <= w) =>
  LLVMPtr sym w ->
  WriteSource sym w ->
  Mem sym ->
  Mem sym
memAddWrite ptr src = do
  let single_write = memWritesSingleton ptr src
  memState %~ \case
    EmptyMem ac wc (a, w) ->
      EmptyMem ac (wc+1) (a, single_write <> w)
    StackFrame ac wc nm (a, w) s ->
      StackFrame ac (wc+1) nm (a, single_write <> w) s
    BranchFrame ac wc (a, w) s ->
      BranchFrame ac (wc+1) (a, single_write <> w) s

memStateAddChanges :: MemChanges sym -> MemState sym -> MemState sym
memStateAddChanges (a, w) = \case
  EmptyMem ac wc (a0, w0) ->
    EmptyMem (sizeMemAllocs a + ac) (memWritesSize w + wc) (a <> a0, w <> w0)
  StackFrame ac wc nm (a0, w0) s ->
    StackFrame (sizeMemAllocs a + ac) (memWritesSize w + wc) nm (a <> a0, w <> w0) s
  BranchFrame ac wc (a0, w0) s ->
    BranchFrame (sizeMemAllocs a + ac) (memWritesSize w + wc) (a <> a0, w <> w0) s


--------------------------------------------------------------------------------
-- Pointer validity

-- | @isAllocatedMut isMut sym w p sz m@ returns the condition required to
-- prove range @[p..p+sz)@ lies within a single allocation in @m@.
--
-- This function is parameterized by a predicate on the mutability, so
-- it can optionally be restricted to mutable regions only.
-- It is also parameterized by a required alignment; only allocations
-- with at least this level of alignment are considered.
--
-- NB this algorithm is set up to explicitly allow both zero size allocations
-- and zero-size chunks to be checked for validity.  When 'sz' is 0, every pointer
-- that is inside the range of the allocation OR ONE PAST THE END are considered
-- "allocated"; this is intended, as it captures C's behavior regarding valid
-- pointers.
isAllocatedMut ::
  forall sym w .
  (1 <= w, IsSymInterface sym) =>
  (Mutability -> Bool) ->
  sym -> NatRepr w     ->
  Alignment            ->
  LLVMPtr sym w        ->
  Maybe (SymBV sym w)  ->
  Mem sym              ->
  IO (Pred sym)
isAllocatedMut mutOk sym w minAlign (llvmPointerView -> (blk, off)) sz m =
  do (wasAllocated, notFreed) <- isAllocatedGeneric sym inAllocation blk (memAllocs m)
     andPred sym wasAllocated notFreed
  where
    inAllocation :: AllocInfo sym -> IO (Pred sym)
    inAllocation (AllocInfo _ asz mut alignment _)
      | mutOk mut && alignment >= minAlign = inBounds asz
      | otherwise = pure (falsePred sym)

    -- @inBounds a allocatedSz@ produces the predicate that
    -- records whether the pointer @ptr@ of size @sz@ falls within the
    -- allocation of block @a@ of size @allocatedSz@.
    inBounds :: forall w'. Maybe (SymBV sym w') -> IO (Pred sym)
    inBounds Nothing =
      case sz of
        Nothing ->
          -- Unbounded access of an unbounded allocation must start at offset 0.
          bvEq sym off =<< bvZero sym w
        Just currSize ->
          -- Bounded access of an unbounded allocation requires that
          -- @offset + size <= 2^w@, or equivalently @offset <= 2^w -
          -- size@. Note that @bvNeg sym size@ computes @2^w - size@
          -- for any nonzero @size@.
          do zeroSize <- bvEq sym currSize =<< bvZero sym w
             noWrap <- bvUle sym off =<< bvNeg sym currSize
             orPred sym zeroSize noWrap

    inBounds (Just allocSize)
      -- If the allocation is done at pointer width is equal to @w@, check
      -- if this allocation covers the required range
      | Just Refl <- testEquality w (bvWidth allocSize)
      , Just currSize <- sz =
        do smallSize <- bvUle sym currSize allocSize    -- currSize <= allocSize
           maxOffset <- bvSub sym allocSize currSize    -- maxOffset = allocSize - currSize
           inRange   <- bvUle sym off maxOffset         -- offset(ptr) <= maxOffset
           andPred sym smallSize inRange

    inBounds (Just _allocSize)
      -- If the allocation is done at pointer width not equal to @w@,
      -- then this is not the allocation we're looking for. Similarly,
      -- if @sz@ is @Nothing@ (indicating we are accessing the entire
      -- address space) then any bounded allocation is too small.
      | otherwise = return $ falsePred sym

-- | @isAllocated sym w p sz m@ returns the condition required to prove
-- range @[p..p+sz)@ lies within a single allocation in @m@.
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
  Maybe (SymBV sym w) ->
  Mem sym          ->
  IO (Pred sym)
isAllocated = isAllocatedMut (const True)

-- | @isAllocatedMutable sym w p sz m@ returns the condition required
-- to prove range @[p..p+sz)@ lies within a single /mutable/
-- allocation in @m@.
isAllocatedMutable ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w -> Alignment -> LLVMPtr sym w -> Maybe (SymBV sym w) -> Mem sym -> IO (Pred sym)
isAllocatedMutable = isAllocatedMut (== Mutable)

-- | Return the condition required to prove that the pointer points to
-- a range of 'size' bytes that falls within an allocated region of
-- the appropriate mutability, and also that the pointer is
-- sufficiently aligned.
isAllocatedAlignedPointer ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  Alignment           {- ^ minimum required pointer alignment                 -} ->
  Mutability          {- ^ 'Mutable' means pointed-to region must be writable -} ->
  LLVMPtr sym w       {- ^ pointer                                            -} ->
  Maybe (SymBV sym w) {- ^ size (@Nothing@ means entire address space)        -} ->
  Mem sym             {- ^ memory                                             -} ->
  IO (Pred sym)
isAllocatedAlignedPointer sym w alignment mutability ptr size mem =
  do p1 <- isAllocatedMut mutOk sym w alignment ptr size mem
     p2 <- isAligned sym w ptr alignment
     andPred sym p1 p2
  where
    mutOk m =
      case mutability of
        Mutable -> m == Mutable
        Immutable -> True

-- | @isValidPointer sym w b m@ returns the condition required to prove that @p@
--   is a valid pointer in @m@. This means that @p@ is in the range of some
--   allocation OR ONE PAST THE END of an allocation. In other words @p@ is a
--   valid pointer if @b <= p <= b+sz@ for some allocation at base @b@ of size
--   @Just sz@, or if @b <= p@ for some allocation of size @Nothing@. Note that,
--   even though @b+sz@ is outside the allocation range of the allocation
--   (loading through it will fail) it is nonetheless a valid pointer value.
--   This strange special case is baked into the C standard to allow certain
--   common coding patterns to be defined.
isValidPointer :: (1 <= w, IsSymInterface sym)
        => sym -> NatRepr w -> LLVMPtr sym w -> Mem sym -> IO (Pred sym)
isValidPointer sym w p m = do
   sz <- constOffset sym w 0
   isAllocated sym w noAlignment p (Just sz) m
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
  | Some bits <- mkNatRepr (alignmentToExponent a)
  , Just LeqProof <- isPosNat bits
  , Just LeqProof <- testLeq bits w =
    do lowbits <- bvSelect sym (knownNat :: NatRepr 0) bits offset
       bvEq sym lowbits =<< bvZero sym bits
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
  (IsSymInterface sym) =>
  sym ->
  LLVMPtr sym w ->
  LLVMPtr sym w ->
  Mem sym ->
  IO (Pred sym)
notAliasable sym (llvmPointerView -> (blk1, _)) (llvmPointerView -> (blk2, _)) mem =
  do p0 <- natEq sym blk1 blk2
     (wasAllocated1, notFreed1) <- isAllocatedGeneric sym isMutable blk1 (memAllocs mem)
     (wasAllocated2, notFreed2) <- isAllocatedGeneric sym isMutable blk2 (memAllocs mem)
     allocated1 <- andPred sym wasAllocated1 notFreed1
     allocated2 <- andPred sym wasAllocated2 notFreed2
     orPred sym p0 =<< orPred sym allocated1 allocated2
  where
    isMutable :: AllocInfo sym -> IO (Pred sym)
    isMutable (AllocInfo _ _ Mutable _ _) = pure (truePred sym)
    isMutable (AllocInfo _ _ Immutable _ _) = pure (falsePred sym)

--------------------------------------------------------------------------------
-- Other memory operations

-- | Write a value to memory.
--
-- The returned predicates assert (in this order):
--  * the pointer falls within an allocated, mutable memory region
--  * the pointer's alignment is correct
writeMem :: ( 1 <= w
            , IsSymInterface sym
            , HasLLVMAnn sym
            , ?memOpts :: MemOptions )
         => sym -> NatRepr w
         -> Maybe String
         -> LLVMPtr sym w
         -> StorageType
         -> Alignment
         -> LLVMVal sym
         -> Mem sym
         -> IO (Mem sym, Pred sym, Pred sym)
writeMem = writeMemWithAllocationCheck isAllocatedMutable

-- | Write a value to any memory region, mutable or immutable.
--
-- The returned predicates assert (in this order):
--  * the pointer falls within an allocated memory region
--  * the pointer's alignment is correct
writeConstMem ::
  ( 1 <= w
  , IsSymInterface sym
  , HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  sym           ->
  NatRepr w     ->
  Maybe String  ->
  LLVMPtr sym w ->
  StorageType   ->
  Alignment     ->
  LLVMVal sym   ->
  Mem sym       ->
  IO (Mem sym, Pred sym, Pred sym)
writeConstMem = writeMemWithAllocationCheck isAllocated

-- | Write a value to memory.
--
-- The returned predicates assert (in this order):
--  * the pointer satisfies the checks specified by
--    the @is_allocated@ function
--  * the pointer's alignment is correct
writeMemWithAllocationCheck ::
  forall sym w .
  ( IsSymInterface sym
  , HasLLVMAnn sym
  , 1 <= w
  , ?memOpts :: MemOptions ) =>
  (sym -> NatRepr w -> Alignment -> LLVMPtr sym w -> Maybe (SymBV sym w) -> Mem sym -> IO (Pred sym)) ->
  sym ->
  NatRepr w ->
  Maybe String ->
  LLVMPtr sym w ->
  StorageType ->
  Alignment ->
  LLVMVal sym ->
  Mem sym ->
  IO (Mem sym, Pred sym, Pred sym)
writeMemWithAllocationCheck is_allocated sym w gsym ptr tp alignment val mem = do
  let mop = MemStoreOp tp gsym ptr mem
  let sz = typeEnd 0 tp
  sz_bv <- constOffset sym w sz
  p1 <- is_allocated sym w alignment ptr (Just sz_bv) mem
  p2 <- isAligned sym w ptr alignment
  maybe_allocation_array <- asMemAllocationArrayStore sym w ptr mem
  mem' <- case maybe_allocation_array of
    -- if this write is inside an allocation backed by a SMT array store and
    -- the value is not a pointer, then decompose this write into disassembling
    -- the value to individual bytes, writing them in the SMT array, and
    -- writing the updated SMT array in the memory
    Just (ok, arr, arr_sz) | Just True <- asConstantPred ok
                           , case val of
                               LLVMValInt block _ -> (asNat block) == (Just 0)
                               _ -> True -> do
      let -- Return @Just value@ if we have successfully loaded a value and
          -- should update the corresponding index in the array with that
          -- value. Return @Nothing@ otherwise.
          subFn :: ValueLoad Addr -> IO (Maybe (PartLLVMVal sym))
          subFn = \case
            LastStore val_view -> fmap Just $ applyView
              sym
              (memEndianForm mem)
              mop
              (Partial.totalLLVMVal sym val)
              val_view
            InvalidMemory tp'
              |  -- With stable-symbolic, loading struct padding is
                 -- permissible. This is the only case that can return
                 -- Nothing.
                 laxLoadsAndStores ?memOpts
              ,  indeterminateLoadBehavior ?memOpts == StableSymbolic
              -> pure Nothing

              |  otherwise
              -> fmap Just $ Partial.partErr sym mop $ Invalid tp'
            OldMemory off _ -> panic "Generic.writeMemWithAllocationCheck"
              [ "Unexpected offset in storage type"
              , "*** Offset:  " ++ show off
              , "*** StorageType:  " ++ show tp
              ]

          -- Given a symbolic array and an index into the array, load a byte
          -- from the corresponding position in memory and store the byte into
          -- the array at that index.
          storeArrayByteFn ::
            SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) ->
            Offset ->
            IO (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8))
          storeArrayByteFn acc_arr off = do
            vc <- traverse subFn (loadBitvector off 1 0 (ValueViewVar tp))
            mb_partial_byte <- traverse (genValueCtor sym (memEndianForm mem) mop)
                                        (sequenceA vc)

            case mb_partial_byte of
              Nothing ->
                -- If we cannot load the byte from memory, skip updating the
                -- array. Currently, the only way that this can arise is when
                -- a byte of struct padding is loaded with StableSymbolic
                -- enabled.
                pure acc_arr
              Just partial_byte ->
                case partial_byte of
                  Partial.NoErr _ (LLVMValInt _ byte)
                    | Just Refl <- testEquality (knownNat @8) (bvWidth byte) -> do
                      idx <- bvAdd sym (llvmPointerOffset ptr)
                        =<< bvLit sym w (bytesToBV w off)
                      arrayUpdate sym acc_arr (Ctx.singleton idx) byte

                  Partial.NoErr _ (LLVMValZero _) -> do
                      byte <- bvZero sym knownRepr
                      idx <- bvAdd sym (llvmPointerOffset ptr)
                        =<< bvLit sym w (bytesToBV w off)
                      arrayUpdate sym acc_arr (Ctx.singleton idx) byte

                  Partial.NoErr _ v ->
                      panic "writeMemWithAllocationCheck"
                             [ "Expected byte value when updating SMT array, but got:"
                             , show v
                             ]
                  Partial.Err p ->
                      panic "writeMemWithAllocationCheck"
                             [ "Expected succesful byte load when updating SMT array"
                             , "but got an error instead:"
                             , show (printSymExpr p)
                             ]

      res_arr <- foldM storeArrayByteFn arr [0 .. (sz - 1)]
      overwriteArrayMem sym w ptr res_arr arr_sz mem

    _ -> return $ memAddWrite ptr (MemStore val tp alignment) mem

  return (mem', p1, p2)

-- | Overwrite SMT array.
--
-- In this case, we have generated an updated SMT array with all of
-- the changes needed to reflect this memory write.  Instead of adding
-- each individual byte write to the write log, we add a single entry that
-- shadows the entire SMT array in memory. This means that the next lookup
-- of e.g., a 4 byte read will see the updated array and be able to read 4
-- bytes from this array instead of having to traverse the write history
-- to find four different `MemStore`s.
--
-- Note that the pointer we write to is the *base* pointer (i.e., with
-- offset zero), since we are shadowing the *entire* array.
overwriteArrayMem ::
  (1 <= w, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym w ->
  SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) ->
  SymBV sym w ->
  Mem sym ->
  IO (Mem sym)
overwriteArrayMem sym w ptr arr sz mem = do
  basePtr <- LLVMPointer (llvmPointerBlock ptr) <$> bvLit sym w (BV.mkBV w 0)
  return $ memAddWrite basePtr (MemArrayStore arr (Just sz)) mem

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
  do p1 <- isAllocated sym w noAlignment src (Just sz) m
     p2 <- isAllocatedMutable sym w noAlignment dst (Just sz) m
     dst_maybe_allocation_array <- asMemAllocationArrayStore sym w dst m
     src_maybe_allocation_array <- asMemAllocationArrayStore sym w src m
     m' <- case (dst_maybe_allocation_array, src_maybe_allocation_array) of
       -- if both the dst and src of this copy operation are inside allocations
       -- backed by SMT array stores, then replace this copy operation with
       -- using SMT array copy, and writing the result SMT array in the memory
       (Just (dst_ok, dst_arr, dst_arr_sz), Just (src_ok, src_arr, _src_arr_sz))
         | Just True <- asConstantPred dst_ok
         , Just True <- asConstantPred src_ok ->
           do res_arr <- arrayCopy sym dst_arr (llvmPointerOffset dst) src_arr (llvmPointerOffset src) sz
              overwriteArrayMem sym w dst res_arr dst_arr_sz m

       _ -> return $ memAddWrite dst (MemCopy src sz) m

     return (m', p1, p2)

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
  do p <- isAllocatedMutable sym w noAlignment ptr (Just sz) m
     maybe_allocation_array <- asMemAllocationArrayStore sym w ptr m
     m' <- case maybe_allocation_array of
       -- if this set operation is inside an allocation backed by a SMT array
       -- store, then replace this set operation with using SMT array set, and
       -- writing the result SMT array in the memory
       Just (ok, arr, arr_sz) | Just True <- asConstantPred ok ->
         do res_arr <- arraySet sym arr (llvmPointerOffset ptr) val sz
            overwriteArrayMem sym w ptr res_arr arr_sz m

       _ -> return $ memAddWrite ptr (MemSet val sz) m

     return (m', p)

writeArrayMemWithAllocationCheck ::
  (IsSymInterface sym, 1 <= w) =>
  (sym -> NatRepr w -> Alignment -> LLVMPtr sym w -> Maybe (SymBV sym w) -> Mem sym -> IO (Pred sym)) ->
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Pointer -} ->
  Alignment ->
  SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ Array value -} ->
  Maybe (SymBV sym w) {- ^ Array size; if @Nothing@, the size is unrestricted -} ->
  Mem sym -> IO (Mem sym, Pred sym, Pred sym)
writeArrayMemWithAllocationCheck is_allocated sym w ptr alignment arr sz m =
  do p1 <- is_allocated sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     let default_m = memAddWrite ptr (MemArrayStore arr sz) m
     maybe_allocation_array <- asMemAllocationArrayStore sym w ptr m
     m' <- case maybe_allocation_array of
       -- if this write is inside an allocation backed by a SMT array store,
       -- then replace this copy operation with using SMT array copy, and
       -- writing the result SMT array in the memory
       Just (ok, alloc_arr, alloc_sz)
         | Just True <- asConstantPred ok, Just arr_sz <- sz ->
         do sz_diff <- bvSub sym alloc_sz arr_sz
            case asBV sz_diff of
              Just (BV.BV 0) -> return default_m
              _ ->
                do zero_off <- bvLit sym w $ BV.mkBV w 0
                   res_arr <- arrayCopy sym alloc_arr (llvmPointerOffset ptr) arr zero_off arr_sz
                   overwriteArrayMem sym w ptr res_arr alloc_sz m

       _ -> return default_m

     return (memInsertArrayBlock (llvmPointerBlock ptr) m', p1, p2)

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
  Maybe (SymBV sym w) {- ^ Array size; if @Nothing@, the size is unrestricted -} ->
  Mem sym -> IO (Mem sym, Pred sym, Pred sym)
writeArrayMem = writeArrayMemWithAllocationCheck isAllocatedMutable

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
  Maybe (SymBV sym w) {- ^ Array size -} ->
  Mem sym -> IO (Mem sym, Pred sym, Pred sym)
writeArrayConstMem = writeArrayMemWithAllocationCheck isAllocated

-- | Explicitly invalidate a region of memory.
invalidateMem ::
  (1 <= w, IsSymInterface sym) =>
  sym -> NatRepr w ->
  LLVMPtr sym w {- ^ Pointer -} ->
  Text          {- ^ Message -} ->
  SymBV sym w   {- ^ Number of bytes to set -} ->
  Mem sym -> IO (Mem sym, Pred sym)
invalidateMem sym w ptr msg sz m =
  do p <- isAllocatedMutable sym w noAlignment ptr (Just sz) m
     return (memAddWrite ptr (MemInvalidate msg sz) m, p)

-- | Allocate a new empty memory region.
allocMem :: (1 <= w) =>
            AllocType -- ^ Type of allocation
         -> Natural -- ^ Block id for allocation
         -> Maybe (SymBV sym w) -- ^ Size
         -> Alignment
         -> Mutability -- ^ Is block read-only
         -> String -- ^ Source location
         -> Mem sym
         -> Mem sym
allocMem a b sz alignment mut loc =
  memAddAlloc (allocMemAllocs b (AllocInfo a sz mut alignment loc))

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
  do sz <- bvLit sym w (bytesToBV w (typeEnd 0 tp))
     base <- natLit sym b
     off <- bvZero sym w
     let p = LLVMPointer base off
     return (m & allocMem a b (Just sz) alignment mut loc
               & memAddWrite p (MemStore v tp alignment))

pushStackFrameMem :: Text -> Mem sym -> Mem sym
pushStackFrameMem nm = memState %~ \s ->
  StackFrame (memStateAllocCount s) (memStateWriteCount s) nm emptyChanges s

popStackFrameMem :: forall sym. Mem sym -> Mem sym
popStackFrameMem m = m & memState %~ popf
  where popf :: MemState sym -> MemState sym
        popf (StackFrame _ _ _ (a,w) s) =
          s & memStateAddChanges c
          where c = (popMemAllocs a, w)

        -- WARNING: The following code executes a stack pop underneath a branch
        -- frame.  This is necessary to get merges to work correctly
        -- when they propagate all the way to function returns.
        -- However, it is not clear that the following code is
        -- precisely correct because it may leave in place writes to
        -- memory locations that have just been popped off the stack.
        -- This does not appear to be causing problems for our
        -- examples, but may be a source of subtle errors.
        popf (BranchFrame _ wc (a,w) s) =
          BranchFrame (sizeMemAllocs (fst c)) wc c $ popf s
          where c = (popMemAllocs a, w)

        popf EmptyMem{} = error "popStackFrameMem given unexpected memory"


-- | Free a heap-allocated block of memory.
--
-- The returned predicates assert (in this order):
--  * the pointer points to the base of a block
--  * said block was heap-allocated, and mutable
--  * said block was not previously freed
--
-- Because the LLVM memory model allows immutable blocks to alias each other,
-- freeing an immutable block could lead to unsoundness.
freeMem :: forall sym w .
  (1 <= w, IsSymInterface sym) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym w {- ^ Base of allocation to free -} ->
  Mem sym ->
  String {- ^ Source location -} ->
  IO (Mem sym, Pred sym, Pred sym, Pred sym)
freeMem sym w (LLVMPointer blk off) m loc =
  do p1 <- bvEq sym off =<< bvZero sym w
     (wasAllocated, notFreed) <- isAllocatedGeneric sym isHeapMutable blk (memAllocs m)
     return (memAddAlloc (freeMemAllocs blk loc) m, p1, wasAllocated, notFreed)
  where
    isHeapMutable :: AllocInfo sym -> IO (Pred sym)
    isHeapMutable (AllocInfo HeapAlloc _ Mutable _ _) = pure (truePred sym)
    isHeapMutable _ = pure (falsePred sym)

-- | Prepare memory so that it can later be merged via 'mergeMem'.
--
-- This is primarily intended for use in the implementation of
-- 'Lang.Crucible.Simulator.Intrinsics.pushBranchIntrinsic' for LLVM memory.
-- It would be nice to remove this someday, see #890.
--
-- For more information about branching and merging, see the comment on 'Mem'.
branchMem :: Mem sym -> Mem sym
branchMem = memState %~ \s ->
  BranchFrame (memStateAllocCount s) (memStateWriteCount s) emptyChanges s

-- | Remove the top 'BranchFrame', adding changes to the underlying memory.
--
-- This is primarily intended for use in the implementation of
-- 'Lang.Crucible.Simulator.Intrinsics.abortBranchIntrinsic' for LLVM memory.
branchAbortMem :: Mem sym -> Mem sym
branchAbortMem = memState %~ popf
  where popf (BranchFrame _ _ c s) = s & memStateAddChanges c
        popf _ = error "branchAbortMem given unexpected memory"

-- | Merge memory that was previously prepared via 'branchMem'.
--
-- This is primarily intended for use in the implementation of
-- 'Lang.Crucible.Simulator.Intrinsics.muxIntrinsic' for LLVM memory.
--
-- For more information about branching and merging, see the comment on 'Mem'.
mergeMem :: IsExpr (SymExpr sym) => Pred sym -> Mem sym -> Mem sym -> Mem sym
mergeMem c x y =
  case (x^.memState, y^.memState) of
    (BranchFrame _ _ a s, BranchFrame _ _ b s') ->
      -- The memories to be merged must have originated from the same memory,
      -- and in particular, should have matching alloc/write counts.
      let allocsEq = memStateAllocCount s == memStateAllocCount s' in
      let writesEq = memStateWriteCount s == memStateWriteCount s' in
      X.assert (allocsEq && writesEq) $
        let s' = s & memStateAddChanges (muxChanges c a b)
        in x & memState .~ s'
    _ -> error "mergeMem given unexpected memories"

--------------------------------------------------------------------------------
-- Finding allocations

-- When we have a concrete allocation number, we can ask more specific questions
-- to the solver and get (overapproximate) concrete answers.

data SomeAlloc sym =
  forall w. (1 <= w) => SomeAlloc AllocType Natural (Maybe (SymBV sym w)) Mutability Alignment String

instance IsSymInterface sym => Eq (SomeAlloc sym) where
  SomeAlloc x_atp x_base x_sz x_mut x_alignment x_loc == SomeAlloc y_atp y_base y_sz y_mut y_alignment y_loc = do
    let sz_eq = case (x_sz, y_sz) of
          (Just x_bv, Just y_bv) -> isJust $ testEquality x_bv y_bv
          (Nothing, Nothing) -> True
          _ -> False
    x_atp == y_atp && x_base == y_base && sz_eq && x_mut == y_mut && x_alignment == y_alignment && x_loc == y_loc

ppSomeAlloc :: forall sym ann. IsExprBuilder sym => SomeAlloc sym -> Doc ann
ppSomeAlloc (SomeAlloc atp base sz mut alignment loc) =
  ppAllocInfo (base, AllocInfo atp sz mut alignment loc :: AllocInfo sym)

-- | Find an overapproximation of the set of allocations with this number.
possibleAllocs ::
  forall sym .
  (IsSymInterface sym) =>
  Natural              ->
  Mem sym              ->
  [SomeAlloc sym]
possibleAllocs n mem =
  case possibleAllocInfo n (memAllocs mem) of
    Nothing -> []
    Just (AllocInfo atp sz mut alignment loc) ->
      [SomeAlloc atp n sz mut alignment loc]

-- | 'IO' plus memoization. The 'IORef' stores suspended computations with
-- 'Left' and evaluated results with 'Right'.
newtype MemoIO m a = MemoIO (IORef (Either (m a) a))

putMemoIO :: MonadIO m => m a -> m (MemoIO m a)
putMemoIO comp = MemoIO <$> liftIO (newIORef $ Left comp)

getMemoIO :: MonadIO m => MemoIO m a -> m a
getMemoIO (MemoIO ref) = liftIO (readIORef ref) >>= \case
  Left comp -> do
    res <- comp
    liftIO $ writeIORef ref $ Right res
    return res
  Right res -> return res


-- | Check if @LLVMPtr sym w@ points inside an allocation that is backed
--   by an SMT array store. If true, return a predicate that indicates
--   when the given array backs the given pointer, the SMT array,
--   and the size of the allocation.
--
--   NOTE: this operation is linear in the size of the list of previous
--   memory writes. This means that memory writes as well as memory reads
--   require a traversal of the list of previous writes. The performance
--   of this operation can be improved by using a map to index the writes
--   by allocation index.
asMemAllocationArrayStore ::
  forall sym w .
  (IsSymInterface sym, 1 <= w) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym w {- ^ Pointer -} ->
  Mem sym ->
  IO (Maybe (Pred sym, SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8), (SymBV sym w)))
asMemAllocationArrayStore sym w ptr mem
  | Just blk_no <- asNat (llvmPointerBlock ptr)
  , memMemberArrayBlock (llvmPointerBlock ptr) mem
  , [SomeAlloc _ _ (Just sz) _ _ _] <- List.nub (possibleAllocs blk_no mem)
  , Just Refl <- testEquality w (bvWidth sz) =
     do memo_nothing <- putMemoIO $ return Nothing
        --putStrLn $ "asMemAllocationArrayStore: base=" ++ show blk_no ++ " sz=" ++ show (printSymExpr sz)
        result <- findArrayStore sym w blk_no (BV.zero w) sz memo_nothing $
          memWritesAtConstant blk_no $ memWrites mem
        return $ case result of
          Just (ok, arr) -> Just (ok, arr, sz)
          Nothing -> Nothing

  | otherwise = return Nothing

asMemMatchingArrayStore ::
  (IsSymInterface sym, 1 <= w) =>
  sym ->
  NatRepr w ->
  LLVMPtr sym w ->
  SymBV sym w ->
  Mem sym ->
  IO (Maybe (Pred sym, SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8)))
asMemMatchingArrayStore sym w ptr sz mem
  | Just blk_no <- asNat (llvmPointerBlock ptr)
  , memMemberArrayBlock (llvmPointerBlock ptr) mem
  , Just off <- asBV (llvmPointerOffset ptr) = do
    --putStrLn $ "asMemMatchingArrayStore: ptr=" ++ show (blk_no, off) ++ " sz=" ++ show (printSymExpr sz)
    memo_nothing <- putMemoIO $ return Nothing
    findArrayStore sym w blk_no off sz memo_nothing $ memWritesAtConstant blk_no $ memWrites mem
  | otherwise = return Nothing

findArrayStore ::
  (IsSymInterface sym, 1 <= w) =>
  sym ->
  NatRepr w ->
  Natural ->
  BV w ->
  SymBV sym w ->
  MemoIO IO (Maybe (Pred sym, SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8))) ->
  [MemWrite sym] ->
  IO (Maybe (Pred sym, SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8)))
findArrayStore sym w blk_no off sz memo_cont = \case
  [] -> getMemoIO memo_cont
  head_mem_write : tail_mem_writes -> do
   --putStrLn $ "  findArrayStore: ptr=" ++ show (blk_no, off) ++ " sz=" ++ show (printSymExpr sz)
   --putStrLn $ "  findArrayStore: write=" ++ (case head_mem_write of MemWrite{} -> "write"; WriteMerge{} -> "merge")

   case head_mem_write of
    MemWrite write_ptr write_source
      | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
      , blk_no == write_blk_no
      , Just Refl <- testEquality w (ptrWidth write_ptr)
      , Just write_off <- asBV (llvmPointerOffset write_ptr)
      , off == write_off
      , MemArrayStore arr (Just arr_store_sz) <- write_source -> do
        ok <- bvEq sym sz arr_store_sz
        return (Just (ok, arr))

      | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
      , blk_no == write_blk_no
      , Just Refl <- testEquality w (ptrWidth write_ptr)
      , Just write_off <- asBV (llvmPointerOffset write_ptr)
      , Just sz_bv <- asBV sz
      , MemCopy src_ptr mem_copy_sz <- write_source
      , Just mem_copy_sz_bv <- asBV mem_copy_sz
      , BV.ule write_off off
      , BV.ule (BV.add w off sz_bv) (BV.add w write_off mem_copy_sz_bv)
      , Just src_blk_no <- asNat (llvmPointerBlock src_ptr)
      , Just src_off <- asBV (llvmPointerOffset src_ptr) ->
        findArrayStore sym w src_blk_no (BV.add w src_off $ BV.sub w off write_off) sz memo_cont tail_mem_writes

      | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
      , blk_no == write_blk_no
      , Just Refl <- testEquality w (ptrWidth write_ptr)
      , Just write_off <- asBV (llvmPointerOffset write_ptr)
      , Just sz_bv <- asBV sz
      , MemSet val mem_set_sz <- write_source
      , Just mem_set_sz_bv <- asBV mem_set_sz
      , BV.ule write_off off
      , BV.ule (BV.add w off sz_bv) (BV.add w write_off mem_set_sz_bv) -> do
        arr <- constantArray sym (Ctx.singleton $ BaseBVRepr w) val
        return $ Just (truePred sym, arr)

      | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
      , blk_no == write_blk_no
      , Just Refl <- testEquality w (ptrWidth write_ptr)
      , Just write_off <- asBV (llvmPointerOffset write_ptr) -> do
        maybe_write_sz <- runMaybeT $ writeSourceSize sym w write_source
        case maybe_write_sz of
          Just write_sz
            | Just sz_bv <- asBV sz
            , Just write_sz_bv <- asBV write_sz
            , end <- BV.add w off sz_bv
            , write_end <- BV.add w write_off write_sz_bv
            , BV.ule end write_off || BV.ule write_end off ->
              findArrayStore sym w blk_no off sz memo_cont tail_mem_writes
          _ -> return Nothing

      | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
      , blk_no /= write_blk_no ->
        findArrayStore sym w blk_no off sz memo_cont tail_mem_writes

      | otherwise -> return Nothing

    WriteMerge cond lhs_mem_writes rhs_mem_writes -> do
      -- Only traverse the tail if necessary, and be careful
      -- only to traverse it once
      memo_tail <- putMemoIO $ findArrayStore sym w blk_no off sz memo_cont tail_mem_writes

      lhs_result <- findArrayStore sym w blk_no off sz memo_tail (memWritesAtConstant blk_no lhs_mem_writes)
      rhs_result <- findArrayStore sym w blk_no off sz memo_tail (memWritesAtConstant blk_no rhs_mem_writes)

      case (lhs_result, rhs_result) of
        (Just (lhs_ok, lhs_arr), Just (rhs_ok, rhs_arr)) ->
           do ok <- itePred sym cond lhs_ok rhs_ok
              arr <- arrayIte sym cond lhs_arr rhs_arr
              pure (Just (ok,arr))

        (Just (lhs_ok, lhs_arr), Nothing) ->
           do ok <- andPred sym cond lhs_ok
              pure (Just (ok, lhs_arr))

        (Nothing, Just (rhs_ok, rhs_arr)) ->
           do cond' <- notPred sym cond
              ok <- andPred sym cond' rhs_ok
              pure (Just (ok, rhs_arr))

        (Nothing, Nothing) -> pure Nothing


{- Note [Memory Model Design]

At a high level, the memory model is represented as a list of memory writes
(with embedded muxes).  Reads from the memory model are accomplished by
1. Traversing backwards in the write log until the most recent write to each byte
   needed to satisfy the read has been covered by a write
2. Re-assembling the read value from fragments of those writes

This story is slightly complicated by optimizations and the fact that memory
regions can be represented in two different ways:
- "plain" allocations that are represented as symbolic bytes managed explicitly by the memory model, and
- Symbolic array storage backed by SMT arrays

The former allow for significant optimizations that lead to smaller formulas for
the underlying SMT solver.  The latter support symbolic reads efficiently.  The
former also supports symbolic reads, at the cost of extremely expensive and
large muxes.

* Memory Writes

The entry point for writing values to memory is 'writeMem' (which is just a
wrapper around 'writeMemWithAllocationCheck').  Writing a value to memory is
relatively simple, with only two major cases to consider.

The first case is an optimization over the SMT array backed memory model.  In
this case, the write can be statically determined to be contained entirely
within the bounds of an SMT array.  For efficiency, the memory model employs an
optimization that generates an updated SMT array (via applications of the SMT
`update` operator) and adds a special entry in the write log that shadows the
entire address range covered by that array in the write history (effectively
overwriting the entire backing array).  The goal of this optimization is to
reduce the number of muxes generated in subsequent reads.

In the general case, writing to the memory model adds a write record to the
write log.

* Memory Reads

The entry point for reading is the 'readMem' function.  Reading is more
complicated than writing, as reads can span multiple writes (and also multiple
different allocation types).

The memory reading code has an optimization to match the 'writeMem' case: if a
read is fully-covered by an SMT array, a fast path is taken that generates small
concrete array select terms.

In the fallback case, 'readMem' (via 'readMem'') traverses the write log to
assemble a Part(ial)LLVMVal from multiple writes.  The code is somewhat CPSed
via the 'readPrev' functions in that code.  If the traversal of the write log
finds a write that provides some, but not all, of the bytes covering a read, it
saves those bytes and invokes 'readPrev' to step back through the write log.
See Note [Value Reconstruction] for a description of how bytes from multiple
writes are re-assembled.  Note that the write log is a mix of 'MemWrite's and
'WriteMerge's; the explicit merge markers turn the log into a tree, where the
join points create muxes in the read value.

Note that the partiality in 'Part(ial)LLVMVal's does not refer to fragments of
values.  Instead, it refers to the fact that values may be only defined when
some predicate is true.

* Special Operations

The memory model has special support for memcpy and memset operations, which are
able to support symbolic lengths.  These operations are represented as
distinguished operations in the write log and are incorporated into the results
of reads as appropriate.

-}


{- Note [Value Reconstruction]

When a value is read, it may span multiple writes in memory (as C/C++/machine
code can do all manner of partial writes into the middle of objects).  The
various reading operations thus produce values of type 'ValueCtor' to represent
the reconstruction of values from fragments.  The 'ValueCtor' is essentially a
script in a restricted DSL that reconstructs values.  The "script" is
interpreted by 'genValueCtor'.

The reconstruction scripts are produced by the 'valueLoad', 'symbolicValueLoad',
and 'rangeLoad' functions.  Note that 'rangeLoad' is used for allocations backed
by SMT arrays, and thus always supports symbolic loads. These functions handle
the complexities of handling padding and data type interpretations.  The fast
paths in the read functions are able to call these directly (i.e., when offsets
and sizes are concrete).

-}
