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
  , MemAlloc(..)
  , memAllocs
  , memEndian
  , memAllocCount
  , memWriteCount
  , allocMem
  , allocAndWriteMem
  , readMem
  , isValidPointer
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

  , SomeAlloc(..)
  , possibleAllocs
  , ppSomeAlloc

    -- * Pretty printing
  , ppType
  , ppPtr
  , ppAlloc
  , ppAllocs
  , ppMem
  , ppTermExpr
  ) where

import           Prelude hiding (pred)

import           Control.Lens
import           Control.Monad
import           Control.Monad.State.Strict
import           Data.Coerce (coerce)
import           Data.IORef
import           Data.Maybe
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Monoid
import           Data.Text (Text)
import           GHC.Generics (Generic, Generic1)
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           Lang.Crucible.Panic (panic)

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
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.MemLog
import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.Value
import           Lang.Crucible.LLVM.MemModel.Partial (PartLLVMVal, HasLLVMAnn)
import qualified Lang.Crucible.LLVM.MemModel.Partial as Partial
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB


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

ppExprEnv :: IsExprBuilder sym => ExprEnv sym w -> Doc
ppExprEnv f = text "ExprEnv" <$$> (indent 4 $ vcat
     [text "loadOffset:"  <+> printSymExpr (loadOffset f)
     ,text "storeOffset:" <+> printSymExpr (storeOffset f)
     ,text "sizeData:"    <+> pretty (printSymExpr <$> sizeData f)])

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

genValueCtor :: forall sym w.
  (IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  EndianForm ->
  LLVMPtr sym w ->
  Mem sym ->
  ValueCtor (PartLLVMVal sym) ->
  IO (PartLLVMVal sym)
genValueCtor sym end ptr mem v =
  case v of
    ValueCtorVar x -> return x
    ConcatBV vcl vch ->
      do vl <- genValueCtor sym end ptr mem vcl
         vh <- genValueCtor sym end ptr mem vch
         case end of
           BigEndian    -> Partial.bvConcat sym ptr mem vh vl
           LittleEndian -> Partial.bvConcat sym ptr mem vl vh
    ConsArray vc1 vc2 ->
      do lv1 <- genValueCtor sym end ptr mem vc1
         lv2 <- genValueCtor sym end ptr mem vc2
         Partial.consArray sym ptr mem lv1 lv2
    AppendArray vc1 vc2 ->
      do lv1 <- genValueCtor sym end ptr mem vc1
         lv2 <- genValueCtor sym end ptr mem vc2
         Partial.appendArray sym ptr mem lv1 lv2
    MkArray tp vv ->
      Partial.mkArray sym tp =<<
        traverse (genValueCtor sym end ptr mem) vv
    MkStruct vv ->
      Partial.mkStruct sym =<<
        traverse (traverse (genValueCtor sym end ptr mem)) vv
    BVToFloat x ->
      Partial.bvToFloat sym ptr mem =<< genValueCtor sym end ptr mem x
    BVToDouble x ->
      Partial.bvToDouble sym ptr mem =<< genValueCtor sym end ptr mem x
    BVToX86_FP80 x ->
      Partial.bvToX86_FP80 sym ptr mem =<< genValueCtor sym end ptr mem x

-- | Compute the actual value of a value deconstructor expression.
applyView ::
  (IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  EndianForm ->
  LLVMPtr sym w ->
  Mem sym ->
  PartLLVMVal sym ->
  ValueView ->
  IO (PartLLVMVal sym)
applyView sym end ptr mem t val =
  case val of
    ValueViewVar _ ->
      return t
    SelectPrefixBV i j v ->
      do t' <- applyView sym end ptr mem t v
         case end of
           BigEndian    -> Partial.selectHighBv sym ptr mem j i t'
           LittleEndian -> Partial.selectLowBv sym ptr mem i j t'
    SelectSuffixBV i j v ->
      do t' <- applyView sym end ptr mem t v
         case end of
           BigEndian -> Partial.selectLowBv sym ptr mem j i t'
           LittleEndian -> Partial.selectHighBv sym ptr mem i j t'
    FloatToBV v ->
      Partial.floatToBV sym ptr mem =<< applyView sym end ptr mem t v
    DoubleToBV v ->
      Partial.doubleToBV sym ptr mem =<< applyView sym end ptr mem t v
    X86_FP80ToBV v ->
      Partial.fp80ToBV sym ptr mem =<< applyView sym end ptr mem t v
    ArrayElt sz tp idx v ->
      Partial.arrayElt sym ptr mem sz tp idx =<< applyView sym end ptr mem t v
    FieldVal flds idx v ->
      Partial.fieldVal sym ptr mem flds idx =<< applyView sym end ptr mem t v

evalMuxValueCtor ::
  forall u sym w .
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w {- ^ The pointer we are loading from -} ->
  Mem sym ->
  ExprEnv sym w {- ^ Evaluation function -} ->
  (u -> ReadMem sym (PartLLVMVal sym)) {- ^ Function for reading specific subranges -} ->
  Mux (ValueCtor u) ->
  ReadMem sym (PartLLVMVal sym)
evalMuxValueCtor sym _w end loadPtr mem _vf subFn (MuxVar v) =
  do v' <- traverse subFn v
     liftIO $ genValueCtor sym end loadPtr mem v'
evalMuxValueCtor sym w end loadPtr mem vf subFn (Mux c t1 t2) =
  do c' <- liftIO $ genCondVar sym w vf c
     case asConstantPred c' of
       Just True  -> evalMuxValueCtor sym w end loadPtr mem vf subFn t1
       Just False -> evalMuxValueCtor sym w end loadPtr mem vf subFn t2
       Nothing ->
        do t1' <- evalMuxValueCtor sym w end loadPtr mem vf subFn t1
           t2' <- evalMuxValueCtor sym w end loadPtr mem vf subFn t2
           liftIO $ Partial.muxLLVMVal sym c' t1' t2'

evalMuxValueCtor sym w end loadPtr mem vf subFn (MuxTable a b m t) =
  do m' <- traverse (evalMuxValueCtor sym w end loadPtr mem vf subFn) m
     t' <- evalMuxValueCtor sym w end loadPtr mem vf subFn t
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
  LLVMPtr sym w  {- ^ The loaded offset               -} ->
  Mem sym        {- ^ The original memory state       -} ->
  StorageType    {- ^ The type we are reading         -} ->
  SymBV sym w    {- ^ The destination of the memcopy  -} ->
  LLVMPtr sym w  {- ^ The source of the copied region -} ->
  SymBV sym w    {- ^ The length of the copied region -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
  ReadMem sym (PartLLVMVal sym)
readMemCopy sym w end loadPtr@(LLVMPointer blk off) origMem tp d src sz readPrev =
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
                liftIO . genValueCtor sym end loadPtr origMem =<< traverse subFn vcr
              _ ->
                evalMuxValueCtor sym w end loadPtr origMem varFn subFn $
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
            evalMuxValueCtor sym w end loadPtr origMem varFn subFn mux0

readMemSet ::
  forall sym w .
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w {- ^ The loaded offset             -} ->
  Mem sym       {- ^ The original memory state       -} ->
  StorageType   {- ^ The type we are reading       -} ->
  SymBV sym w   {- ^ The destination of the memset -} ->
  SymBV sym 8   {- ^ The fill byte that was set    -} ->
  SymBV sym w   {- ^ The length of the set region  -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
  ReadMem sym (PartLLVMVal sym)
readMemSet sym w end loadPtr@(LLVMPointer blk off) origMem tp d byte sz readPrev =
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
                  liftIO $ genValueCtor sym end loadPtr origMem (memsetValue b tp')
            case BV.asUnsigned <$> asBV sz of
              Just csz -> do
                let s = R (fromInteger so) (fromInteger (so + csz))
                let vcr = rangeLoad (fromInteger lo) tp s
                liftIO . genValueCtor sym end loadPtr origMem =<< traverse subFn vcr
              _ -> evalMuxValueCtor sym w end loadPtr origMem varFn subFn $
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
                     genValueCtor sym end loadPtr origMem (memsetValue b tp')
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- BV.asUnsigned <$> asBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end loadPtr origMem varFn subFn mux0

-- | Read from a memory with a store to the same block we are reading.
readMemStore ::
  forall sym w.
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w {- ^ The loaded address                 -} ->
  Mem sym       {- ^ The original memory state       -} ->
  StorageType   {- ^ The type we are reading            -} ->
  SymBV sym w   {- ^ The destination of the store       -} ->
  LLVMVal sym   {- ^ The value that was stored          -} ->
  StorageType   {- ^ The type of value that was written -} ->
  Alignment     {- ^ The alignment of the pointer we are reading from -} ->
  Alignment     {- ^ The alignment of the store from which we are reading -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym))
  {- ^ A callback function for when reading fails -} ->
  ReadMem sym (PartLLVMVal sym)
readMemStore sym w end loadPtr@(LLVMPointer blk off) origMem ltp d t stp loadAlign storeAlign readPrev =
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
                  applyView sym end loadPtr origMem (Partial.totalLLVMVal sym t) v
                subFn (InvalidMemory tp) = liftIO (Partial.partErr sym loadPtr origMem $ Partial.Invalid tp)
            let vcr = valueLoad (fromInteger lo) ltp (fromInteger so) (ValueViewVar stp)
            liftIO . genValueCtor sym end loadPtr origMem =<< traverse subFn vcr
       -- Symbolic offsets
       _ ->
         do let subFn :: ValueLoad OffsetExpr -> ReadMem sym (PartLLVMVal sym)
                subFn (OldMemory o tp')  = do
                  o' <- liftIO $ genOffsetExpr sym w varFn o
                  readPrev tp' (LLVMPointer blk o')
                subFn (LastStore v)      = liftIO $
                  applyView sym end loadPtr origMem (Partial.totalLLVMVal sym t) v
                subFn (InvalidMemory tp) = liftIO (Partial.partErr sym loadPtr origMem $ Partial.Invalid tp)
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
              else evalMuxValueCtor sym w end loadPtr origMem varFn subFn $
                symbolicValueLoad
                  pref
                  ltp
                  (signedBVBounds diff)
                  (ValueViewVar stp)
                  (LinearLoadStoreOffsetDiff stride delta)

-- | Read from a memory with an array store to the same block we are reading.
readMemArrayStore
  :: forall sym w
   . (1 <= w, IsSymInterface sym, HasLLVMAnn sym)
  => sym
  -> NatRepr w
  -> EndianForm
  -> LLVMPtr sym w {- ^ The loaded offset -}
  -> Mem sym       {- ^ The original memory state       -}
  -> StorageType {- ^ The type we are reading -}
  -> SymBV sym w {- ^ The destination of the mem array store -}
  -> SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) {- ^ The stored array -}
  -> Maybe (SymBV sym w) {- ^ The length of the stored array -}
  -> (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym))
  -> ReadMem sym (PartLLVMVal sym)
readMemArrayStore sym w end loadPtr@(LLVMPointer blk read_off) origMem tp write_off arr size read_prev = do
  let loadFn :: SymBV sym w -> StorageType -> ReadMem sym (PartLLVMVal sym)
      loadFn base tp' = liftIO $ do
        let loadArrayByteFn :: Offset -> IO (PartLLVMVal sym)
            loadArrayByteFn off = do
              blk0 <- natLit sym 0
              idx <- bvAdd sym base =<< bvLit sym w (bytesToBV w off)
              byte <- arrayLookup sym arr $ Ctx.singleton idx
              return $ Partial.totalLLVMVal sym $ LLVMValInt blk0 byte
        genValueCtor sym end loadPtr origMem =<< loadTypedValueFromBytes 0 tp' loadArrayByteFn
  let varFn = ExprEnv read_off write_off size
  case (BV.asUnsigned <$> asBV read_off, BV.asUnsigned <$> asBV write_off) of
    -- known read and write offsets
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
        Just concrete_size -> do
          let s = R (fromInteger so) (fromInteger (so + concrete_size))
          let vcr = rangeLoad (fromInteger lo) tp s
          liftIO . genValueCtor sym end loadPtr origMem =<< traverse subFn vcr
        _ -> evalMuxValueCtor sym w end loadPtr origMem varFn subFn $
          fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
    -- Symbolic offsets
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
      evalMuxValueCtor sym w end loadPtr origMem varFn subFn rngLd

readMemInvalidate ::
  forall sym w .
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym -> NatRepr w ->
  EndianForm ->
  LLVMPtr sym w {- ^ The loaded offset                   -} ->
  Mem sym       {- ^ The original memory state           -} ->
  StorageType   {- ^ The type we are reading             -} ->
  SymBV sym w   {- ^ The destination of the invalidation -} ->
  Text          {- ^ The error message                   -} ->
  SymBV sym w   {- ^ The length of the set region        -} ->
  (StorageType -> LLVMPtr sym w -> ReadMem sym (PartLLVMVal sym)) ->
  ReadMem sym (PartLLVMVal sym)
readMemInvalidate sym w end loadPtr@(LLVMPointer blk off) origMem tp d msg sz readPrev =
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
                subFn (InRange _o _tp') =
                  liftIO (Partial.partErr sym loadPtr origMem $ Partial.Invalidated msg)
--                  pure . Partial.partErr $ Partial.Invalidated msg
            case BV.asUnsigned <$> asBV sz of
              Just csz -> do
                let s = R (fromInteger so) (fromInteger (so + csz))
                let vcr = rangeLoad (fromInteger lo) tp s
                liftIO . genValueCtor sym end loadPtr origMem =<< traverse subFn vcr
              _ -> evalMuxValueCtor sym w end loadPtr origMem varFn subFn $
                     fixedOffsetRangeLoad (fromInteger lo) tp (fromInteger so)
       -- Symbolic offsets
       _ ->
         do let subFn :: RangeLoad OffsetExpr IntExpr -> ReadMem sym (PartLLVMVal sym)
                subFn (OutOfRange o tp') = do
                  o' <- liftIO $ genOffsetExpr sym w varFn o
                  readPrev tp' (LLVMPointer blk o')
                subFn (InRange _o _tp') =
                  liftIO (Partial.partErr sym loadPtr origMem $ Partial.Invalidated msg)
            let pref | Just{} <- dd = FixedStore
                     | Just{} <- ld = FixedLoad
                     | otherwise = NeitherFixed
            let mux0 | Just csz <- BV.asUnsigned <$> asBV sz =
                         fixedSizeRangeLoad pref tp (fromInteger csz)
                     | otherwise =
                         symbolicRangeLoad pref tp
            evalMuxValueCtor sym w end loadPtr origMem varFn subFn mux0

-- | Read a value from memory.
readMem :: forall sym w.
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) => sym ->
  NatRepr w ->
  LLVMPtr sym w ->
  StorageType ->
  Alignment ->
  Mem sym ->
  IO (PartLLVMVal sym)
readMem sym w l tp alignment m = do
  sz         <- bvLit sym w (bytesToBV w (typeEnd 0 tp))
  p1         <- isAllocated sym w alignment l (Just sz) m
  p2         <- isAligned sym w l alignment
  maybe_allocation_array <- asMemAllocationArrayStore sym w l m
  part_val <- case maybe_allocation_array of
    -- if this read is inside an allocation backed by a SMT array store,
    -- then decompose this read into reading the individual bytes and
    -- assembling them to obtain the value, without introducing any
    -- ite operations
    Just (arr, _arr_sz) -> do
      let loadArrayByteFn :: Offset -> IO (PartLLVMVal sym)
          loadArrayByteFn off = do
            blk0 <- natLit sym 0
            idx <- bvAdd sym (llvmPointerOffset l)
              =<< bvLit sym w (bytesToBV w off)
            byte <- arrayLookup sym arr $ Ctx.singleton idx
            return $ Partial.totalLLVMVal sym $ LLVMValInt blk0 byte
      genValueCtor sym (memEndianForm m) l m
        =<< loadTypedValueFromBytes 0 tp loadArrayByteFn
    Nothing -> readMem' sym w (memEndianForm m) l m tp alignment (memWrites m)

  Partial.attachSideCondition sym p1 (UB.ReadUnallocated  (UB.pointerView l)) =<<
    Partial.attachSideCondition sym p2 (UB.ReadBadAlignment (UB.pointerView l) alignment) part_val

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
readMem' ::
  forall w sym.
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) => sym ->
  NatRepr w ->
  EndianForm ->
  LLVMPtr sym w  {- ^ Address we are reading            -} ->
  Mem sym        {- ^ The original memory state         -} ->
  StorageType    {- ^ The type to read from memory      -} ->
  Alignment      {- ^ Alignment of pointer to read from -} ->
  MemWrites sym  {- ^ List of writes                    -} ->
  IO (PartLLVMVal sym)
readMem' sym w end l0 origMem tp0 alignment (MemWrites ws) =
  runReadMem initReadMemDebugState (go fallback0 l0 tp0 [] ws)
  where
    fallback0 ::
      StorageType ->
      LLVMPtr sym w ->
      ReadMem sym (PartLLVMVal sym)
    fallback0 _ l =
      do x <- get
         liftIO (Partial.partErr sym l origMem $ Partial.NoSatisfyingWrite (ppReadMemDebugState @sym x))
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
                            MemCopy src sz -> readMemCopy sym w end l origMem tp d src sz readPrev
                            MemSet v sz    -> readMemSet sym w end l origMem tp d v sz readPrev
                            MemStore v stp storeAlign -> readMemStore sym w end l origMem tp d v stp alignment storeAlign readPrev
                            MemArrayStore arr sz -> readMemArrayStore sym w end l origMem tp d arr sz readPrev
                            MemInvalidate msg sz -> readMemInvalidate sym w end l origMem tp d msg sz readPrev
                    sameBlock <- liftIO $ natEq sym blk1 blk2
                    case asConstantPred sameBlock of
                      Just True  -> do
                        result <- readCurrent
                        addMatchingWrite h result
                        pure result
                      Just False -> readPrev tp l
                      Nothing ->
                        do x <- readCurrent
                           y <- readPrev tp l
                           liftIO $ Partial.muxLLVMVal sym sameBlock x y

--------------------------------------------------------------------------------

-- | Our algorithm for reading memory has a lot of backtracking, making it
-- difficult to determine what went wrong if the read fails. This datatype keeps
-- some state so that we can provide better error messages.
--
-- In particular, every time we attempt a read from a write with a matching
-- allocation index, it keeps track of the write and the result we got.
newtype ReadMemDebugState sym =
  ReadMemDebugState [(MemWrite sym, PartLLVMVal sym)]
  deriving (Generic)

initReadMemDebugState :: ReadMemDebugState sym
initReadMemDebugState = ReadMemDebugState []

ppReadMemDebugState :: (IsExprBuilder sym, IsSymInterface sym)
                    => ReadMemDebugState sym -> [Doc]
ppReadMemDebugState (ReadMemDebugState st) =
  case st of
    [] -> []
    _  ->
      [ text "Matching writes:"
      , vcat $ flip map st $ \(w, v) ->
          text "* Write: " <> ppWrite w
          <$$> indent 2 (text "Failed assertion: " <$$>
                         indent 2 (Partial.ppAssertion v))
      ]

newtype ReadMem sym a =
  ReadMem { getReadMem :: StateT (ReadMemDebugState sym) IO a }
  deriving (Applicative, Functor, Generic, Generic1, Monad, MonadIO)

deriving instance MonadState (ReadMemDebugState sym) (ReadMem sym)

instance Wrapped (ReadMem sym a) where

runReadMem :: ReadMemDebugState sym -> ReadMem sym a -> IO a
runReadMem st (ReadMem c) = evalStateT c st

addMatchingWrite :: MemWrite sym -> PartLLVMVal sym -> ReadMem sym ()
addMatchingWrite w v = ReadMem (modify (coerce ((w,v):)))

--------------------------------------------------------------------------------

memWritesSingleton ::
  IsExprBuilder sym =>
  LLVMPtr sym w ->
  WriteSource sym w ->
  MemWrites sym
memWritesSingleton ptr src
  | Just blk <- asNat (llvmPointerBlock ptr)
  , isIndexableSource src =
    MemWrites
      [ MemWritesChunkIndexed $
          IntMap.singleton (fromIntegral blk) [MemWrite ptr src]
      ]
  | otherwise = MemWrites [MemWritesChunkFlat [MemWrite ptr src]]
  where
    isIndexableSource ::  WriteSource sym w -> Bool
    isIndexableSource = \case
      MemStore{} -> True
      MemArrayStore{} -> True
      MemSet{} -> True
      MemInvalidate{} -> True
      MemCopy{} -> False

memWritesSize :: MemWrites sym -> Int
memWritesSize (MemWrites writes) = getSum $ foldMap
  (\case
    MemWritesChunkIndexed indexed_writes ->
      foldMap (Sum . length) indexed_writes
    MemWritesChunkFlat flat_writes -> Sum $ length flat_writes)
  writes

muxChanges :: Pred sym -> MemChanges sym -> MemChanges sym -> MemChanges sym
muxChanges c (left_allocs, lhs_writes) (rhs_allocs, rhs_writes) =
  ( [AllocMerge c left_allocs rhs_allocs]
  , muxWrites c lhs_writes rhs_writes
  )

muxWrites :: Pred sym -> MemWrites sym -> MemWrites sym -> MemWrites sym
muxWrites _ (MemWrites []) (MemWrites []) = MemWrites []
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
        go (StackFrame _ _ l s)  = f l <> go s
        go (BranchFrame _ _ l s) = f l <> go s

memAllocs :: Mem sym -> [MemAlloc sym]
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
  StackFrame ac _ _ _ -> ac
  BranchFrame ac _ _ _ -> ac

memStateWriteCount :: MemState sym -> Int
memStateWriteCount s = case s of
  EmptyMem _ wc _ -> wc
  StackFrame _ wc _ _ -> wc
  BranchFrame _ wc _ _ -> wc

memAllocCount :: Mem sym -> Int
memAllocCount m = memStateAllocCount (m ^. memState)

memWriteCount :: Mem sym -> Int
memWriteCount m = memStateWriteCount (m ^. memState)

memAddAlloc :: MemAlloc sym -> Mem sym -> Mem sym
memAddAlloc x = memState %~ \case
  EmptyMem ac wc (a, w) -> EmptyMem (ac+1) wc (x:a, w)
  StackFrame ac wc (a, w) s -> StackFrame (ac+1) wc (x:a, w) s
  BranchFrame ac wc (a, w) s -> BranchFrame (ac+1) wc (x:a, w) s

memAddWrite ::
  IsExprBuilder sym =>
  LLVMPtr sym w ->
  WriteSource sym w ->
  Mem sym ->
  Mem sym
memAddWrite ptr src = do
  let single_write = memWritesSingleton ptr src
  memState %~ \case
    EmptyMem ac wc (a, w) ->
      EmptyMem ac (wc+1) (a, single_write <> w)
    StackFrame ac wc (a, w) s ->
      StackFrame ac (wc+1) (a, single_write <> w) s
    BranchFrame ac wc (a, w) s ->
      BranchFrame ac (wc+1) (a, single_write <> w) s

memStateAddChanges :: MemChanges sym -> MemState sym -> MemState sym
memStateAddChanges (a, w) = \case
  EmptyMem ac wc (a0, w0) ->
    EmptyMem (length a + ac) (memWritesSize w + wc) (a ++ a0, w <> w0)
  StackFrame ac wc (a0, w0) s ->
    StackFrame (length a + ac) (memWritesSize w + wc) (a ++ a0, w <> w0) s
  BranchFrame ac wc (a0, w0) s ->
    BranchFrame (length a + ac) (memWritesSize w + wc) (a ++ a0, w <> w0) s


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
  go (pure (falsePred sym)) (memAllocs m)
  where
    -- @inThisAllocation a allocatedSz@ produces the predicate that
    -- records whether the pointer @ptr@ of size @sz@ falls within the
    -- allocation of block @a@ of size @allocatedSz@.
    inThisAllocation :: forall w'. Maybe (SymBV sym w') -> IO (Pred sym)
    inThisAllocation Nothing =
      case sz of
        Nothing ->
          -- Unbounded access of an unbounded allocation must start at offset 0.
          bvEq sym off =<< bvLit sym w (BV.zero w)
        Just currSize ->
          -- Bounded access of an unbounded allocation requires that
          -- @offset + size <= 2^w@, or equivalently @offset <= 2^w -
          -- size@. Note that @bvNeg sym size@ computes @2^w - size@
          -- for any nonzero @size@.
          do zeroSize <- bvEq sym currSize =<< bvLit sym w (BV.zero w)
             noWrap <- bvUle sym off =<< bvNeg sym currSize
             orPred sym zeroSize noWrap

    inThisAllocation (Just allocSize)
      -- If the allocation is done at pointer width is equal to @w@, check
      -- if this allocation covers the required range
      | Just Refl <- testEquality w (bvWidth allocSize)
      , Just currSize <- sz =
        do smallSize <- bvUle sym currSize allocSize    -- currSize <= allocSize
           maxOffset <- bvSub sym allocSize currSize    -- maxOffset = allocSize - currSize
           inRange   <- bvUle sym off maxOffset         -- offset(ptr) <= maxOffset
           andPred sym smallSize inRange

    inThisAllocation (Just _allocSize)
      -- If the allocation is done at pointer width not equal to @w@,
      -- then this is not the allocation we're looking for. Similarly,
      -- if @sz@ is @Nothing@ (indicating we are accessing the entire
      -- address space) then any bounded allocation is too small.
      | otherwise = return $ falsePred sym

    go :: IO (Pred sym) -> [MemAlloc sym] -> IO (Pred sym)
    go fallback [] = fallback
    go fallback (Alloc _ a asz mut alignment _ : r)
      | mutOk mut && alignment >= minAlign =
        -- If the block ID matches, then call 'inThisAllocation',
        -- otherwise search the remainder of the allocation history.
        do sameBlock <- natEq sym blk =<< natLit sym a
           itePredM sym sameBlock (inThisAllocation asz) (go fallback r)
      | otherwise = go fallback r
    go fallback (MemFree a : r) =
      do notSameBlock <- notPred sym =<< natEq sym blk a
         andPred sym notSameBlock =<< go fallback r
    go fallback (AllocMerge _ [] [] : r) = go fallback r
    go fallback (AllocMerge c xr yr : r) =
      do p <- go fallback r -- TODO: wrap this in a delay
         px <- go (return p) xr
         py <- go (return p) yr
         itePred sym c px py

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
       bvEq sym lowbits =<< bvLit sym bits (BV.zero bits)
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
writeMem :: (1 <= w, IsSymInterface sym, HasLLVMAnn sym)
         => sym -> NatRepr w
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
  (1 <= w, IsSymInterface sym, HasLLVMAnn sym) =>
  sym           ->
  NatRepr w     ->
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
  (IsSymInterface sym, HasLLVMAnn sym, 1 <= w) =>
  (sym -> NatRepr w -> Alignment -> LLVMPtr sym w -> Maybe (SymBV sym w) -> Mem sym -> IO (Pred sym)) ->
  sym ->
  NatRepr w ->
  LLVMPtr sym w ->
  StorageType ->
  Alignment ->
  LLVMVal sym ->
  Mem sym ->
  IO (Mem sym, Pred sym, Pred sym)
writeMemWithAllocationCheck is_allocated sym w ptr tp alignment val mem = do
  let sz = typeEnd 0 tp
  sz_bv <- constOffset sym w sz
  p1 <- is_allocated sym w alignment ptr (Just sz_bv) mem
  p2 <- isAligned sym w ptr alignment
  maybe_allocation_array <- asMemAllocationArrayStore sym w ptr mem
  mem' <- case maybe_allocation_array of
    -- if this write is inside an allocation backed by a SMT array store,
    -- then decompose this write into disassembling the value to individual
    -- bytes, writing them in the SMT array, and writing the updated SMT array
    -- in the memory
    Just (arr, arr_sz) -> do
      let subFn :: ValueLoad Addr -> IO (PartLLVMVal sym)
          subFn = \case
            LastStore val_view -> applyView
              sym
              (memEndianForm mem)
              ptr
              mem
              (Partial.totalLLVMVal sym val)
              val_view
            InvalidMemory tp'-> Partial.partErr sym ptr mem $ Partial.Invalid tp'
            OldMemory off _ -> panic "Generic.writeMemWithAllocationCheck"
              [ "Unexpected offset in storage type"
              , "*** Offset:  " ++ show off
              , "*** StorageType:  " ++ show tp
              ]
          storeArrayByteFn ::
            SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8) ->
            Offset ->
            IO (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8))
          storeArrayByteFn acc_arr off = do
            partial_byte <- genValueCtor sym (memEndianForm mem) ptr mem
              =<< traverse subFn (loadBitvector off 1 0 (ValueViewVar tp))

            -- TODO! we're abusing assertSafe here a little
            v <- Partial.assertSafe sym ptr (bitvectorType (toBytes (1::Integer))) partial_byte
            case v of
              LLVMValInt _ byte
                | Just Refl <- testEquality (knownNat @8) (bvWidth byte) -> do
                  idx <- bvAdd sym (llvmPointerOffset ptr)
                    =<< bvLit sym w (bytesToBV w off)
                  arrayUpdate sym acc_arr (Ctx.singleton idx) byte
              _ -> return acc_arr
      res_arr <- foldM storeArrayByteFn arr [0 .. (sz - 1)]
      return $ memAddWrite ptr (MemArrayStore res_arr (Just arr_sz)) mem
    Nothing -> return $ memAddWrite ptr (MemStore val tp alignment) mem
  return (mem', p1, p2)

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
     return (memAddWrite dst (MemCopy src sz) m, p1, p2)

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
     return (memAddWrite ptr (MemSet val sz) m, p)

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
writeArrayMem sym w ptr alignment arr sz m =
  do p1 <- isAllocatedMutable sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     return (memAddWrite ptr (MemArrayStore arr sz) m, p1, p2)

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
writeArrayConstMem sym w ptr alignment arr sz m =
  do p1 <- isAllocated sym w alignment ptr sz m
     p2 <- isAligned sym w ptr alignment
     return (memAddWrite ptr (MemArrayStore arr sz) m, p1, p2)

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
allocMem :: AllocType -- ^ Type of allocation
         -> Natural -- ^ Block id for allocation
         -> Maybe (SymBV sym w) -- ^ Size
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
  do sz <- bvLit sym w (bytesToBV w (typeEnd 0 tp))
     base <- natLit sym b
     off <- bvLit sym w (BV.zero w)
     let p = LLVMPointer base off
     return (m & memAddAlloc (Alloc a b (Just sz) mut alignment loc)
               & memAddWrite p (MemStore v tp alignment))

pushStackFrameMem :: Mem sym -> Mem sym
pushStackFrameMem = memState %~ \s ->
  StackFrame (memStateAllocCount s) (memStateWriteCount s) emptyChanges s

popStackFrameMem :: Mem sym -> Mem sym
popStackFrameMem m = m & memState %~ popf
  where popf (StackFrame _ _ (a,w) s) =
          s & memStateAddChanges c
          where c = (mapMaybe pa a, w)

        -- WARNING: The following code executes a stack pop underneath a branch
        -- frame.  This is necessary to get merges to work correctly
        -- when they propagate all the way to function returns.
        -- However, it is not clear that the following code is
        -- precisely correct because it may leave in place writes to
        -- memory locations that have just been popped off the stack.
        -- This does not appear to be causing problems for our
        -- examples, but may be a source of subtle errors.
        popf (BranchFrame _ wc (a,w) s) =
          BranchFrame (length (fst c)) wc c $ popf s
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
  do p1 <- bvEq sym off =<< bvLit sym w (BV.zero w)
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
        Alloc{} ->
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
branchMem = memState %~ \s ->
  BranchFrame (memStateAllocCount s) (memStateWriteCount s) emptyChanges s

branchAbortMem :: Mem sym -> Mem sym
branchAbortMem = memState %~ popf
  where popf (BranchFrame _ _ c s) = s & memStateAddChanges c
        popf _ = error "branchAbortMem given unexpected memory"

mergeMem :: Pred sym -> Mem sym -> Mem sym -> Mem sym
mergeMem c x y =
  case (x^.memState, y^.memState) of
    (BranchFrame _ _ a s, BranchFrame _ _ b _) ->
      let s' = s & memStateAddChanges (muxChanges c a b)
      in x & memState .~ s'
    _ -> error "mergeMem given unexpected memories"

--------------------------------------------------------------------------------
-- Finding allocations

-- When we have a concrete allocation number, we can ask more specific questions
-- to the solver and get (overapproximate) concrete answers.

data SomeAlloc sym =
  forall w. SomeAlloc AllocType Natural (Maybe (SymBV sym w)) Mutability Alignment String

instance IsSymInterface sym => Eq (SomeAlloc sym) where
  SomeAlloc x_atp x_base x_sz x_mut x_alignment x_loc == SomeAlloc y_atp y_base y_sz y_mut y_alignment y_loc = do
    let sz_eq = case (x_sz, y_sz) of
          (Just x_bv, Just y_bv) -> isJust $ testEquality x_bv y_bv
          (Nothing, Nothing) -> True
          _ -> False
    x_atp == y_atp && x_base == y_base && sz_eq && x_mut == y_mut && x_alignment == y_alignment && x_loc == y_loc

ppSomeAlloc :: forall sym. IsExprBuilder sym => SomeAlloc sym -> Doc
ppSomeAlloc (SomeAlloc atp base sz mut alignment loc) =
  ppAlloc (Alloc atp base sz mut alignment loc :: MemAlloc sym)

-- | Find an overapproximation of the set of allocations with this number.
--
--   Ultimately, only one of these could have happened.
--
--   It may be possible to be more precise than this function currently is.
--   In particular, if we find an 'Alloc' with a matching block number before a
--   'AllocMerge', then we can (maybe?) just return that 'Alloc'. And if one
--   call of @helper@ on a 'MemAlloc' returns anything nonempty, that can just
--   be returned (?).
possibleAllocs ::
  forall sym .
  (IsSymInterface sym) =>
  Natural              ->
  Mem sym              ->
  [SomeAlloc sym]
possibleAllocs n = helper . memAllocs
  where helper =
          foldMap $
            \case
              MemFree _ -> []
              Alloc atp base sz mut alignment loc ->
                if base == n
                then [SomeAlloc atp base sz mut alignment loc]
                else []
              AllocMerge (asConstantPred -> Just True) as1 _as2 -> helper as1
              AllocMerge (asConstantPred -> Just False) _as1 as2 -> helper as2
              AllocMerge _ as1 as2 -> helper as1 ++ helper as2

-- | Check if @LLVMPtr sym w@ points inside an allocation that is backed
--   by an SMT array store. If true, return the SMT array and the size of
--   the allocation.
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
  IO (Maybe (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8), (SymBV sym w)))
asMemAllocationArrayStore sym w ptr mem
  | Just blk_no <- asNat (llvmPointerBlock ptr)
  , [SomeAlloc _ _ (Just sz) _ _ _] <- List.nub (possibleAllocs blk_no mem)
  , Just Refl <- testEquality w (bvWidth sz) = do
    let findArrayStore ::
          [MemWrite sym] ->
          IO (Maybe (SymArray sym (SingleCtx (BaseBVType w)) (BaseBVType 8)))
        findArrayStore = \case
          head_mem_write : tail_mem_writes -> case head_mem_write of
            MemWrite write_ptr write_source
              | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
              , blk_no == write_blk_no
              , MemArrayStore arr (Just arr_store_sz) <- write_source
              , Just Refl <- testEquality w (ptrWidth write_ptr) -> do
                sz_eq <- bvEq sym sz arr_store_sz
                case asConstantPred sz_eq of
                  Just True -> return $ Just arr
                  _ -> return Nothing
              | Just write_blk_no <- asNat (llvmPointerBlock write_ptr)
              , blk_no /= write_blk_no ->
                findArrayStore tail_mem_writes
              | otherwise -> return Nothing
            WriteMerge cond lhs_mem_writes rhs_mem_writes -> do
              lhs_result <- findArrayStore $
                (memWritesAtConstant blk_no lhs_mem_writes) ++ tail_mem_writes
              rhs_result <- findArrayStore $
                (memWritesAtConstant blk_no rhs_mem_writes) ++ tail_mem_writes
              case (lhs_result, rhs_result) of
                (Just lhs_arr, Just rhs_arr) ->
                  Just <$> arrayIte sym cond lhs_arr rhs_arr
                _ -> return Nothing
          [] -> return Nothing
    result <- findArrayStore $ memWritesAtConstant blk_no $ memWrites mem
    return $ case result of
      Just arr -> Just (arr, sz)
      Nothing -> Nothing
  | otherwise = return Nothing

