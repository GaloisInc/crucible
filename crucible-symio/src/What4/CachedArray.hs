-----------------------------------------------------------------------
-- |
-- Module           : What4.CachedArray
-- Description      : What4 array storage with a concrete backing supporting symbolic indexes
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Daniel Matichuk <dmatichuk@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module What4.CachedArray
  (
    CachedArray
  , writeArray
  , readArray
  , muxArrays
  , initArrayConcrete
  , initArray
  ) where

import           GHC.Natural

import           Control.Monad ( foldM )
import           Data.Functor.Const
import           Data.Maybe ( catMaybes )
import           Data.Map ( Map )
import qualified Data.Map as Map

import           Data.IntervalMap.Generic.Strict ( IntervalMap )
import qualified Data.IntervalMap.Generic.Strict as IM
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr ( type (<=) )
import qualified Data.BitVector.Sized as BV


import qualified What4.Interface as W4
import qualified What4.Concrete as W4
import qualified What4.Utils.AbstractDomains as W4
import qualified What4.Utils.BVDomain as BVD

------------------------------------------------
-- Interface

-- TODO: add coalescing function for merging adjacent entries
-- into symbolic arrays

writeArray ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  W4.SymExpr sym tp ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
writeArray sym symIdxExpr val arr = arrConstraints arr $ do  
  arr' <- invalidateEntries sym symIdx arr
  let entry = ArrayEntryVal symIdx (W4.truePred sym) val
  arr'' <- insertWithM k entry (\_ old_v -> addNewEntry sym symIdx val old_v) (arrMap arr')
  return $ arr { arrMap = arr'' }
  where
    k = symIdxToAbs @sym symIdx
    symIdx = SymIndex symIdxExpr

readArray ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) idx ->
  CachedArray sym idx tp ->
  IO (W4.SymExpr sym tp)
readArray sym symIdxExpr arr = case FC.allFC W4.baseIsConcrete symIdxExpr of
  True | Just e@(ArrayEntryVal _ _ v) <- IM.lookup k (arrMap arr) -> do
    constEntryCond sym e symIdx >>= \case
      Just True -> return v
      _ -> symbolic
  _ -> symbolic      
  where
    k = symIdxToAbs @sym symIdx
    symIdx = SymIndex symIdxExpr
    
    symbolic :: IO (W4.SymExpr sym tp)
    symbolic = do
      let intersecting = IM.toAscList $ IM.intersecting (arrMap arr) k
      arrConstraints arr $ 
        mapM (\(_, entry) -> readEntry sym symIdx entry) intersecting >>= \case  
          [] -> fail "readArray: unexpected empty result"
          ((r, _) : rest) -> foldM (\else_ (result, p) -> W4.baseTypeIte sym p result else_) r rest

-- TODO: use nonces to determine when this is unecessary
muxArrays ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  CachedArray sym idx tp ->
  CachedArray sym idx tp ->
  IO (CachedArray sym idx tp)
muxArrays sym p arr1 arr2 = arrConstraints arr1 $ do
  arr' <- mapMIntersection (\_ eT eF -> muxEntries sym p eT eF) (arrMap arr1) (arrMap arr2)
  return $ arr1 { arrMap = arr' }

-- | Initialize an array with symbolic contents at concrete locations
initArrayConcrete ::
  forall sym idx tp idx' tp'.
  W4.IsSymExprBuilder sym =>
  idx ~ (idx' Ctx.::> tp') =>
  sym ->
  Map (Ctx.Assignment W4.ConcreteVal idx) (W4.SymExpr sym tp) ->
  IO (CachedArray sym idx tp)
initArrayConcrete sym m = do
  im <- IM.fromList <$> mapM go (Map.assocs m)
  return $ CachedArray im id
  where
    go ::
      (Ctx.Assignment W4.ConcreteVal idx, W4.SymExpr sym tp) ->
      IO (AbsIndex idx, ArrayEntry sym idx tp)
    go (cidx, v) = do
      sidx <- concreteIdxToSym sym cidx
      let
        aidx = symIdxToAbs @sym sidx
        entry = ArrayEntryVal sidx (W4.truePred sym) v
      return $ (aidx, entry)

-- | Initialize an array with symbolic contents at symbolic locations
initArray ::
  forall sym idx tp idx' tp'.
  W4.IsSymExprBuilder sym =>
  idx ~ (idx' Ctx.::> tp') =>
  sym ->
  Map (Ctx.Assignment (W4.SymExpr sym) idx) (W4.SymExpr sym tp) ->
  IO (CachedArray sym idx tp)
initArray sym m = do
  im <- IM.fromList <$> mapM go (Map.assocs m)
  return $ CachedArray im id
  where
    go ::
      (Ctx.Assignment (W4.SymExpr sym) idx, W4.SymExpr sym tp) ->
      IO (AbsIndex idx, ArrayEntry sym idx tp)
    go (symIdxExpr, v) = do
      let
        symIdx = SymIndex symIdxExpr
        aidx = symIdxToAbs @sym symIdx
        entry = ArrayEntryVal symIdx (W4.truePred sym) v
      return $ (aidx, entry)

---------------------------------------------------
-- Implementation


data CachedArray sym (idx :: Ctx.Ctx W4.BaseType) (tp :: W4.BaseType) where
  CachedArray ::
    {
      arrMap :: IntervalMap (AbsIndex ctx) (ArrayEntry sym ctx tp)
    , arrConstraints :: forall a. (NonEmptyCtx ctx => a) -> a
    } -> CachedArray sym ctx tp


-- | An array entry defines a set of possible values for a given
-- abstract domain. Entries may overlap, therefore each is paired
-- with a validity predicate that defines precisely which (symbolic)
-- indexes the entry is valid on.
data ArrayEntry sym ctx tp where
  ArrayEntryArr ::
    (SymIndex sym ctx -> IO (W4.Pred sym)) ->
    -- ^ indexes that this array is valid on
    W4.SymArray sym ctx tp ->
    ArrayEntry sym ctx tp
  -- ^ a symbolic array entry defines a collection of values which
  -- are valid on the abstract domain of the entry, given that the
  -- validity predicate holds. It represents multiple array writes coalesced
  -- into a single term.
  ArrayEntryVal ::
    SymIndex sym ctx ->
    -- ^ exact (symbolic) index that for this entry
    W4.Pred sym ->
    -- ^ predicate which is true when this value is live
    W4.SymExpr sym tp ->
    ArrayEntry sym ctx tp
  -- ^ a symbolic value entry represents a single write to an abstract
  -- index.

-- | A symbolic index into the array. It represents the index for a single array element,
-- although its value may be symbolic
newtype SymIndex sym ctx = SymIndex (Ctx.Assignment (W4.SymExpr sym) ctx)

data NonEmptyCtxRepr ctx where
  NonEmptyCtxRepr :: NonEmptyCtxRepr (ctx Ctx.::> x)

class NonEmptyCtx ctx where
  nonEmptyCtxRepr :: NonEmptyCtxRepr ctx

instance NonEmptyCtx (ctx Ctx.::> tp) where
  nonEmptyCtxRepr = NonEmptyCtxRepr

entryCond ::
  W4.IsSymExprBuilder sym =>
  sym -> 
  ArrayEntry sym ctx tp ->
  SymIndex sym ctx ->
  IO (W4.Pred sym)
entryCond _sym (ArrayEntryArr condF _) idx = condF idx
entryCond sym (ArrayEntryVal idx' p _) idx = do
  p' <- isEqIndex sym idx idx'
  W4.andPred sym p p'

constEntryCond ::
  W4.IsSymExprBuilder sym =>
  sym -> 
  ArrayEntry sym ctx tp ->
  SymIndex sym ctx ->
  IO (Maybe Bool)
constEntryCond sym entry idx = W4.asConstantPred <$> entryCond sym entry idx

data AbsInterval tp where
  AbsIntervalNat :: W4.NatValueRange -> AbsInterval W4.BaseNatType
  AbsIntervalBV :: (1 <= w) => W4.NatRepr w -> W4.ValueRange Integer -> AbsInterval (W4.BaseBVType w)

data AbsIntervalEnd tp where
  AbsIntervalEndNat :: W4.ValueBound Natural -> AbsIntervalEnd W4.BaseNatType
  AbsIntervalEndBV :: (1 <= w) => W4.NatRepr w -> W4.ValueBound Integer -> AbsIntervalEnd (W4.BaseBVType w)
  
 
instance TestEquality AbsInterval where
  testEquality a1 a2 = case compareF a1 a2 of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF AbsInterval where
  compareF a1 a2 = case (a1, a2) of
    (AbsIntervalNat (W4.NatSingleRange n1), AbsIntervalNat (W4.NatSingleRange n2)) ->
      fromOrdering $ compare n1 n2
    (AbsIntervalNat n1, AbsIntervalNat n2) ->
      fromOrdering $ 
      compare (W4.natRangeLow n1) (W4.natRangeLow n2)
      <> compare (W4.natRangeHigh n1) (W4.natRangeHigh n2)
    (AbsIntervalBV w1 (W4.SingleRange i1), AbsIntervalBV w2 (W4.SingleRange i2)) ->
      lexCompareF w1 w2 $ fromOrdering $ compare i1 i2
    (AbsIntervalBV w1 i1, AbsIntervalBV w2 i2) ->
      lexCompareF w1 w2 $ fromOrdering $
        compare (W4.rangeLowBound i1) (W4.rangeLowBound i2)
        <> compare (W4.rangeHiBound i1) (W4.rangeHiBound i2)
    (AbsIntervalNat{}, AbsIntervalBV{}) -> LTF
    (AbsIntervalBV{}, AbsIntervalNat{}) -> GTF

instance Eq (AbsInterval tp) where
  a1 == a2 = (compare a1 a2) == EQ

instance Ord (AbsInterval tp) where
  compare a1 a2 = toOrdering $ compareF a1 a2

instance Ord (AbsIntervalEnd tp) where
  compare a1 a2 = toOrdering $ compareF a1 a2

instance Eq (AbsIntervalEnd tp) where
  a1 == a2 = (compare a1 a2) == EQ

instance TestEquality AbsIntervalEnd where
  testEquality a1 a2 = case compareF a1 a2 of
    EQF -> Just Refl
    _ -> Nothing  

instance OrdF AbsIntervalEnd where
  compareF a1 a2 = case (a1, a2) of
    (AbsIntervalEndNat n1, AbsIntervalEndNat n2) -> fromOrdering $ compare n1 n2
    (AbsIntervalEndBV w1 i1, AbsIntervalEndBV w2 i2) ->
      lexCompareF w1 w2 $ fromOrdering $ compare i1 i2
    (AbsIntervalEndNat{}, AbsIntervalEndBV{}) -> LTF
    (AbsIntervalEndBV{}, AbsIntervalEndNat{}) -> GTF

instance IM.Interval (AbsInterval tp) (AbsIntervalEnd tp) where
  lowerBound ai = case ai of
    AbsIntervalNat v -> AbsIntervalEndNat $ W4.Inclusive $ W4.natRangeLow v
    AbsIntervalBV w v -> AbsIntervalEndBV w $ W4.rangeLowBound v
  upperBound ai = case ai of
    AbsIntervalNat v -> AbsIntervalEndNat $ W4.natRangeHigh v
    AbsIntervalBV w v -> AbsIntervalEndBV w $ W4.rangeHiBound v

newtype AbsIndex (idx :: Ctx.Ctx W4.BaseType) =
  AbsIndex (Ctx.Assignment AbsInterval idx)
  deriving (Eq, Ord)

instance IM.Interval (AbsIndex tp) (AbsIndexEnd tp) where
  lowerBound (AbsIndex idx) = AbsIndexEnd $ FC.fmapFC IM.lowerBound idx
  upperBound (AbsIndex idx) = AbsIndexEnd $ FC.fmapFC IM.upperBound idx

newtype AbsIndexEnd (idx :: Ctx.Ctx W4.BaseType) =
  AbsIndexEnd (Ctx.Assignment AbsIntervalEnd idx)
  deriving (Eq, Ord)



bvDomainRange ::
  1 <= w =>
  W4.NatRepr w ->
  BVD.BVDomain w ->
  AbsInterval (W4.BaseBVType w)
bvDomainRange w d = case BVD.ubounds d of
  (i1, i2) | i1 == i2 -> AbsIntervalBV w (W4.singleRange i1)
  (i1, i2) -> AbsIntervalBV w (W4.valueRange (W4.Inclusive i1) (W4.Inclusive i2))

exprToAbsInterval ::
  forall sym tp. 
  W4.IsSymExprBuilder sym =>
  W4.SymExpr sym tp ->
  AbsInterval tp
exprToAbsInterval e = absToInterval (W4.exprType e) (W4.getAbsValue e)
  
absToInterval ::
  W4.BaseTypeRepr tp ->
  W4.AbstractValue tp ->
  AbsInterval tp  
absToInterval repr v = case repr of
  W4.BaseNatRepr -> AbsIntervalNat v
  W4.BaseBVRepr w -> bvDomainRange w v
  _ -> error "Unsupported type"
    

readEntry ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  SymIndex sym ctx ->
  ArrayEntry sym ctx tp ->
  IO (W4.SymExpr sym tp, W4.Pred sym)
readEntry sym symIdx@(SymIndex symIdxExpr) entry = do
  cond <- entryCond sym entry symIdx
  case entry of
    ArrayEntryArr _ arr -> do
      NonEmptyCtxRepr <- return $ nonEmptyCtxRepr @ctx
      v <- W4.arrayLookup sym arr symIdxExpr 
      return (v, cond)
    ArrayEntryVal _ _ v -> do
      return (v, cond)

_isWithinInterval ::
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) idx ->
  AbsIndex idx ->
  IO (W4.Pred sym)
_isWithinInterval sym idx (AbsIndex absIdx) = do
  preds <- FC.toListFC getConst <$> Ctx.zipWithM (\e a -> Const <$> isWithinInterval' sym e a) idx absIdx
  foldM (W4.andPred sym) (W4.truePred sym) preds


isWithinInterval' ::
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.SymExpr sym tp ->
  AbsInterval tp ->
  IO (W4.Pred sym)
isWithinInterval' sym e ai = case ai of
  AbsIntervalNat (W4.NatSingleRange n) -> do
    n' <- W4.natLit sym n
    W4.isEq sym n' e
  AbsIntervalNat (W4.NatMultiRange lo hiBound) ->
    case hiBound of
      W4.Inclusive hi -> do
        lo' <- W4.natLit sym lo
        hi' <- W4.natLit sym hi
        isLoBound <- W4.natLe sym lo' e
        isHiBound <- W4.natLe sym e hi'
        W4.andPred sym isLoBound isHiBound
      W4.Unbounded -> do
        lo' <- W4.natLit sym lo
        W4.natLe sym lo' e
  AbsIntervalBV w (W4.SingleRange i) -> do
    i' <- W4.bvLit sym w (BV.mkBV w i)
    W4.isEq sym i' e
  AbsIntervalBV w (W4.MultiRange loBound hiBound) -> do
    isLoBound <- case loBound of
      W4.Unbounded -> return $ W4.truePred sym
      W4.Inclusive lo -> do
        lo' <- W4.bvLit sym w (BV.mkBV w lo)
        W4.bvUle sym lo' e
    isHiBound <- case hiBound of
      W4.Unbounded -> return $ W4.truePred sym
      W4.Inclusive hi -> do
        hi' <- W4.bvLit sym w (BV.mkBV w hi)
        W4.bvUle sym e hi'
    W4.andPred sym isLoBound isHiBound

symIdxToAbs ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  SymIndex sym ctx -> AbsIndex ctx
symIdxToAbs (SymIndex symIdxExpr) = AbsIndex $ FC.fmapFC (exprToAbsInterval @sym) symIdxExpr

concreteIdxToSym ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment W4.ConcreteVal ctx ->
  IO (SymIndex sym ctx)
concreteIdxToSym sym conc = SymIndex <$> FC.traverseFC (W4.concreteToSym sym) conc

-- | Invalidate a specific entry at a specific index, which may
-- remove it entirely
invalidateEntry ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym ctx ->
  ArrayEntry sym ctx tp ->
  IO (Maybe (ArrayEntry sym ctx tp))
invalidateEntry sym symIdx e = do
  constEntryCond sym e symIdx >>= \case
    Just False -> return $ Just e
    Just True -> return Nothing
    Nothing -> case e of
      ArrayEntryArr condF v -> do        
        let
          condF' symIdx' = do
            notThis <- W4.notPred sym =<< isEqIndex sym symIdx symIdx'
            cond <- condF symIdx'
            W4.andPred sym notThis cond
        return $ Just $ ArrayEntryArr condF' v
      ArrayEntryVal symIdx' cond v -> do
        notThis <- W4.notPred sym =<< isEqIndex sym symIdx symIdx'
        cond' <- W4.andPred sym notThis cond
        case W4.asConstantPred cond' of
          Just False -> return Nothing
          _ -> return $ Just $ ArrayEntryVal symIdx' cond' v

isEqIndex ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym ctx ->
  SymIndex sym ctx ->
  IO (W4.Pred sym)
isEqIndex sym (SymIndex symIdxExpr1) (SymIndex symIdxExpr2) = do
  preds <- FC.toListFC getConst <$> Ctx.zipWithM (\e1 e2 -> Const <$> W4.isEq sym e1 e2) symIdxExpr1 symIdxExpr2  
  foldM (W4.andPred sym) (W4.truePred sym) preds


-- FIXME: highly inefficient
_mapMInterval ::
  forall k v e m.
  Monad m =>
  IM.Interval k e =>
  Eq k =>
  (k -> v -> m (Maybe v)) ->
  IM.IntervalMap k v ->
  m (IM.IntervalMap k v)
_mapMInterval f im = do
  im' <- catMaybes <$> mapM go (IM.toAscList im)
  return $ IM.fromAscList im'
  where
    go :: (k, v) -> m (Maybe (k, v))
    go (k, v) = f k v >>= \case
      Just v' -> return $ Just (k, v')
      Nothing -> return Nothing

-- FIXME: highly inefficient
mapMIntersecting ::
  forall k v e m.
  Monad m =>
  IM.Interval k e =>
  Ord k =>
  k ->
  (k -> v -> m (Maybe v)) ->
  IM.IntervalMap k v ->
  m (IM.IntervalMap k v)
mapMIntersecting k f im = do
  let (pref, inter, suf) = IM.splitIntersecting im k
  im' <- catMaybes <$> mapM go (IM.toAscList inter)
  return $ IM.fromAscList (IM.toAscList pref ++ im' ++ IM.toAscList suf)
  where
    go :: (k, v) -> m (Maybe (k, v))
    go (k', v) = f k' v >>= \case
      Just v' -> return $ Just (k', v')
      Nothing -> return Nothing

-- FIXME: highly inefficient
mapMIntersection ::
  forall k v e m.
  Monad m =>
  IM.Interval k e =>
  Ord k =>
  (k -> v -> v -> m v) ->
  IM.IntervalMap k v ->
  IM.IntervalMap k v ->
  m (IM.IntervalMap k v)
mapMIntersection f im im' =
  foldM (\im'' (k, v) -> mapMIntersecting k (\k' v' -> Just <$> f k' v v') im'') im' (IM.toList im)

insertWithM ::
  forall k v e m.
  Monad m =>
  IM.Interval k e =>
  Ord k =>
  k ->
  v ->
  (v -> v -> m v) ->
  IM.IntervalMap k v ->
  m (IM.IntervalMap k v)
insertWithM k v f im = case IM.lookup k im of
  Just v' -> do
    v'' <- f v v'
    return $ IM.insert k v'' im
  Nothing -> return $ IM.insert k v im

-- | Invalidate all existing symbolic entries at exactly this index
invalidateEntries ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym ctx ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
invalidateEntries sym symIdx arr = do
  let k = symIdxToAbs @sym symIdx
  cmap <- mapMIntersecting k (\_ -> invalidateEntry sym symIdx) (arrMap arr)
  return $ arr { arrMap = cmap }


muxConditions ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  (SymIndex sym ctx -> IO (W4.Pred sym)) ->
  (SymIndex sym ctx -> IO (W4.Pred sym)) ->
  SymIndex sym ctx ->
  IO (W4.Pred sym)
muxConditions sym p fcondT fcondF symIdx = do
 condT <- fcondT symIdx
 condF <- fcondF symIdx
 W4.baseTypeIte sym p condT condF


muxSymIndex ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  SymIndex sym ctx ->
  SymIndex sym ctx ->
  IO (SymIndex sym ctx)
muxSymIndex sym p (SymIndex symIdxExprT) (SymIndex symIdxExprF) =
 SymIndex <$> Ctx.zipWithM (W4.baseTypeIte sym p) symIdxExprT symIdxExprF

muxEntries ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  W4.Pred sym ->
  ArrayEntry sym ctx tp ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
muxEntries sym p eT eF = case (eT, eF) of
  (ArrayEntryArr fcondT aT, ArrayEntryArr fcondF aF) -> do
    a <- W4.baseTypeIte sym p aT aF
    return $ ArrayEntryArr (muxConditions sym p fcondT fcondF) a
  (ArrayEntryVal idxT condT vT, ArrayEntryVal idxF condF vF) -> do
    idx <- muxSymIndex sym p idxT idxF
    cond <- W4.baseTypeIte sym p condT condF
    a <- W4.baseTypeIte sym p vT vF
    return $ ArrayEntryVal idx cond a
  (ArrayEntryArr fcondT aT, ArrayEntryVal _ _ vF) -> do
    NonEmptyCtxRepr <- return $ nonEmptyCtxRepr @ctx
    W4.BaseArrayRepr repr _ <- return $ W4.exprType aT
    aF <- W4.constantArray sym repr vF
    a <- W4.baseTypeIte sym p aT aF
    return $ ArrayEntryArr (muxConditions sym p fcondT (entryCond sym eF)) a
  (ArrayEntryVal _ _ vT, ArrayEntryArr fcondF aF) -> do
    NonEmptyCtxRepr <- return $ nonEmptyCtxRepr @ctx
    W4.BaseArrayRepr repr _ <- return $ W4.exprType aF
    aT <- W4.constantArray sym repr vT
    a <- W4.baseTypeIte sym p aT aF
    return $ ArrayEntryArr (muxConditions sym p (entryCond sym eT) fcondF) a    
    
addNewEntry ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  SymIndex sym ctx ->
  W4.SymExpr sym tp ->
  -- ^ new entry
  ArrayEntry sym ctx tp ->
  -- ^ old entry
  IO (ArrayEntry sym ctx tp)
addNewEntry sym symIdx new_v old_e = do
  (old_v, isOldEntry) <- readEntry sym symIdx old_e
  e <- W4.baseTypeIte sym isOldEntry old_v new_v
  return $ ArrayEntryVal symIdx (W4.truePred sym) e
