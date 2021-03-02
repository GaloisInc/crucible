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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module What4.CachedArray
  (
    CachedArray
  , writeRange
  , writeSingle
  , readSingle
  , readRange
  , muxArrays
  , initArrayConcrete
  , initArray
  ) where

import           GHC.Natural

import           Control.Lens ( (.=), (.~), (&) )
import           Control.Monad ( foldM, join )
import           Control.Monad.Trans ( lift )
import           Data.Functor.Const
import           Data.Maybe ( catMaybes )
import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.List (find)
import           Data.Maybe (mapMaybe)
  
import           Data.Parameterized.Some
import qualified Data.Parameterized.Nonce as N
import           Data.IntervalMap.Generic.Strict ( IntervalMap )
import qualified Data.IntervalMap.Generic.Strict as IM
import qualified Data.IntervalMap.Generic.Interval as IM
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr ( type (<=) )
import qualified Data.BitVector.Sized as BV

import qualified Lang.Crucible.Utils.MuxTree as MT

import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import qualified What4.Concrete as W4
import qualified What4.Utils.AbstractDomains as W4
import qualified What4.Utils.BVDomain as BVD

------------------------------------------------
-- Interface

-- TODO: add coalescing function for merging adjacent entries
-- into symbolic arrays

writeRange ::
  forall sym ctx tp.
  NonEmptyCtx ctx =>
  W4.IsSymExprBuilder sym =>
  sym ->
  -- | base address to write to
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  -- | size of write 
  W4.SymExpr sym (CtxHead ctx) ->
  -- | symbolic value to write
  W4.SymArray sym (Ctx.EmptyCtx Ctx.::> (CtxHead ctx)) tp ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
writeRange sym loExpr offExpr val arr | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx =
  arrConstraints arr $ do
  rng <- mkSymRangeOff sym loExpr offExpr
  arr' <- invalidateEntries sym gen rng arr
  -- offset the incoming array so that its value at zero becomes the value at
  -- the base address
  let
    off = indexToOffset $ symRangeLo rng
    vals :: SymIndex sym ctx -> IO (W4.PartExpr (W4.Pred sym) (W4.SymExpr sym tp))
    vals idx' = do
        p <- isInRange sym rng idx'
        (SymOffset idxOffsetExpr) <- indexToOffset <$> subSymOffset sym idx' off
        v <- W4.arrayLookup sym val (Ctx.empty Ctx.:> idxOffsetExpr)
        return $ W4.mkPE p v
  entry <- mkMultiEntry sym gen vals
  arr'' <- insertWithM (symRangeToAbs rng) (toPMuxTree sym entry) (mergeEntriesMux sym gen (isInRange sym rng)) (arrMap arr')
  incNonce $ arr { arrMap = arr''}
  where
    gen = arrNonceGen arr

writeSingle ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  W4.SymExpr sym  tp ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
writeSingle sym symIdxExpr val arr = arrConstraints arr $ do
  arr' <- invalidateEntries sym gen (SymRangeSingle symIdx) arr
  entry <- mkValEntry sym gen symIdx val
  
  arr'' <- insertWithM (symIdxToAbs symIdx) (toPMuxTree sym entry) (mergeEntriesMux sym gen (isEqIndex sym symIdx)) (arrMap arr')
  incNonce $ arr { arrMap = arr'' }
  where
    gen = arrNonceGen arr
    symIdx = mkSymIndex symIdxExpr


readSingle ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) idx ->
  CachedArray sym idx tp ->
  IO (W4.SymExpr sym tp)
readSingle sym symIdxExpr arr = readArrayBase sym symIdx arr
  where
    symIdx = SymIndex symIdxExpr Nothing


readRange ::
  forall sym ctx tp.
  NonEmptyCtx ctx =>
  W4.IsSymExprBuilder sym =>
  sym ->
  -- | base address to read from
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  -- | size of read 
  W4.SymExpr sym (CtxHead ctx) ->  
  CachedArray sym ctx tp ->
  IO (W4.SymArray sym (Ctx.EmptyCtx Ctx.::> (CtxHead ctx)) tp)
readRange sym loExpr offExpr arr | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx = do
  rng <- mkSymRangeOff sym loExpr offExpr
  let absIdx = symRangeToAbs rng
  -- offset the outgoing array so that its value at zero is the value at
  -- the base address
  
  var <- W4.freshBoundVar sym W4.emptySymbol (W4.exprType offExpr)
  let off = SymOffset (W4.varExpr sym var)
  offsetIdx <- addSymOffset sym (symRangeLo rng) off
  body <- readArrayBase sym (offsetIdx { symIdxAbs = Just absIdx}) arr
  fn <- W4.definedFn sym (W4.safeSymbol "readRange") (Ctx.empty Ctx.:> var) body W4.AlwaysUnfold
  W4.arrayFromFn sym fn


muxArrays ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  CachedArray sym idx tp ->
  CachedArray sym idx tp ->
  IO (CachedArray sym idx tp)
muxArrays sym p arr1 arr2 = case arr1 == arr2 of
  True -> return arr1
  False -> arrConstraints arr1 $ do
    arr' <- mapMIntersection (\_ eT eF -> muxEntries sym p eT eF) (arrMap arr1) (arrMap arr2)
    incNonce $ arr1 { arrMap = arr' }

-- | Initialize an array with symbolic contents at concrete locations
initArrayConcrete ::
  forall sym idx tp idx' tp'.
  W4.IsSymExprBuilder sym =>
  ShowF (W4.SymExpr sym) =>
  idx ~ (idx' Ctx.::> tp') =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  W4.BaseTypeRepr tp ->
  Map (Ctx.Assignment W4.ConcreteVal idx) (W4.SymExpr sym tp) ->
  IO (CachedArray sym idx tp)
initArrayConcrete sym gen repr m = do
  nonce <- N.freshNonce gen
  im <- IM.fromList <$> mapM go (Map.assocs m)
  return $ CachedArray im id repr gen nonce
  where
    go ::
      (Ctx.Assignment W4.ConcreteVal idx, W4.SymExpr sym tp) ->
      IO (AbsIndex idx, PMuxTree sym (ArrayEntry sym idx tp))
    go (cidx, v) = do
      symIdx <- concreteIdxToSym sym cidx
      entry <- mkValEntry sym gen symIdx v
      return $ (symIdxToAbs symIdx, toPMuxTree sym entry)

-- | Initialize an array with symbolic contents at symbolic locations
initArray ::
  forall sym idx tp idx' tp'.
  W4.IsSymExprBuilder sym =>
  ShowF (W4.SymExpr sym) =>
  idx ~ (idx' Ctx.::> tp') =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  W4.BaseTypeRepr tp ->
  Map (Ctx.Assignment (W4.SymExpr sym) idx) (W4.SymExpr sym tp) ->
  IO (CachedArray sym idx tp)
initArray sym gen repr m = do
  nonce <- N.freshNonce gen
  im <- IM.fromList <$> mapM go (Map.assocs m)
  return $ CachedArray im id repr gen nonce
  where
    go ::
      (Ctx.Assignment (W4.SymExpr sym) idx, W4.SymExpr sym tp) ->
      IO (AbsIndex idx, PMuxTree sym (ArrayEntry sym idx tp))
    go (symIdxExpr, v) = do
      let
        symIdx = SymIndex symIdxExpr Nothing
      entry <- mkValEntry sym gen symIdx v
      return $ (symIdxToAbs symIdx, toPMuxTree sym entry)

---------------------------------------------------
-- Implementation
type family ScopeOf k :: * where
  ScopeOf (W4B.ExprBuilder t st fs) = t

data CachedArray sym (ctx :: Ctx.Ctx W4.BaseType) (tp :: W4.BaseType) where
  CachedArray ::
    {
      arrMap :: IntervalMap (AbsIndex ctx) (PMuxTree sym (ArrayEntry sym ctx tp))
    , arrConstraints :: forall a. ((NonEmptyCtx ctx, ShowF (W4.SymExpr sym)) => a) -> a
    , arrTypeRepr :: W4.BaseTypeRepr tp
    , arrNonceGen :: N.NonceGenerator IO (ScopeOf sym)
    , _arrNonce :: N.Nonce (ScopeOf sym) (ctx Ctx.::> tp)
    } -> CachedArray sym ctx tp

instance Eq (CachedArray sym idx tp) where
  (CachedArray _ _ _ _ nonce1) == (CachedArray _ _ _ _ nonce2) = case testEquality nonce1 nonce2 of
    Just Refl -> True
    _ -> False

incNonce :: CachedArray sym idx tp -> IO (CachedArray sym idx tp)
incNonce (CachedArray am ac tr gen _) = do
  nonce <- N.freshNonce gen
  return $ CachedArray am ac tr gen nonce

-- | An array entry defines a set of possible values for a given
-- abstract domain. Entries may overlap, and so as an invariant we
-- preserve the fact that at each logical index, exactly one entry is valid
data ArrayEntry sym ctx tp where
  ArrayEntry ::
    { entryVals :: (SymIndex sym ctx -> IO (W4.PartExpr (W4.Pred sym) (W4.SymExpr sym tp)))
    , entryNonce :: N.Nonce (ScopeOf sym) tp
    } -> ArrayEntry sym ctx tp


incNonceEntry ::
  N.NonceGenerator IO (ScopeOf sym) ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
incNonceEntry gen (ArrayEntry vals _) = do
  nonce <- N.freshNonce gen
  return $ ArrayEntry vals nonce

instance Eq (ArrayEntry sym ctx tp) where
  e1 == e2 = entryNonce e1 == entryNonce e2

instance Ord (ArrayEntry sym ctx tp) where
  compare e1 e2 = compare (entryNonce e1) (entryNonce e2)

-- | A symbolic index into the array. It represents the index for a single array element,
-- although its value may be symbolic
data SymIndex sym ctx =
  SymIndex
    { -- | the symbolic index
      _symIdxExpr :: Ctx.Assignment (W4.SymExpr sym) ctx
      -- | an optional override for the abstract domain of the index
    , symIdxAbs :: Maybe (AbsIndex ctx)
    }

deriving instance (W4.IsSymExprBuilder sym => Eq (SymIndex sym ctx))
deriving instance (W4.IsSymExprBuilder sym => Ord (SymIndex sym ctx))

-- | An offset is an index into the last element of the array index
-- A value range is always representable as a base + offset
data SymOffset sym ctx where
  SymOffset :: W4.SymExpr sym tp -> SymOffset sym (ctx Ctx.::> tp)


indexToOffset ::
  forall sym ctx.
  NonEmptyCtx ctx =>
  W4.IsSymExprBuilder sym =>
  SymIndex sym ctx ->
  SymOffset sym ctx
indexToOffset (SymIndex eCtx _) | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx =
  let
    idx = Ctx.lastIndex (Ctx.size eCtx)
    e = eCtx Ctx.! idx
  in SymOffset e

addSymOffset ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym ctx ->
  SymOffset sym ctx ->
  IO (SymIndex sym ctx)
addSymOffset sym (SymIndex eCtx _) (SymOffset off) = do
  let
    idx = Ctx.lastIndex (Ctx.size eCtx)
    e = eCtx Ctx.! idx
  e' <- case W4.exprType off of
    W4.BaseIntegerRepr -> W4.intAdd sym e off
    W4.BaseBVRepr _ -> W4.bvAdd sym e off
    _ -> fail $ "Unsupported type"
  return $ SymIndex (eCtx & (ixF idx) .~ e') Nothing

negateSymOffset ::
  W4.IsSymExprBuilder sym =>
  sym ->
  SymOffset sym ctx ->
  IO (SymOffset sym ctx)
negateSymOffset sym (SymOffset off) = do
  e' <- case W4.exprType off of
    W4.BaseIntegerRepr -> W4.intNeg sym off
    W4.BaseBVRepr _ -> W4.bvNeg sym off
    _ -> fail $ "Unsupported type"  
  return $ SymOffset e'

-- | Previous offset from the given one, to create an exclusive upper bound
prevSymOffset ::
  W4.IsSymExprBuilder sym =>
  sym ->
  SymOffset sym ctx ->
  IO (SymOffset sym ctx)
prevSymOffset sym (SymOffset off) = do
  e' <- case W4.exprType off of
    W4.BaseIntegerRepr -> do
      one <- W4.intLit sym 1
      W4.intSub sym off one
    W4.BaseBVRepr w -> do
      one <- W4.bvLit sym w (BV.mkBV w 1)
      W4.bvSub sym off one
    _ -> fail $ "Unsupported type"  
  return $ SymOffset e'

subSymOffset ::
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym ctx ->
  SymOffset sym ctx ->
  IO (SymIndex sym ctx)  
subSymOffset sym idx off = do
  negoff <- negateSymOffset sym off
  addSymOffset sym idx negoff 

mkSymIndex ::
  forall sym ctx.
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  SymIndex sym ctx
mkSymIndex e = SymIndex e Nothing

-- | Represents a symbolic range, where equality and ordering is defined on the
-- abstract domain of the underlying expression
data SymRange sym ctx =
    SymRangeSingle (SymIndex sym ctx)
  | SymRangeMulti (SymIndex sym ctx) (SymIndex sym ctx)

symRangeLo :: SymRange sym ctx -> SymIndex sym ctx
symRangeLo (SymRangeSingle symIdx) = symIdx
symRangeLo (SymRangeMulti loIdx _) = loIdx

symRangeHi :: SymRange sym ctx -> SymIndex sym ctx
symRangeHi (SymRangeSingle symIdx) = symIdx
symRangeHi (SymRangeMulti _ hiIdx) = hiIdx

symRangeToAbs ::
  W4.IsSymExprBuilder sym =>
  SymRange sym ctx ->
  AbsIndex ctx
symRangeToAbs (SymRangeSingle symIdx) = symIdxToAbs symIdx
symRangeToAbs (SymRangeMulti loIdx hiIdx) =
  joinAbsIndex (symIdxToAbs loIdx) (symIdxToAbs hiIdx)


-- | Create a range that is exclusive of the given offset
-- i.e. 2 + 4 --> (2, 5)
mkSymRangeOff ::
  forall sym ctx ctx' offtp.
  ctx ~ (ctx' Ctx.::> offtp) =>
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  W4.SymExpr sym offtp ->
  IO (SymRange sym ctx)
mkSymRangeOff sym loExpr offExpr = do
  let
    lo = mkSymIndex @sym loExpr
    off = SymOffset offExpr
  offPrev <- prevSymOffset sym off
  hi <- addSymOffset sym lo offPrev
  return $ (SymRangeMulti lo hi)

data NonEmptyCtxRepr (ctx :: Ctx.Ctx k) where
  NonEmptyCtxRepr :: NonEmptyCtxRepr (ctx Ctx.::> x)

class NonEmptyCtx (ctx :: Ctx.Ctx k) where
  type CtxHead ctx :: k
  type CtxTail ctx :: Ctx.Ctx k
  nonEmptyCtxRepr :: NonEmptyCtxRepr ctx

instance NonEmptyCtx (ctx Ctx.::> tp) where
  type CtxHead (ctx Ctx.::> tp) = tp
  type CtxTail (ctx Ctx.::> tp) = ctx
  nonEmptyCtxRepr = NonEmptyCtxRepr


constEntryCond ::
  W4.IsSymExprBuilder sym =>
  ArrayEntry sym ctx tp ->
  SymIndex sym ctx ->
  IO (Maybe Bool)
constEntryCond entry idx = entryVals entry idx >>= \case
  W4.Unassigned -> return $ Just False
  W4.PE p _ -> return $ W4.asConstantPred p

data AbsInterval tp where
  AbsIntervalInt :: W4.ValueRange Integer -> AbsInterval W4.BaseIntegerType
  AbsIntervalBV :: (1 <= w) => W4.NatRepr w -> W4.ValueRange Integer -> AbsInterval (W4.BaseBVType w)

data AbsIntervalEnd tp where
  AbsIntervalEndInt :: W4.ValueBound Integer -> AbsIntervalEnd W4.BaseIntegerType
  AbsIntervalEndBV :: (1 <= w) => W4.NatRepr w -> W4.ValueBound Integer -> AbsIntervalEnd (W4.BaseBVType w)
  
 
instance TestEquality AbsInterval where
  testEquality a1 a2 = case compareF a1 a2 of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF AbsInterval where
  compareF a1 a2 = case (a1, a2) of
    (AbsIntervalInt (W4.SingleRange n1), AbsIntervalInt (W4.SingleRange n2)) ->
      fromOrdering $ compare n1 n2
    (AbsIntervalInt n1, AbsIntervalInt n2) ->
      fromOrdering $ 
      compare (W4.rangeLowBound n1) (W4.rangeHiBound n2)
      <> compare (W4.rangeLowBound n1) (W4.rangeHiBound n2)
    (AbsIntervalBV w1 (W4.SingleRange i1), AbsIntervalBV w2 (W4.SingleRange i2)) ->
      lexCompareF w1 w2 $ fromOrdering $ compare i1 i2
    (AbsIntervalBV w1 i1, AbsIntervalBV w2 i2) ->
      lexCompareF w1 w2 $ fromOrdering $
        compare (W4.rangeLowBound i1) (W4.rangeLowBound i2)
        <> compare (W4.rangeHiBound i1) (W4.rangeHiBound i2)
    (AbsIntervalInt{}, AbsIntervalBV{}) -> LTF
    (AbsIntervalBV{}, AbsIntervalInt{}) -> GTF

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
    (AbsIntervalEndInt n1, AbsIntervalEndInt n2) -> fromOrdering $ compare n1 n2
    (AbsIntervalEndBV w1 i1, AbsIntervalEndBV w2 i2) ->
      lexCompareF w1 w2 $ fromOrdering $ compare i1 i2
    (AbsIntervalEndInt{}, AbsIntervalEndBV{}) -> LTF
    (AbsIntervalEndBV{}, AbsIntervalEndInt{}) -> GTF



instance IM.Interval (AbsInterval tp) (AbsIntervalEnd tp) where
  lowerBound ai = case ai of
    AbsIntervalInt v -> AbsIntervalEndInt $ W4.rangeLowBound v
    AbsIntervalBV w v -> AbsIntervalEndBV w $ W4.rangeLowBound v
  upperBound ai = case ai of
    AbsIntervalInt v -> AbsIntervalEndInt $ W4.rangeLowBound v
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
  W4.BaseIntegerRepr -> AbsIntervalInt v
  W4.BaseBVRepr w -> bvDomainRange w v
  _ -> error "Unsupported type"


readArrayBase ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym idx ->
  CachedArray sym idx tp ->
  IO (W4.SymExpr sym tp)
readArrayBase sym symIdx arr = do
  let
    intersecting = IM.toAscList $ IM.intersecting (arrMap arr) (symIdxToAbs symIdx)
  entries <- mapM expandEntry $ concat $ map (viewPMuxTree . snd) intersecting
  case entries of
    [(W4.PE p (AsOrd e), path_cond)]
      | Just True <- W4.asConstantPred path_cond
      , Just True <- W4.asConstantPred p -> return e
    entryExprs -> arrConstraints arr $ do
      
      muxTree <- mkPMuxTreePartial sym entryExprs
      MT.collapseMuxTree sym ite muxTree >>= \case
        Just (AsOrd e) -> return e
        -- garbage result
        Nothing -> W4.freshConstant sym W4.emptySymbol (arrTypeRepr arr)
      
  where
    ite ::
      W4.Pred sym -> 
      Maybe (AsOrd (W4.SymExpr sym) tp) ->
      Maybe (AsOrd (W4.SymExpr sym) tp) ->
      IO (Maybe (AsOrd (W4.SymExpr sym) tp))
    ite p (Just (AsOrd e1)) (Just (AsOrd e2)) = (Just . AsOrd) <$> W4.baseTypeIte sym p e1 e2
    ite _ Nothing (Just e2) = return $ Just e2
    ite _ (Just e1) Nothing = return $ Just e1
    ite _ Nothing Nothing = return Nothing
    
    expandEntry ::
      (ArrayEntry sym idx tp, W4.Pred sym) ->
      IO (W4.PartExpr (W4.Pred sym) (AsOrd (W4.SymExpr sym) tp), W4.Pred sym)
    expandEntry (entry, path_cond) = do
      val <- entryVals entry symIdx
      return $ (fmap AsOrd val, path_cond)

mkValEntry ::
  W4.IsSymExprBuilder sym =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  SymIndex sym ctx ->
  W4.SymExpr sym tp ->
  IO (ArrayEntry sym ctx tp)
mkValEntry sym gen idx v = do
  let vals idx' = do
        p <- isEqIndex sym idx idx'
        return $ W4.mkPE p v
  mkMultiEntry sym gen vals

mkMultiEntry ::
  W4.IsSymExprBuilder sym =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  (SymIndex sym ctx -> IO (W4.PartExpr (W4.Pred sym) (W4.SymExpr sym tp))) ->
  IO (ArrayEntry sym ctx tp)
mkMultiEntry _sym gen vals = do
  nonce <- N.freshNonce gen
  return $ ArrayEntry vals nonce

symIdxToAbs ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  SymIndex sym ctx -> AbsIndex ctx
symIdxToAbs (SymIndex symIdxExpr Nothing) = AbsIndex $ FC.fmapFC (exprToAbsInterval @sym) symIdxExpr
symIdxToAbs (SymIndex _ (Just absIdx)) = absIdx

concreteIdxToSym ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment W4.ConcreteVal ctx ->
  IO (SymIndex sym ctx)
concreteIdxToSym sym conc = do
 symIdxExpr <- FC.traverseFC (W4.concreteToSym sym) conc
 return $ SymIndex symIdxExpr Nothing


-- | Invalidate all entries within the given range
-- TODO: delete entries which are statically invalid
invalidateRange ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  ShowF (W4.SymExpr sym) =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  -- | range to invalidate
  SymRange sym ctx ->
  -- | range of this entry
  AbsIndex ctx ->
  ArrayEntry sym ctx tp ->
  IO (Maybe (ArrayEntry sym ctx tp))
invalidateRange sym gen invalid_rng _this_rng entry = do
  let vals symIdx' = do
        notThis <- W4.notPred sym =<< isInRange sym invalid_rng symIdx'
        val <- entryVals entry symIdx'
        W4.runPartialT sym notThis $ W4.returnPartial val
  entry' <- incNonceEntry gen $ entry { entryVals = vals }
  return $ Just entry'


isInRange ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymRange sym ctx ->
  SymIndex sym ctx ->
  IO (W4.Pred sym)  
isInRange sym rng symIdx2@(SymIndex symIdxExpr _) = case rng of
  SymRangeSingle symIdx1 -> isEqIndex sym symIdx1 symIdx2
  SymRangeMulti (SymIndex loIdxExpr _) (SymIndex hiIdxExpr _) -> do
    lo <- FC.toListFC getConst <$> Ctx.zipWithM doLe loIdxExpr symIdxExpr
    hi <- FC.toListFC getConst <$> Ctx.zipWithM doLe symIdxExpr hiIdxExpr
    foldM (W4.andPred sym) (W4.truePred sym) $ lo ++ hi
  where
    doLe ::
      forall tp.
      W4.SymExpr sym tp ->
      W4.SymExpr sym tp ->
      IO (Const (W4.Pred sym) tp)
    doLe e1 e2 = Const <$> case W4.exprType e1 of
      W4.BaseBVRepr _ -> W4.bvUle sym e1 e2
      W4.BaseIntegerRepr -> W4.intLe sym e1 e2
      _ -> fail "isInRange: unsupported type"

isEqIndex ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymIndex sym ctx ->
  SymIndex sym ctx ->
  IO (W4.Pred sym)
isEqIndex sym (SymIndex symIdxExpr1 _) (SymIndex symIdxExpr2 _) = do
  preds <- FC.toListFC getConst <$> Ctx.zipWithM (\e1 e2 -> Const <$> W4.isEq sym e1 e2) symIdxExpr1 symIdxExpr2  
  foldM (W4.andPred sym) (W4.truePred sym) preds


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
  case IM.size inter of
    0 -> return im
    _ -> do
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
  N.NonceGenerator IO (ScopeOf sym) ->
  SymRange sym ctx ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
invalidateEntries sym gen symRange arr = arrConstraints arr $ do
  cmap <- mapMIntersecting absIndex (\k v -> getMaybe <$> pmuxTreeMaybeOp sym (invalidateRange sym gen symRange k) v) (arrMap arr)
  return $ arr { arrMap = cmap }
  where
    absIndex = symRangeToAbs symRange
    getMaybe :: PMuxTree sym (ArrayEntry sym ctx tp) -> Maybe (PMuxTree sym (ArrayEntry sym ctx tp))
    getMaybe mt | isEmptyPMuxTree mt = Nothing
    getMaybe mt = Just mt
      
buildMuxTree :: (W4.IsExprBuilder sym, Ord a) => sym -> a -> [(a, W4.Pred sym)] -> IO (MT.MuxTree sym a)
buildMuxTree sym a as =
  foldM (\mt (a',p) -> MT.mergeMuxTree sym p (MT.toMuxTree sym a') mt) (MT.toMuxTree sym a) as


joinAbsIndex ::
  AbsIndex ctx ->
  AbsIndex ctx ->
  AbsIndex ctx
joinAbsIndex (AbsIndex idx1) (AbsIndex idx2) =
  AbsIndex $ Ctx.zipWith joinAbsInterval idx1 idx2

joinAbsInterval ::
  AbsInterval tp ->
  AbsInterval tp ->
  AbsInterval tp
joinAbsInterval a1 a2 = case (a1, a2) of
  (AbsIntervalInt rng1, AbsIntervalInt rng2) -> AbsIntervalInt $ W4.avJoin W4.BaseIntegerRepr rng1 rng2
  (AbsIntervalBV w rng1, AbsIntervalBV _ rng2) -> AbsIntervalBV w $ W4.avJoin W4.BaseIntegerRepr rng1 rng2


muxEntries ::
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  PMuxTree sym (ArrayEntry sym ctx tp) ->
  PMuxTree sym (ArrayEntry sym ctx tp) ->
  IO (PMuxTree sym (ArrayEntry sym ctx tp))
muxEntries sym p mtT mtF = MT.mergeMuxTree sym p mtT mtF

mergeEntries ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  ShowF (W4.SymExpr sym) =>
  NonEmptyCtx ctx =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  (SymIndex sym ctx -> IO (W4.Pred sym)) ->
  ArrayEntry sym ctx tp ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
mergeEntries sym gen pickLeftFn e1 e2 = do
  let vals symIdx' = do
        pickLeft <- pickLeftFn symIdx'
        val1 <- entryVals e1 symIdx'
        val2 <- entryVals e2 symIdx'
        W4.mergePartial sym (\p a b -> lift $ W4.baseTypeIte sym p a b)
          pickLeft val1 val2
  incNonceEntry gen $ e1 { entryVals = vals }

mergeEntriesMux ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  ShowF (W4.SymExpr sym) =>
  NonEmptyCtx ctx =>
  sym ->
  N.NonceGenerator IO (ScopeOf sym) ->
  (SymIndex sym ctx -> IO (W4.Pred sym)) ->
  PMuxTree sym (ArrayEntry sym ctx tp) ->
  PMuxTree sym (ArrayEntry sym ctx tp) ->
  IO (PMuxTree sym (ArrayEntry sym ctx tp))
mergeEntriesMux sym gen pickLeftFn = pmuxTreeBinOp sym (mergeEntries sym gen pickLeftFn)

data AsOrd f tp where
  AsOrd :: OrdF f => { _unAsOrd :: f tp } -> AsOrd f tp

instance Eq (AsOrd f tp) where
  (AsOrd a) == (AsOrd b) = case compareF a b of
    EQF -> True
    _ -> False

instance Ord (AsOrd f tp) where
  compare (AsOrd a) (AsOrd b) = toOrdering $ compareF a b

-- | A partial mux tree
type PMuxTree sym tp = MT.MuxTree sym (Maybe tp)

viewPMuxTree :: forall sym a. PMuxTree sym a -> [(a, W4.Pred sym)]
viewPMuxTree mt = mapMaybe go $ MT.viewMuxTree mt
  where
    go :: (Maybe a, W4.Pred sym) -> Maybe (a, W4.Pred sym)
    go (Just a, p) = Just (a, p)
    go _ = Nothing

isEmptyPMuxTree :: PMuxTree sym tp -> Bool
isEmptyPMuxTree mt = case MT.viewMuxTree mt of
  [(Nothing, _)] -> True
  _ -> False

mkPMuxTree ::
  (W4.IsExprBuilder sym, Ord a) =>
  sym ->
  [(a, W4.Pred sym)] ->
  IO (PMuxTree sym a)
mkPMuxTree sym ls = buildMuxTree sym Nothing (map (\(a, p) -> (Just a, p)) ls)

mkPMuxTreePartial ::
  forall sym a.
  (W4.IsExprBuilder sym, Ord a) =>
  sym ->
  [(W4.PartExpr (W4.Pred sym) a, W4.Pred sym)] ->
  IO (PMuxTree sym a)
mkPMuxTreePartial sym ls = mkPMuxTree sym =<< (catMaybes <$> mapM go ls)
  where
    go :: (W4.PartExpr (W4.Pred sym) a, W4.Pred sym) -> IO (Maybe (a, W4.Pred sym))
    go (W4.PE p a, cond) = do
      p' <- W4.andPred sym p cond
      return $ Just (a, p')
    go (W4.Unassigned, _) = return Nothing


pmuxTreeMaybeOp ::
  (W4.IsExprBuilder sym, Ord a, Ord b) =>
  sym ->
  (a -> IO (Maybe b)) ->
  PMuxTree sym a ->
  IO (PMuxTree sym b)
pmuxTreeMaybeOp sym f mt = MT.muxTreeUnaryOp sym (\a -> join <$> mapM f a) mt

_pmuxTreeUnaryOp ::
  (W4.IsExprBuilder sym, Ord b) =>
  sym ->
  (a -> IO b) ->
  PMuxTree sym a ->
  IO (PMuxTree sym b)  
_pmuxTreeUnaryOp sym f mt = MT.muxTreeUnaryOp sym (\a -> mapM f a) mt


pmuxTreeBinOp ::
  forall sym a b c.
  (W4.IsExprBuilder sym, Ord c) =>
  sym ->
  (a -> b -> IO c) ->
  PMuxTree sym a ->
  PMuxTree sym b ->
  IO (PMuxTree sym c)  
pmuxTreeBinOp sym f mt1 mt2 = MT.muxTreeBinOp sym g mt1 mt2
  where
    g :: Maybe a -> Maybe b -> IO (Maybe c)
    g (Just a) (Just b) = Just <$> f a b
    g _ _ = return Nothing

toPMuxTree :: W4.IsExprBuilder sym => sym -> a -> PMuxTree sym a
toPMuxTree sym a = MT.toMuxTree sym (Just a)
