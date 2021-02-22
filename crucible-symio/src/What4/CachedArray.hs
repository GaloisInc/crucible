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
writeRange sym loExpr offExpr val arr | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx = do
  rng <- mkSymRangeOff sym loExpr offExpr
  let absIdx = symRangeToAbs rng
  arr' <- invalidateEntries sym rng arr
  -- offset the incoming array so that its value at zero becomes the value at
  -- the base address
  let off = indexToOffset $ symRangeLo rng
  (symIdx, vars) <- freshIndex sym Nothing (FC.fmapFC W4.exprType loExpr)
  (SymOffset idxOffsetExpr) <- indexToOffset <$> subSymOffset sym symIdx off
  body <- W4.arrayLookup sym val (Ctx.empty Ctx.:> idxOffsetExpr)
  fn <- W4.definedFn sym (W4.safeSymbol "writeRange") vars body W4.AlwaysUnfold
  val' <- W4.arrayFromFn sym fn
  let entry = ArrayEntryArr (isInRange sym rng) val'
  arr'' <- insertWithM absIdx entry (mergeEntries sym) (arrMap arr')
  return $ arr { arrMap = arr'' }


writeSingle ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  W4.SymExpr sym  tp ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
writeSingle sym symIdxExpr val arr = arrConstraints arr $ do  
  arr' <- invalidateEntries sym (SymRangeSingle symIdx) arr
  let entry = ArrayEntryVal symIdx (W4.truePred sym) val
  arr'' <- insertWithM absIdx entry (mergeEntries sym) (arrMap arr')
  return $ arr { arrMap = arr'' }
  where
    absIdx = symIdxToAbs symIdx
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
        symIdx = SymIndex symIdxExpr Nothing
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
data SymIndex sym ctx =
  SymIndex
    { -- | the symbolic index
      _symIdxExpr :: Ctx.Assignment (W4.SymExpr sym) ctx
      -- | an optional override for the abstract domain of the index
    , symIdxAbs :: Maybe (AbsIndex ctx)
    }

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

data SymRange sym ctx =
    SymRangeSingle (SymIndex sym ctx)
  | SymRangeMulti (SymIndex sym ctx) (SymIndex sym ctx)

symRangeLo :: SymRange sym ctx -> SymIndex sym ctx
symRangeLo (SymRangeSingle symIdx) = symIdx
symRangeLo (SymRangeMulti loIdx _) = loIdx

symRangeToAbs ::
  W4.IsSymExprBuilder sym =>
  SymRange sym ctx ->
  AbsIndex ctx
symRangeToAbs (SymRangeSingle symIdx) = symIdxToAbs symIdx
symRangeToAbs (SymRangeMulti loIdx hiIdx) =
  joinAbsIndex (symIdxToAbs loIdx) (symIdxToAbs hiIdx)

mkSymRange ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  SymRange sym ctx
mkSymRange loExpr hiExpr = case testEquality loExpr hiExpr of
  Just Refl -> SymRangeSingle $ mkSymIndex loExpr
  Nothing -> SymRangeMulti (mkSymIndex @sym loExpr) (mkSymIndex @sym hiExpr)


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
  hi <- addSymOffset sym lo off
  return $ (SymRangeMulti lo hi)

isConcreteIndex :: W4.IsSymExprBuilder sym => SymIndex sym ctx -> Bool
isConcreteIndex (SymIndex symIdxExpr _) = FC.allFC W4.baseIsConcrete symIdxExpr

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

addIntervals ::
  AbsInterval tp ->
  AbsInterval tp ->
  AbsInterval tp
addIntervals i1 i2 = case (i1, i2) of
  (AbsIntervalInt n1, AbsIntervalInt n2) -> AbsIntervalInt (W4.addRange n1 n2)
  (AbsIntervalBV w bv1, AbsIntervalBV _ bv2) -> AbsIntervalBV w (W4.addRange bv1 bv2)

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
readArrayBase sym symIdx arr = case isConcreteIndex symIdx of
  True | Just e@(ArrayEntryVal _ _ v) <- IM.lookup k (arrMap arr) -> do
    constEntryCond sym e symIdx >>= \case
      Just True -> return v
      _ -> symbolic
  _ -> symbolic      
  where
    k = symIdxToAbs @sym symIdx
    
    symbolic :: IO (W4.SymExpr sym tp)
    symbolic = do
      let intersecting = IM.toAscList $ IM.intersecting (arrMap arr) k
      arrConstraints arr $ 
        mapM (\(_, entry) -> readEntry sym symIdx entry) intersecting >>= \case  
          [] -> fail "readArray: unexpected empty result"
          ((r, _) : rest) -> collapse r rest

    collapse ::
      W4.SymExpr sym tp ->
      [(W4.SymExpr sym tp, W4.Pred sym)] ->
      IO (W4.SymExpr sym tp)
    collapse default_ ((r, cond) : rest) = W4.iteM W4.baseTypeIte sym cond (return r) (collapse default_ rest)
    collapse default_ [] = return default_

readEntry ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  SymIndex sym ctx ->
  ArrayEntry sym ctx tp ->
  IO (W4.SymExpr sym tp, W4.Pred sym)
readEntry sym symIdx@(SymIndex symIdxExpr _) entry = do
  cond <- entryCond sym entry symIdx
  case entry of
    ArrayEntryArr _ arr -> do
      NonEmptyCtxRepr <- return $ nonEmptyCtxRepr @_ @ctx
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
  AbsIntervalInt (W4.SingleRange n) -> do
    n' <- W4.intLit sym n
    W4.isEq sym n' e
  AbsIntervalInt (W4.MultiRange loBound hiBound) -> do
    isLoBound <- case loBound of
      W4.Unbounded -> return $ W4.truePred sym
      W4.Inclusive lo -> do
        lo' <- W4.intLit sym lo
        W4.intLe sym lo' e
    isHiBound <- case hiBound of
      W4.Unbounded -> return $ W4.truePred sym
      W4.Inclusive hi -> do
        hi' <- W4.intLit sym hi
        W4.intLe sym e hi'
    W4.andPred sym isLoBound isHiBound
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
invalidateRange ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymRange sym ctx ->
  ArrayEntry sym ctx tp ->
  IO (Maybe (ArrayEntry sym ctx tp))
invalidateRange sym rng e = case e of
  ArrayEntryArr condF v -> do        
    let
      condF' symIdx' = do
        notThis <- W4.notPred sym =<< isInRange sym rng symIdx'
        cond <- condF symIdx'
        W4.andPred sym notThis cond
      entry = ArrayEntryArr condF' v

    freshIdx <- mkSymIndex <$> FC.traverseFC (W4.freshConstant sym W4.emptySymbol) (rangeRepr rng)
    constEntryCond sym entry freshIdx >>= \case
      Just False -> return $ Nothing
      _ -> return $ Just entry
  ArrayEntryVal symIdx' cond v -> do
    notThis <- W4.notPred sym =<< isInRange sym rng symIdx'
    cond' <- W4.andPred sym notThis cond
    case W4.asConstantPred cond' of
      Just False -> return Nothing
      _ -> return $ Just $ ArrayEntryVal symIdx' cond' v

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
  SymRange sym ctx ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
invalidateEntries sym symRange arr = do
  cmap <- mapMIntersecting absIdx (\_ -> invalidateRange sym symRange) (arrMap arr)
  return $ arr { arrMap = cmap }
  where
    absIdx = symRangeToAbs symRange

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

muxSymIndex ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.Pred sym ->
  SymIndex sym ctx ->
  SymIndex sym ctx ->
  IO (SymIndex sym ctx)
muxSymIndex sym p (SymIndex symIdxExprT mabsT) (SymIndex symIdxExprF mabsF) = do
 symIdxExpr <- Ctx.zipWithM (W4.baseTypeIte sym p) symIdxExprT symIdxExprF
 return $ SymIndex symIdxExpr mabs
 where
   mabs :: Maybe (AbsIndex ctx)
   mabs = do
     absT <- mabsT
     absF <- mabsF
     return $ joinAbsIndex absT absF

muxEntries ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  W4.Pred sym ->
  ArrayEntry sym ctx tp ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
muxEntries sym p eT eF  = case (eT, eF) of
  (ArrayEntryArr fcondT aT, ArrayEntryArr fcondF aF) -> do
    a <- W4.baseTypeIte sym p aT aF
    return $ ArrayEntryArr (muxConditions sym p fcondT fcondF) a
  (ArrayEntryVal idxT condT vT, ArrayEntryVal idxF condF vF) -> do
    idx <- muxSymIndex sym p idxT idxF
    cond <- W4.baseTypeIte sym p condT condF
    a <- W4.baseTypeIte sym p vT vF
    return $ ArrayEntryVal idx cond a
  (ArrayEntryArr fcondT aT, ArrayEntryVal _ _ vF) -> do
    W4.BaseArrayRepr repr _ <- return $ W4.exprType aT
    aF <- W4.constantArray sym repr vF
    a <- W4.baseTypeIte sym p aT aF
    return $ ArrayEntryArr (muxConditions sym p fcondT (entryCond sym eF)) a
  (ArrayEntryVal _ _ vT, ArrayEntryArr fcondF aF) -> do    
    W4.BaseArrayRepr repr _ <- return $ W4.exprType aF
    aT <- W4.constantArray sym repr vT
    a <- W4.baseTypeIte sym p aT aF
    return $ ArrayEntryArr (muxConditions sym p (entryCond sym eT) fcondF) a    

freshIndex ::
  forall sym idx.
  W4.IsSymExprBuilder sym =>
  sym ->
  Maybe (AbsIndex idx) ->
  Ctx.Assignment W4.BaseTypeRepr idx ->
  IO (SymIndex sym idx, Ctx.Assignment (W4.BoundVar sym) idx)
freshIndex sym mabsIdx reprs = do
  vars <- FC.traverseFC (W4.freshBoundVar sym W4.emptySymbol) reprs
  let symIdx = SymIndex (FC.fmapFC (W4.varExpr sym) vars) mabsIdx
  return $ (symIdx, vars)


idxRepr ::
  W4.IsSymExprBuilder sym =>
  SymIndex sym ctx -> Ctx.Assignment W4.BaseTypeRepr ctx
idxRepr (SymIndex e _) = FC.fmapFC W4.exprType e

rangeRepr ::
  W4.IsSymExprBuilder sym =>
  SymRange sym ctx -> Ctx.Assignment W4.BaseTypeRepr ctx
rangeRepr (SymRangeSingle idx) = idxRepr idx
rangeRepr (SymRangeMulti idx _) = idxRepr idx

entryRepr ::
  W4.IsSymExprBuilder sym =>
  ArrayEntry sym ctx tp -> Ctx.Assignment W4.BaseTypeRepr ctx
entryRepr entry = case entry of
  ArrayEntryVal idx _ _ -> idxRepr idx
  ArrayEntryArr _ arr
    | W4.BaseArrayRepr repr _ <- W4.exprType arr -> repr
  _ -> error "impossible"

mergeEntries ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  ArrayEntry sym ctx tp ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
mergeEntries sym e1 e2 | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx = case (e1, e2) of
  (ArrayEntryVal symIdx cond v, _) -> mergeEntryVal sym symIdx cond v e1
  (_, ArrayEntryVal symIdx cond v) -> mergeEntryVal sym symIdx cond v e2
  (ArrayEntryArr fcond1 _, ArrayEntryArr fcond2 _) -> do
    (symIdx, vars) <- freshIndex sym Nothing (entryRepr e1)    
    let
      fcond symIdx' = do
        cond1 <- fcond1 symIdx'
        cond2 <- fcond2 symIdx'
        W4.orPred sym cond1 cond2

    (v1, cond1) <- readEntry sym symIdx e1
    (v2, _) <- readEntry sym symIdx e2
    body <- W4.baseTypeIte sym cond1 v1 v2
    fn <- W4.definedFn sym (W4.safeSymbol "mergeEntries") vars body W4.AlwaysUnfold
    a <- W4.arrayFromFn sym fn
    return $ ArrayEntryArr fcond a


mergeEntryVal ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  SymIndex sym ctx ->
  W4.Pred sym ->
  W4.SymExpr sym tp ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
mergeEntryVal sym symIdx cond1 v1 e2 = do
  (v2, cond2) <- readEntry sym symIdx e2
  cond <- W4.orPred sym cond1 cond2
  e <- W4.baseTypeIte sym cond1 v1 v2
  return $ ArrayEntryVal symIdx cond e
