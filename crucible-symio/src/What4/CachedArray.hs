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
{-# LANGUAGE UndecidableInstances #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module What4.CachedArray
  (
    CachedArray
  , ArrayChunk
  , mkArrayChunk
  , evalChunk
  , writeChunk
  , writeSingle
  , readSingle
  , readChunk
  , arrayToChunk
  , chunkToArray
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
import qualified Data.IORef as IO

import           Data.Parameterized.Some
import qualified Data.Parameterized.Nonce as N
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

import qualified Data.Parameterized.IntervalsMap as IM
import           Data.Parameterized.IntervalsMap ( AsOrd(..) )

------------------------------------------------
-- Interface

-- TODO: add coalescing function for merging adjacent entries

newtype ArrayChunk sym idx tp =
  ArrayChunk { evalChunk :: (W4.SymExpr sym idx -> IO (W4.SymExpr sym tp)) }

mkArrayChunk ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  (W4.SymExpr sym idx -> IO (W4.SymExpr sym tp)) ->
  IO (ArrayChunk sym idx tp)
mkArrayChunk _sym f = do
  ref <- IO.newIORef Map.empty
  let f' idx = do
        m <- IO.readIORef ref
        case Map.lookup (AsOrd idx) m of
          Just v -> return v
          Nothing -> do
            v <- f idx
            IO.modifyIORef ref (Map.insert (AsOrd idx) v)
            return v
  return $ ArrayChunk f'

writeChunk ::
  forall sym ctx tp.
  NonEmptyCtx ctx =>
  W4.IsSymExprBuilder sym =>
  sym ->
  -- | base address to write to
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  -- | size of write 
  W4.SymExpr sym (CtxFirst ctx) ->
  -- | symbolic value to write
  ArrayChunk sym (CtxFirst ctx) tp ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
writeChunk sym loExpr offExpr chunk arr | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx =
  arrConstraints arr $ do
  rng <- mkSymRangeOff sym loExpr offExpr
  arr' <- invalidateEntries sym rng arr
  -- offset the incoming function so that its value at zero becomes the value at
  -- the base address
  let
    off = indexToOffset $ symRangeLo rng
    vals :: SymIndex sym ctx -> IO (W4.PartExpr (W4.Pred sym) (W4.SymExpr sym tp))
    vals idx' = do
        p <- isInRange sym rng idx'
        (SymOffset idxOffsetExpr) <- indexToOffset <$> subSymOffset sym idx' off
        v <- evalChunk chunk idxOffsetExpr
        return $ W4.mkPE p v
  entry <- mkMultiEntry sym vals
  arr'' <- IM.insertWithM (mergeEntriesMux sym (isInRange sym rng)) (symRangeToAbs rng) (toPMuxTree sym entry)  (arrMap arr')
  incNonce sym $ arr { arrMap = arr''}


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
  entry <- mkValEntry sym symIdx val
  
  arr'' <- IM.insertWithM (mergeEntriesMux sym (isEqIndex sym symIdx)) (symIdxToAbs symIdx) (toPMuxTree sym entry)  (arrMap arr')
  incNonce sym $ arr { arrMap = arr'' }
  where
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

readChunk ::
  forall sym ctx tp.
  NonEmptyCtx ctx =>
  W4.IsSymExprBuilder sym =>
  sym ->
  -- | base address to read from
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  -- | size of read 
  W4.SymExpr sym (CtxFirst ctx) ->  
  CachedArray sym ctx tp ->
  IO (ArrayChunk sym (CtxFirst ctx) tp)
readChunk sym loExpr offExpr arr | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx = do
  rng <- mkSymRangeOff sym loExpr offExpr
  let absIdx = symRangeToAbs rng
  -- offset the outgoing array so that its value at zero is the value at
  -- the base address
  return $ ArrayChunk $ \idxExpr -> do
    let off = SymOffset idxExpr
    offsetIdx <- addSymOffset sym (symRangeLo rng) off
    readArrayBase sym (offsetIdx { symIdxAbs = Just absIdx}) arr

chunkToArray ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  W4.BaseTypeRepr idx ->
  ArrayChunk sym idx tp ->
  IO (W4.SymArray sym (Ctx.EmptyCtx Ctx.::> idx) tp)
chunkToArray sym repr chunk = do
  var <- W4.freshBoundVar sym W4.emptySymbol repr
  body <- evalChunk chunk (W4.varExpr sym var)
  fn <- W4.definedFn sym (W4.safeSymbol "readRange") (Ctx.empty Ctx.:> var) body W4.AlwaysUnfold
  W4.arrayFromFn sym fn

arrayToChunk ::
  forall sym idx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  (W4.SymArray sym (Ctx.EmptyCtx Ctx.::> idx) tp) ->
  IO (ArrayChunk sym idx tp)
arrayToChunk sym arr = mkArrayChunk sym $ \idx -> W4.arrayLookup sym arr (Ctx.empty Ctx.:> idx)


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
    notp <- W4.notPred sym p
    arr' <- IM.mergeWithM
              (pmuxTreeAddCondition sym p)
              (pmuxTreeAddCondition sym notp)
              (muxEntries sym p)
              (arrMap arr1)
              (arrMap arr2)
    incNonce sym $ arr1 { arrMap = arr' }

-- | Initialize an array with symbolic contents at concrete locations
initArrayConcrete ::
  forall sym idx tp idx' tp'.
  W4.IsSymExprBuilder sym =>
  idx ~ (idx' Ctx.::> tp') =>
  sym ->
  W4.BaseTypeRepr tp ->
  [(Ctx.Assignment W4.ConcreteVal idx, W4.SymExpr sym tp)] ->
  IO (CachedArray sym idx tp)
initArrayConcrete sym repr m = do
  nonce <- freshArrayNonce sym
  im <- IM.fromList <$> mapM go m
  return $ CachedArray im id repr nonce
  where
    go ::
      (Ctx.Assignment W4.ConcreteVal idx, W4.SymExpr sym tp) ->
      IO (AbsIndex idx, PMuxTree sym (ArrayEntry sym idx tp))
    go (cidx, v) = do
      symIdx <- concreteIdxToSym sym cidx
      entry <- mkValEntry sym symIdx v
      return $ (symIdxToAbs symIdx, toPMuxTree sym entry)

-- | Initialize an array with symbolic contents at symbolic locations
initArray ::
  forall sym idx tp idx' tp'.
  W4.IsSymExprBuilder sym =>
  idx ~ (idx' Ctx.::> tp') =>
  sym ->
  W4.BaseTypeRepr tp ->
  [(Ctx.Assignment (W4.SymExpr sym) idx, W4.SymExpr sym tp)] ->
  IO (CachedArray sym idx tp)
initArray sym repr m = do
  nonce <- freshArrayNonce sym
  im <- IM.fromList <$> mapM go m
  return $ CachedArray im id repr nonce
  where
    go ::
      (Ctx.Assignment (W4.SymExpr sym) idx, W4.SymExpr sym tp) ->
      IO (AbsIndex idx, PMuxTree sym (ArrayEntry sym idx tp))
    go (symIdxExpr, v) = do
      let
        symIdx = SymIndex symIdxExpr Nothing
      entry <- mkValEntry sym symIdx v
      return $ (symIdxToAbs symIdx, toPMuxTree sym entry)

---------------------------------------------------
-- Implementation

-- | A sentinel integer that is refreshed every time the array is updated.
-- Effectively we are just using its internal nonce, but
-- without the need for introducing a new type parameter for a fresh nonce generator.
newtype ArrayNonce sym = ArrayNonce (W4.SymInteger sym)

instance TestEquality (W4.SymExpr sym) => Eq (ArrayNonce sym) where
  (ArrayNonce i1) == (ArrayNonce i2) | Just Refl <- testEquality i1 i2 = True
  _ == _ = False

instance OrdF (W4.SymExpr sym) => Ord (ArrayNonce sym) where
  compare (ArrayNonce i1) (ArrayNonce i2) = toOrdering $ compareF i1 i2

freshArrayNonce ::
  W4.IsSymExprBuilder sym =>
  sym ->
  IO (ArrayNonce sym)
freshArrayNonce sym = ArrayNonce <$> W4.freshConstant sym W4.emptySymbol W4.BaseIntegerRepr

data CachedArray sym (ctx :: Ctx.Ctx W4.BaseType) (tp :: W4.BaseType) where
  CachedArray ::
    {
      arrMap :: IM.IntervalsMap AbsIntervalEnd ctx (PMuxTree sym (ArrayEntry sym ctx tp))
    , arrConstraints :: forall a. (NonEmptyCtx ctx => a) -> a
    , arrTypeRepr :: W4.BaseTypeRepr tp
    , _arrNonce :: ArrayNonce sym
    } -> CachedArray sym ctx tp

instance TestEquality (W4.SymExpr sym) => Eq (CachedArray sym idx tp) where
  (CachedArray _ _ _ nonce1) == (CachedArray _ _ _ nonce2) = nonce1 == nonce2

incNonce ::
  W4.IsSymExprBuilder sym =>
  sym ->
  CachedArray sym idx tp ->
  IO (CachedArray sym idx tp)
incNonce sym (CachedArray am ac tr _) = do
  nonce <- freshArrayNonce sym
  return $ CachedArray am ac tr nonce

-- | An array entry defines a set of possible values for a given
-- abstract domain. Entries may overlap, and so as an invariant we
-- preserve the fact that at each logical index, exactly one entry is valid
data ArrayEntry sym ctx tp where
  ArrayEntry ::
    { -- TODO: should we cache these results?
      entryVals :: (SymIndex sym ctx -> IO (W4.PartExpr (W4.Pred sym) (W4.SymExpr sym tp)))
    , entryNonce :: ArrayNonce sym
    } -> ArrayEntry sym ctx tp


incNonceEntry ::
  W4.IsSymExprBuilder sym =>
  sym ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
incNonceEntry sym (ArrayEntry vals _) = do
  nonce <- freshArrayNonce sym
  return $ ArrayEntry vals nonce

instance TestEquality (W4.SymExpr sym) => Eq (ArrayEntry sym ctx tp) where
  e1 == e2 = entryNonce e1 == entryNonce e2

instance OrdF (W4.SymExpr sym) => Ord (ArrayEntry sym ctx tp) where
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
  SymOffset :: W4.SymExpr sym (CtxFirst ctx) -> SymOffset sym ctx

data FirstIndex ctx where
  FirstIndex :: Ctx.Index ctx (CtxFirst ctx) -> FirstIndex ctx

skipFirst ::
  FirstIndex (ctx Ctx.::> tp1) -> FirstIndex (ctx Ctx.::> tp1 Ctx.::> tp2)
skipFirst (FirstIndex idx) = FirstIndex (Ctx.skipIndex idx)

firstIndex ::
  forall ctx.
  NonEmptyCtx ctx =>
  Ctx.Size ctx ->
  FirstIndex ctx
firstIndex sz | NonEmptyCtxRepr <- nonEmptyCtxRepr @_ @ctx =
  case Ctx.viewSize (Ctx.decSize sz) of
    Ctx.ZeroSize -> FirstIndex (Ctx.baseIndex)
    Ctx.IncSize _ -> skipFirst (firstIndex (Ctx.decSize sz))

indexToOffset ::
  forall sym ctx.
  NonEmptyCtx ctx =>
  W4.IsSymExprBuilder sym =>
  SymIndex sym ctx ->
  SymOffset sym ctx
indexToOffset (SymIndex eCtx _) =
  let
    FirstIndex idx = firstIndex (Ctx.size eCtx)
    e = eCtx Ctx.! idx
  in SymOffset e

addSymOffset ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  SymIndex sym ctx ->
  SymOffset sym ctx ->
  IO (SymIndex sym ctx)
addSymOffset sym (SymIndex eCtx _) (SymOffset off) = do
  let
    FirstIndex idx = firstIndex (Ctx.size eCtx)
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
  NonEmptyCtx ctx =>
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
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  W4.SymExpr sym (CtxFirst ctx) ->
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

type family CtxFirst (ctx :: Ctx.Ctx k) where
  CtxFirst (Ctx.EmptyCtx Ctx.::> a) = a
  CtxFirst (ctx Ctx.::> _) = CtxFirst ctx

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


data AbsIntervalEnd tp where
  AbsIntervalEndInt :: W4.ValueBound Integer -> AbsIntervalEnd W4.BaseIntegerType
  AbsIntervalEndBV :: (1 <= w) => W4.NatRepr w -> W4.ValueBound Integer -> AbsIntervalEnd (W4.BaseBVType w)

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


type AbsIndex (idx :: Ctx.Ctx W4.BaseType) = IM.Intervals AbsIntervalEnd idx
type AbsInterval tp = IM.IntervalF AbsIntervalEnd tp


bvDomainRange ::
  1 <= w =>
  W4.NatRepr w ->
  BVD.BVDomain w ->
  AbsInterval (W4.BaseBVType w)
bvDomainRange w d = case BVD.ubounds d of
  (i1, i2) -> IM.mkIntervalF $ IM.ClosedInterval (AbsIntervalEndBV w (W4.Inclusive i1)) (AbsIntervalEndBV w (W4.Inclusive i2))

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
  W4.BaseIntegerRepr -> case v of
    W4.SingleRange x -> IM.mkIntervalF $ IM.ClosedInterval (AbsIntervalEndInt (W4.Inclusive x)) (AbsIntervalEndInt (W4.Inclusive x))
    W4.MultiRange lo hi -> IM.mkIntervalF $ IM.ClosedInterval (AbsIntervalEndInt lo) (AbsIntervalEndInt hi)
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
    intersecting = IM.toList $ IM.intersecting (arrMap arr) (symIdxToAbs symIdx)
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
  SymIndex sym ctx ->
  W4.SymExpr sym tp ->
  IO (ArrayEntry sym ctx tp)
mkValEntry sym idx v = do
  let vals idx' = do
        p <- isEqIndex sym idx idx'
        return $ W4.mkPE p v
  mkMultiEntry sym vals

mkMultiEntry ::
  W4.IsSymExprBuilder sym =>
  sym ->
  (SymIndex sym ctx -> IO (W4.PartExpr (W4.Pred sym) (W4.SymExpr sym tp))) ->
  IO (ArrayEntry sym ctx tp)
mkMultiEntry sym vals = do
  nonce <- freshArrayNonce sym
  return $ ArrayEntry vals nonce

symIdxToAbs ::
  forall sym ctx.
  W4.IsSymExprBuilder sym =>
  SymIndex sym ctx -> AbsIndex ctx
symIdxToAbs (SymIndex symIdxExpr Nothing) = IM.Intervals $ FC.fmapFC (exprToAbsInterval @sym) symIdxExpr
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
  sym ->
  -- | range to invalidate
  SymRange sym ctx ->
  ArrayEntry sym ctx tp ->
  IO (Maybe (ArrayEntry sym ctx tp))
invalidateRange sym invalid_rng entry = do
  let vals symIdx' = do
        notThis <- W4.notPred sym =<< isInRange sym invalid_rng symIdx'
        val <- entryVals entry symIdx'
        W4.runPartialT sym notThis $ W4.returnPartial val
  entry' <- incNonceEntry sym $ entry { entryVals = vals }
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

-- | Invalidate all existing symbolic entries at exactly this index
invalidateEntries ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  sym ->
  SymRange sym ctx ->
  CachedArray sym ctx tp ->
  IO (CachedArray sym ctx tp)
invalidateEntries sym symRange arr = arrConstraints arr $ do
  NonEmptyCtxRepr <- return $ nonEmptyCtxRepr @_ @ctx
  cmap <- IM.mapMIntersecting absIndex (\v -> getMaybe <$> pmuxTreeMaybeOp sym (invalidateRange sym symRange) v) (arrMap arr)
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
joinAbsIndex (IM.Intervals idx1) (IM.Intervals idx2) = IM.Intervals $ Ctx.zipWith IM.mergeIntervalsF idx1 idx2


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
  NonEmptyCtx ctx =>
  sym ->
  (SymIndex sym ctx -> IO (W4.Pred sym)) ->
  ArrayEntry sym ctx tp ->
  ArrayEntry sym ctx tp ->
  IO (ArrayEntry sym ctx tp)
mergeEntries sym pickLeftFn e1 e2 = do
  let vals symIdx' = do
        pickLeft <- pickLeftFn symIdx'
        val1 <- entryVals e1 symIdx'
        val2 <- entryVals e2 symIdx'
        W4.mergePartial sym (\p a b -> lift $ W4.baseTypeIte sym p a b)
          pickLeft val1 val2
  incNonceEntry sym $ e1 { entryVals = vals }

mergeEntriesMux ::
  forall sym ctx tp.
  W4.IsSymExprBuilder sym =>
  NonEmptyCtx ctx =>
  sym ->
  (SymIndex sym ctx -> IO (W4.Pred sym)) ->
  PMuxTree sym (ArrayEntry sym ctx tp) ->
  PMuxTree sym (ArrayEntry sym ctx tp) ->
  IO (PMuxTree sym (ArrayEntry sym ctx tp))
mergeEntriesMux sym pickLeftFn = pmuxTreeBinOp sym (mergeEntries sym pickLeftFn)

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

pmuxTreeAddCondition ::
  forall sym a.
  W4.IsExprBuilder sym =>
  Ord a =>
  sym ->
  W4.Pred sym ->
  PMuxTree sym a ->
  IO (PMuxTree sym a)
pmuxTreeAddCondition sym cond mt = mkPMuxTree sym =<< mapM addCond (viewPMuxTree mt)
  where
    addCond :: (a, W4.Pred sym) -> IO (a, W4.Pred sym)
    addCond (a, cond') = do
      cond'' <- W4.andPred sym cond cond'
      return $ (a, cond'')


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
