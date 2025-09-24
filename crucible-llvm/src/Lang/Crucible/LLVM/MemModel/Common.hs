-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.MemModel.Common
-- Description      : Core definitions of the symbolic C memory model
-- Copyright        : (c) Galois, Inc 2011-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Lang.Crucible.LLVM.MemModel.Common
  ( -- * Range declarations.
    Range(..)

    -- * Pointer declarations
  , OffsetExpr(..)
  , IntExpr(..)
  , Cond(..)

  , Mux(..)

  , ValueCtor(..)

  , BasePreference(..)

  , RangeLoad(..)
  , rangeLoad
  , fixedOffsetRangeLoad
  , fixedSizeRangeLoad
  , symbolicRangeLoad
  , symbolicUnboundedRangeLoad

  , ValueView(..)

  , ValueLoad(..)
  , valueLoad
  , LinearLoadStoreOffsetDiff(..)
  , symbolicValueLoad
  , loadBitvector

  , memsetValue
  , loadTypedValueFromBytes
  ) where

import Control.Exception (assert)
import Control.Lens
import Control.Monad (guard)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as V
import Numeric.Natural

import Lang.Crucible.Panic ( panic )
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.MemModel.Type

-- | @R i j@ denotes that the write should store in range [i..j).
data Range = R { rStart :: Addr, _rEnd :: Addr }
  deriving (Eq, Show)

-- Value

data OffsetExpr
  = OffsetAdd OffsetExpr IntExpr
  | Load
  | Store
  deriving (Show)

data IntExpr
  = OffsetDiff OffsetExpr OffsetExpr
  | IntAdd IntExpr IntExpr
  | CValue Bytes
  | StoreSize
  deriving (Show)

data Cond
  = OffsetEq OffsetExpr OffsetExpr
  | OffsetLe OffsetExpr OffsetExpr
  | IntEq IntExpr IntExpr
  | IntLe IntExpr IntExpr
  | And Cond Cond
  | Or Cond Cond
  deriving (Show)

(.==) :: OffsetExpr -> OffsetExpr -> Cond
infix 4 .==
x .== y = OffsetEq x y

(.<=) :: OffsetExpr -> OffsetExpr -> Cond
infix 4 .<=
x .<= y = OffsetLe x y

infixl 6 .+
(.+) :: OffsetExpr -> IntExpr -> OffsetExpr
x .+ CValue 0 = x
x .+ y = OffsetAdd x y

infixl 6 .-
(.-) :: OffsetExpr -> OffsetExpr -> IntExpr
x .- y = OffsetDiff x y

-- Muxs

data Mux a
  = Mux Cond (Mux a) (Mux a)
  | MuxTable OffsetExpr OffsetExpr (Map Bytes (Mux a)) (Mux a)
    -- ^ 'MuxTable' encodes a lookup table: @'MuxTable' p1 p2
    -- 'Map.empty' z@ is equivalent to @z@, and @'MuxTable' p1 p2
    -- ('Map.insert' (i, x) m) z@ is equivalent to @'Mux' (p1 '.+'
    -- 'CValue' i '.==' p2) x ('MuxTable' p1 p2 m z)@.
  | MuxVar a
  deriving Show

-- Variable for mem model.

loadOffset :: Bytes -> OffsetExpr
loadOffset n = Load .+ CValue n

storeOffset :: Bytes -> OffsetExpr
storeOffset n = Store .+ CValue n

storeEnd :: OffsetExpr
storeEnd = Store .+ StoreSize

-- | @loadInStoreRange n@ returns predicate if Store <= Load && Load <= Store + n
loadInStoreRange :: Bytes -> Cond
loadInStoreRange (Bytes 0) = Load .== Store
loadInStoreRange n = And (Store .<= Load)
                         (Load .<= Store .+ CValue n)

-- Value constructor

-- | Describes how to construct a larger LLVM value as a combination
-- of smaller components.
data ValueCtor a
  = ValueCtorVar a
    -- | Concatenates two bitvectors.
    -- The first bitvector contains values stored at the low-address bytes
    -- while the second contains values at the high-address bytes. Thus, the
    -- meaning of this depends on the endianness of the target architecture.
  | ConcatBV (ValueCtor a) (ValueCtor a)
  | BVToFloat (ValueCtor a)
  | BVToDouble (ValueCtor a)
  | BVToX86_FP80 (ValueCtor a)
    -- | Cons one value to beginning of array.
  | ConsArray (ValueCtor a) (ValueCtor a)
  | AppendArray (ValueCtor a) (ValueCtor a)
  | MkArray StorageType (Vector (ValueCtor a))
  | MkStruct (Vector (Field StorageType, ValueCtor a))
  deriving (Functor, Foldable, Traversable, Show)

concatBV :: Bytes -> ValueCtor a -> Bytes -> ValueCtor a -> ValueCtor a
concatBV _xw x _yw y = ConcatBV x y

singletonArray :: StorageType -> ValueCtor a -> ValueCtor a
singletonArray tp e = MkArray tp (V.singleton e)

-- | Create value of type that splits at a particular byte offset.
splitTypeValue :: StorageType   -- ^ Type of value to create
               -> Offset -- ^ Bytes offset to slice type at.
               -> (Offset -> StorageType -> ValueCtor a) -- ^ Function for subtypes.
               -> ValueCtor a
splitTypeValue tp d subFn = assert (d > 0) $
  case storageTypeF tp of
    Bitvector sz -> assert (d < sz) $
      concatBV d (subFn 0 (bitvectorType d))
               (sz - d) (subFn d (bitvectorType (sz - d)))
    Float -> BVToFloat (subFn 0 (bitvectorType 4))
    Double -> BVToDouble (subFn 0 (bitvectorType 8))
    X86_FP80 -> BVToX86_FP80 (subFn 0 (bitvectorType 10))
    Array n0 etp -> assert (n0 > 0) $ do
      let esz = storageTypeSize etp
      let (c,part) = assert (esz > 0) $ toInteger d `divMod` toInteger esz
      let n = toInteger n0 - toInteger c
      let o = d - toBytes part -- (Bytes c) * esz
      let consPartial
            | n < 0 = panic "splitTypeValue" ["Unexpected array size: " ++ show n, show tp, show d]
            | part == 0 = subFn o (arrayType (fromInteger n) etp)
            | n > 1 =
                ConsArray (subFn o etp)
                          (subFn (o+esz) (arrayType (fromInteger (n-1)) etp))
            | otherwise = assert (n == 1) $
                singletonArray etp (subFn o etp)
      let result
            | c > 0 = assert (c < toInteger n0) $
              AppendArray (subFn 0 (arrayType (fromInteger c) etp))
                          consPartial
            | otherwise = consPartial
      result
    Struct flds -> MkStruct (fldFn <$> flds)
      where fldFn fld = (fld, subFn (fieldOffset fld) (fld^.fieldVal))

-- | This is used so that when we are comparing symbolic loads against
-- previous stores, we can represent the difference as relative to
-- a fixed address whenever possible.
data BasePreference
   = FixedLoad
   | FixedStore
   | NeitherFixed
  deriving (Eq, Show)

-- RangeLoad

-- | A 'RangeLoad' describes different kinds of memory loads in the
-- context of a byte range copied into an old memory.
data RangeLoad a b
  = OutOfRange a StorageType
    -- ^ Load from an address range disjoint from the copied bytes.
    -- The arguments represent the address and type of the load.
  | InRange b StorageType
    -- ^ Load consists of bytes within the copied range. The first
    -- argument represents the offset relative to the start of the
    -- copied bytes.
  deriving (Show)

adjustOffset :: (b -> d)
             -> (a -> c)
             -> RangeLoad a b -> RangeLoad c d
adjustOffset _ outFn (OutOfRange a tp) = OutOfRange (outFn a) tp
adjustOffset inFn _  (InRange b tp) = InRange (inFn b) tp

-- | Decomposes a single load after a memcopy into a combination of
-- simple value loads.
rangeLoad ::
  Addr  {- ^ load offset  -} ->
  StorageType {- ^ load type    -} ->
  Range {- ^ copied range -} ->
  ValueCtor (RangeLoad Addr Addr)
rangeLoad lo ltp s@(R so se)
   | so == se  = loadFail
   | le <= so  = loadFail
   | se <= lo  = loadFail
   | lo < so   = splitTypeValue ltp (so - lo) (\o tp -> rangeLoad (lo+o) tp s)
   | se < le   = splitTypeValue ltp (se - lo) (\o tp -> rangeLoad (lo+o) tp s)
   | otherwise = assert (so <= lo && le <= se) $ ValueCtorVar (InRange (lo - so) ltp)
 where le = typeEnd lo ltp
       loadFail = ValueCtorVar (OutOfRange lo ltp)

-- | Produces a @Mux ValueCtor@ expression representing the range load conditions
-- when the load and store offsets are concrete and the store size is bounded
fixedOffsetRangeLoad :: Addr
                     -- ^ Address of load
                     -> StorageType
                     -- ^ Type to load
                     -> Addr
                     -- ^ Address of store
                     -> Mux (ValueCtor (RangeLoad Addr Addr))
fixedOffsetRangeLoad l tp s
  | s < l = do -- Store is before load.
    let sd = l - s -- Number of bytes load comes after store
    Mux (IntLe StoreSize (CValue sd)) loadFail (loadCase (sd+1))
  | le <= s = loadFail -- No load if load ends before write.
  | otherwise = loadCase 0
  where
    le = typeEnd l tp
    loadCase i
      | i < le-s  = Mux (IntEq StoreSize (CValue i)) (loadVal i) (loadCase (i+1))
      | otherwise = loadVal i
    loadVal ssz = MuxVar (rangeLoad l tp (R s (s+ssz)))
    loadFail = MuxVar (ValueCtorVar (OutOfRange l tp))

-- | @fixLoadBeforeStoreOffset pref i k@ adjusts a pointer value that is relative
-- the load address into a global pointer.  The code assumes that @load + i == store@.
fixLoadBeforeStoreOffset :: BasePreference -> Offset -> Offset -> OffsetExpr
fixLoadBeforeStoreOffset pref i k
  | pref == FixedStore = Store .+ CValue (k - i)
  | otherwise = Load .+ CValue k

-- | @fixLoadAfterStoreOffset pref i k@ adjusts a pointer value that is relative
-- the load address into a global pointer.  The code assumes that @load == store + i@.
fixLoadAfterStoreOffset :: BasePreference -> Offset -> Offset -> OffsetExpr
fixLoadAfterStoreOffset pref i k = assert (k >= i) $
  case pref of
    FixedStore -> Store .+ CValue k
    _          -> Load  .+ CValue (k - i)

-- | @loadFromStoreStart pref tp i j@ loads a value of type @tp@ from a range under the
-- assumptions that @load + i == store@ and @j = i + min(StoreSize, typeEnd(tp)@.
loadFromStoreStart :: BasePreference
                   -> StorageType
                   -> Offset
                   -> Offset
                   -> ValueCtor (RangeLoad OffsetExpr IntExpr)
loadFromStoreStart pref tp i j = adjustOffset inFn outFn <$> rangeLoad 0 tp (R i j)
  where inFn = CValue
        outFn = fixLoadBeforeStoreOffset pref i

-- | Produces a @Mux ValueCtor@ expression representing the range load conditions
-- when the load and store values are concrete
fixedSizeRangeLoad :: BasePreference -- ^ Whether addresses are based on store or load.
                   -> StorageType
                   -> Bytes
                   -> Mux (ValueCtor (RangeLoad OffsetExpr IntExpr))
fixedSizeRangeLoad _ tp 0 = MuxVar (ValueCtorVar (OutOfRange Load tp))
fixedSizeRangeLoad pref tp ssz =
  Mux (loadOffset lsz .<= Store) loadFail (prefixL lsz)
  where
    lsz = typeEnd 0 tp

    prefixL i
      | i > 0 = Mux (loadOffset i .== Store) (loadVal i) (prefixL (i-1))
      -- Special case where we skip some offsets, it it won't
      -- make more splitting
      | lsz <= ssz && pref == NeitherFixed =
        -- Load is contained in storage.
        Mux (loadInStoreRange (ssz-lsz)) loadSucc $
        -- Load extends past end of storage
        suffixS (ssz-lsz)
      | otherwise = suffixS 0

    suffixS i
      | i < ssz   = Mux (Load .== storeOffset i) (storeVal i) (suffixS (i+1))
      | otherwise = loadFail

    loadVal i = MuxVar (loadFromStoreStart pref tp i (i+ssz))

    storeVal i = MuxVar (adjustOffset inFn outFn <$> rangeLoad i tp (R 0 ssz))
      where inFn = CValue
            outFn = fixLoadAfterStoreOffset pref i

    loadSucc = MuxVar (ValueCtorVar (InRange (Load .- Store) tp))
    loadFail = MuxVar (ValueCtorVar (OutOfRange Load tp))

-- | Produces a @Mux ValueCtor@ expression representing the range load conditions
-- when the load and store values are symbolic and the @StoreSize@ is bounded.
symbolicRangeLoad :: BasePreference -> StorageType -> Mux (ValueCtor (RangeLoad OffsetExpr IntExpr))
symbolicRangeLoad pref tp =
  Mux (Store .<= Load)
  (Mux (loadOffset sz .<= storeEnd) (loadVal0 sz) (loadIter0 (sz-1)))
  (storeAfterLoad 1)
  where
    sz = typeEnd 0 tp

    loadIter0 j
      | j > 0     = Mux (loadOffset j .== storeEnd) (loadVal0 j) (loadIter0 (j-1))
      | otherwise = loadFail

    loadVal0 j = MuxVar $ adjustOffset inFn outFn <$> rangeLoad 0 tp (R 0 j)
      where inFn k  = IntAdd (OffsetDiff Load Store) (CValue k)
            outFn k = OffsetAdd Load (CValue k)

    storeAfterLoad i
      | i < sz = Mux (loadOffset i .== Store) (loadFromOffset i) (storeAfterLoad (i+1))
      | otherwise = loadFail

    loadFromOffset i =
      assert (0 < i && i < sz) $
      Mux (IntLe (CValue (sz - i)) StoreSize) (loadVal i (i+sz)) (f (sz-1))
      where f j | j > i = Mux (IntEq (CValue (j-i)) StoreSize) (loadVal i j) (f (j-1))
                | otherwise = loadFail

    loadVal i j = MuxVar (loadFromStoreStart pref tp i j)
    loadFail = MuxVar (ValueCtorVar (OutOfRange Load tp))

-- | Produces a @Mux ValueCtor@ expression representing the RangeLoad conditions
-- when the load and store values are symbolic and the @StoreSize@ is unbounded.
symbolicUnboundedRangeLoad :: BasePreference -> StorageType -> Mux (ValueCtor (RangeLoad OffsetExpr IntExpr))
symbolicUnboundedRangeLoad pref tp =
  Mux (Store .<= Load)
  (loadVal0 sz)
  (storeAfterLoad 1)
  where
    sz = typeEnd 0 tp

    loadVal0 j = MuxVar $ adjustOffset inFn outFn <$> rangeLoad 0 tp (R 0 j)
      where inFn k  = IntAdd (OffsetDiff Load Store) (CValue k)
            outFn k = OffsetAdd Load (CValue k)

    storeAfterLoad i
      | i < sz = Mux (loadOffset i .== Store) (loadFromOffset i) (storeAfterLoad (i+1))
      | otherwise = loadFail

    loadFromOffset i =
      assert (0 < i && i < sz) $
      Mux (IntLe (CValue (sz - i)) StoreSize) (loadVal i (i+sz)) (f (sz-1))
      where f j | j > i = Mux (IntEq (CValue (j-i)) StoreSize) (loadVal i j) (f (j-1))
                | otherwise = loadFail

    loadVal i j = MuxVar (loadFromStoreStart pref tp i j)
    loadFail = MuxVar (ValueCtorVar (OutOfRange Load tp))

-- ValueView

-- | Represents a projection of a sub-component out of a larger LLVM value.
data ValueView
  = ValueViewVar StorageType
    -- | Select low-address bytes in the bitvector.
    -- The sizes include the number of low bytes, and the number of high bytes.
  | SelectPrefixBV Bytes Bytes ValueView
    -- | Select the given number of high-address bytes in the bitvector.
    -- The sizes include the number of low bytes, and the number of high bytes.
  | SelectSuffixBV Bytes Bytes ValueView
  | FloatToBV ValueView
  | DoubleToBV ValueView
  | X86_FP80ToBV ValueView
  | ArrayElt Natural StorageType Natural ValueView

  | FieldVal (Vector (Field StorageType)) Int ValueView
  deriving (Show, Eq, Ord)

viewType :: ValueView -> Maybe StorageType
viewType (ValueViewVar tp) = Just tp
viewType (SelectPrefixBV u v vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (Bitvector (u + v) == tp)
     pure $ bitvectorType u
viewType (SelectSuffixBV u v vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (Bitvector (u + v) == tp)
     pure $ bitvectorType v
viewType (FloatToBV vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (Float == tp)
     pure $ bitvectorType 4
viewType (DoubleToBV vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (Double == tp)
     pure $ bitvectorType 8
viewType (X86_FP80ToBV vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (X86_FP80 == tp)
     pure $ bitvectorType 10
viewType (ArrayElt n etp i vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (i < n && Array n etp == tp)
     pure $ etp
viewType (FieldVal v i vv) =
  do tp <- storageTypeF <$> viewType vv
     guard (Struct v == tp)
     view fieldVal <$> (v V.!? i)

-- | A 'ValueLoad' describes different kinds of memory loads in the
-- context of a new value stored into an old memory.
data ValueLoad v
  = OldMemory v StorageType
    -- ^ Load from an address range disjoint from the stored value.
    -- The arguments represent the address and type of the load.
  | LastStore ValueView
    -- ^ Load consists of valid bytes within the stored value.
  | InvalidMemory StorageType
    -- ^ Load touches invalid memory. Currently, this can only arise when
    -- trying to read struct padding bytes as a bitvector.
  deriving (Functor,Show)

loadBitvector :: Addr -> Bytes -> Addr -> ValueView -> ValueCtor (ValueLoad Addr)
loadBitvector lo lw so v = do
  let le = lo + lw
  let ltp = bitvectorType lw
  let stp = fromMaybe (error ("loadBitvector given bad view " ++ show v)) (viewType v)
  let retValue eo v' = (sz', valueLoad lo' (bitvectorType sz') eo v')
        where etp = fromMaybe (error ("Bad view " ++ show v')) (viewType v')
              esz = storageTypeSize etp
              lo' = max lo eo
              sz' = min le (eo+esz) - lo'
  case storageTypeF stp of
    Bitvector sw
      | so < lo -> do
        -- Number of bytes to drop.
        let d = lo - so
        -- Store is before load.
        valueLoad lo ltp lo (SelectSuffixBV d (sw - d) v)
      | otherwise -> assert (lo == so && lw < sw) $
        -- Load ends before store ends.
        valueLoad lo ltp so (SelectPrefixBV lw (sw - lw) v)
    Float -> valueLoad lo ltp so (FloatToBV v)
    Double -> valueLoad lo ltp so (DoubleToBV v)
    X86_FP80 -> valueLoad lo ltp so (X86_FP80ToBV v)
    Array n tp -> snd $ foldl1 cv (val <$> r)
      where cv (wx,x) (wy,y) = (wx + wy, concatBV wx x wy y)
            esz = storageTypeSize tp
            c0 = assert (esz > 0) $ toInteger (lo - so) `div` toInteger esz
            (c1, p1) = toInteger (le - so) `divMod` toInteger esz
            -- Get range of indices to read.
            r | p1 == 0 = assert (c1 > c0) [c0..c1-1]
              | otherwise = assert (c1 >= c0) [c0..c1]
            val i
              | i >= 0 = retValue (so + natBytesMul (fromInteger i) esz) (ArrayElt n tp (fromInteger i) v)
              | otherwise = panic "loadBitvector" ["Bad array index", show i, show (lo, lw, so, v)]
    Struct sflds -> assert (not (null r)) $ snd $ foldl1 cv r
      where cv (wx,x) (wy,y) = (wx+wy, concatBV wx x wy y)
            r = concat (zipWith val [0..] (V.toList sflds))
            val i f = v1
              where eo = so + fieldOffset f
                    ee = eo + storageTypeSize (f^.fieldVal)
                    v1 | le <= eo = v2
                       | ee <= lo = v2
                       | otherwise = retValue eo (FieldVal sflds i v) : v2
                    v2 | fieldPad f == 0 = []   -- Return no padding.
                       | le <= ee = [] -- Nothing of load ends before padding.
                         -- Nothing if padding ends before load begins.
                       | ee+fieldPad f <= lo = []
                       | otherwise = [(p, ValueCtorVar badMem)]
                      where p = min (ee+fieldPad f) le - (max lo ee)
                            tpPad  = bitvectorType p
                            badMem = InvalidMemory tpPad

-- | Decomposes a single load after a store into a combination of
-- simple value loads.
valueLoad ::
  Addr      {- ^ load address         -} ->
  StorageType      {- ^ load type            -} ->
  Addr      {- ^ store address        -} ->
  ValueView {- ^ view of stored value -} ->
  ValueCtor (ValueLoad Addr)
valueLoad lo ltp so v
  | le <= so && nonZeroLoad = ValueCtorVar (OldMemory lo ltp) -- Load ends before store
  | se <= lo && nonZeroLoad = ValueCtorVar (OldMemory lo ltp) -- Store ends before load
    -- Load is before store.
  | lo < so  = splitTypeValue ltp (so - lo) (\o tp -> valueLoad (lo+o) tp so v)
    -- Load ends after store ends.
  | se < le  = splitTypeValue ltp (le - se) (\o tp -> valueLoad (lo+o) tp so v)
  | (lo,ltp) == (so,stp) = ValueCtorVar (LastStore v)
  | otherwise =
    case storageTypeF ltp of
      Bitvector lw -> loadBitvector lo lw so v
      Float  -> BVToFloat  $ valueLoad lo (bitvectorType 4) so v
      Double -> BVToDouble $ valueLoad lo (bitvectorType 8) so v
      X86_FP80 -> BVToX86_FP80 $ valueLoad lo (bitvectorType 10) so v
      Array ln tp ->
        let leSize = storageTypeSize tp
            val i = valueLoad (lo+leSize*fromIntegral i) tp so v
         in MkArray tp (V.generate (fromIntegral ln) val)
      Struct lflds ->
        let val f = (f, valueLoad (lo+fieldOffset f) (f^.fieldVal) so v)
         in MkStruct (val <$> lflds)
 where stp = fromMaybe (error ("Coerce value given bad view " ++ show v)) (viewType v)
       le = typeEnd lo ltp
       se = so + storageTypeSize stp
       nonZeroLoad = le - lo > 0

-- | @LinearLoadStoreOffsetDiff stride delta@ represents the fact that
--   the difference between the load offset and the store offset is
--   of the form @stride * n + delta@ for some integer @n@, where
--   @stride@ and @delta@ are non-negative integers, and @n@ can be
--   positive, negative, or zero.  If no form if known, then @stride@ is @1@
--   and @delta@ is @0@.
data LinearLoadStoreOffsetDiff = LinearLoadStoreOffsetDiff Bytes Bytes

-- | This function computes a mux tree value for loading a chunk from inside
--   a previously-written value.  The @StorageType@ of the load indicates
--   the size of the loaded value and how we intend to view it.  The bounds,
--   if provided, are bounds on the difference between the load pointer and the
--   store pointer.  Postive values indicate the Load offset is larger than the
--   store offset.  These bounds, if provided, are used to shrink the size of
--   the computed mux tree, and can lead to significantly smaller results.
--   The @ValueView@ is the syntactic representation of the value being
--   loaded from.  The @LinearLoadStoreOffsetDiff@ form further reduces the size
--   of the mux tree by only considering (load offset - store offset) values of
--   the given form.
symbolicValueLoad ::
  BasePreference {- ^ whether addresses are based on store or load -} ->
  StorageType           {- ^ load type            -} ->
  Maybe (Integer, Integer) {- ^ optional bounds on the offset between load and store -} ->
  ValueView      {- ^ view of stored value -} ->
  LinearLoadStoreOffsetDiff {- ^ linear (load offset - store offset) form -} ->
  Mux (ValueCtor (ValueLoad OffsetExpr))
symbolicValueLoad pref tp bnd v (LinearLoadStoreOffsetDiff stride delta) =
  Mux (Or (loadOffset lsz .<= Store) (storeOffset (storageTypeSize stp) .<= Load)) loadFail $
  MuxTable Load Store prefixTable $
  MuxTable Store Load suffixTable loadFail
  where
    lsz = typeEnd 0 tp
    stp = case viewType v of
            Just x -> x
            Nothing -> panic "crucible-llvm:symbolicValueLoad"
                       [ "Unable obtain type of stored value ValueView" ]

    -- The prefix table represents cases where the load pointer occurs strictly before the
    -- write pointer, so that the end of the load may be partially satisfied by this write.
    prefixTable = mkPrefixTable prefixLoBound

    -- The suffix table represents cases where the load pointer occurs at or after the write
    -- pointer so that the load is fully satisfied or the beginning is partially satisfied
    -- by this write.
    suffixTable = mkSuffixTable suffixLoBound

    -- The smallest (non-negative) offset value that can occur in the suffix table.
    -- This is either 0 (load = store) or is given by the difference bound when
    -- the low value is positive.
    suffixLoBound =
      case bnd of
        Just (lo, _hi)
          | lo > 0 -> adjustLoBound delta (toBytes lo)
        _ -> delta

    -- One past the largest offset value that can occur in the suffix table.
    -- This is either the length of the written value, or is given by the
    -- difference bound.  Note, in the case @hi@ is negative, the suffix table
    -- will be empty.
    suffixHiBound =
      case bnd of
        Just (_lo, hi)
          | hi >= 0   -> min (storageTypeSize stp) (toBytes hi + 1)
          | otherwise -> 0
        _ -> storageTypeSize stp

    -- The smallest magnitude of offset that the load may occur
    -- behind the write pointer.  This is at least the stride of the alignment,
    -- but may also be given by the high bound value of the difference, if it is negative.
    prefixLoBound =
      case bnd of
        Just (_lo, hi)
          | hi < 0 -> adjustLoBound (stride - delta) (toBytes (-hi))
        _ -> stride - delta

    -- The largest magnitude of offset, plus one, that the load may occur
    -- behind the write pointer.  This is at most the length of the read,
    -- but may also be given by the low bound value of the offset difference,
    -- if it is negative.  Note, in the case that @lo@ is positive, the
    -- prefix table will be empty.
    prefixHiBound =
      case bnd of
        Just (lo, _hi)
          | lo < 0    -> min lsz (toBytes (-lo) + 1)
          | otherwise -> 0
        _ -> lsz

    -- Walk through prefix offset values, computing a mux tree of the values
    -- for those prefix loads.
    mkPrefixTable :: Bytes -> Map Bytes (Mux (ValueCtor (ValueLoad OffsetExpr)))
    mkPrefixTable i
      | i < prefixHiBound = Map.insert i
        (MuxVar (fmap adjustFn <$> valueLoad 0 tp i v))
        (mkPrefixTable (i + stride))
      | otherwise = Map.empty
      where adjustFn = fixLoadBeforeStoreOffset pref i

    -- Walk through suffix offset values, computing a mux tree of the values
    -- for those suffix loads.
    mkSuffixTable :: Bytes -> Map Bytes (Mux (ValueCtor (ValueLoad OffsetExpr)))
    mkSuffixTable i
      | i < suffixHiBound =
        Map.insert i
        (MuxVar (fmap adjustFn <$> valueLoad i tp 0 v))
        (mkSuffixTable (i + stride))
      | otherwise = Map.empty
      where adjustFn = fixLoadAfterStoreOffset pref i

    loadFail = MuxVar (ValueCtorVar (OldMemory Load tp))

    adjustLoBound :: Bytes -> Bytes -> Bytes
    adjustLoBound i bound = if i >= bound
      then i
      else adjustLoBound (i + stride) bound

-- | Create a value of the given type made up of copies of the given byte.
memsetValue :: a -> StorageType -> ValueCtor a
memsetValue byte = go
  where
    val = ValueCtorVar byte
    go tp =
      case storageTypeF tp of
        Bitvector sz
          | sz <= 1 -> val
          | otherwise -> concatBV 1 val (sz - 1) (go (bitvectorType (sz - 1)))
        Float -> BVToFloat (go (bitvectorType 4))
        Double -> BVToDouble (go (bitvectorType 8))
        X86_FP80 -> BVToX86_FP80 (go (bitvectorType 10))
        Array n etp -> MkArray etp (V.replicate (fromIntegral n) (go etp))
        Struct flds -> MkStruct (fldFn <$> flds)
          where fldFn fld = (fld, go (fld^.fieldVal))

-- | Create value of type that splits at a particular byte offset.
--
-- This function uses the given 'StorageType' to determine how many bytes to
-- read (including accounting for padding in struct types).  The function to
-- load each byte is provided as an argument.
--
-- NOTE: The 'Offset' argument is not necessarily the offset into the
-- allocation; it *could* be zero if the load function captures the offset into
-- the allocation.
loadTypedValueFromBytes
  :: Offset -- ^ The initial offset to pass to the byte loading function
  -> StorageType -- ^ The type used to compute how many bytes to read
  -> (Offset -> IO a) -- ^ A function to read individual bytes (at the given offset)
  -> IO (ValueCtor a)
loadTypedValueFromBytes off tp subFn = case storageTypeF tp of
  Bitvector size
    | size <= 1 -> ValueCtorVar <$> subFn off
    | otherwise -> do
      head_byte <- ValueCtorVar <$> subFn off
      tail_bytes <- loadTypedValueFromBytes
        (off + 1)
        (bitvectorType (size - 1))
        subFn
      return $ concatBV 1 head_byte (size - 1) tail_bytes
  Float ->
    BVToFloat <$> loadTypedValueFromBytes off (bitvectorType 4) subFn
  Double ->
    BVToDouble <$> loadTypedValueFromBytes off (bitvectorType 8) subFn
  X86_FP80 ->
    BVToX86_FP80 <$> loadTypedValueFromBytes off (bitvectorType 10) subFn
  Array len elem_type -> MkArray elem_type <$> V.generateM
    (fromIntegral len)
    (\idx -> loadTypedValueFromBytes
      (off + (fromIntegral idx) * (storageTypeSize elem_type))
      elem_type
      subFn)
  Struct fields -> MkStruct <$> V.mapM
    (\field -> do
      field_val <- loadTypedValueFromBytes
        (off + (fieldOffset field))
        (field^.fieldVal)
        subFn
      return (field, field_val))
    fields
