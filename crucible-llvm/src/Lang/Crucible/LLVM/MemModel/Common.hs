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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Lang.Crucible.LLVM.MemModel.Common
  ( -- * Range declarations.
    Range(..)

    -- * Pointer declarations
  , PtrExpr(..)
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

  , ValueView(..)

  , ValueLoad(..)
  , valueLoad
  , symbolicValueLoad

  , memsetValue
  ) where

import Control.Exception (assert)
import Control.Lens
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word

import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.LLVM.MemModel.Type

-- | @R i j@ denotes that the write should store in range [i..j).
data Range = R { rStart :: Addr, _rEnd :: Addr }
  deriving (Eq, Show)

-- Value

data PtrExpr
  = PtrAdd PtrExpr IntExpr
  | Load
  | Store
  deriving (Show)

data IntExpr
  = PtrDiff PtrExpr PtrExpr
  | IntAdd IntExpr IntExpr
  | CValue Integer
  | StoreSize
  deriving (Show)

data Cond
  = PtrComparable PtrExpr PtrExpr -- ^ Are pointers in the same allocation unit
  | PtrOffsetEq PtrExpr PtrExpr
  | PtrOffsetLe PtrExpr PtrExpr
  | IntEq IntExpr IntExpr
  | IntLe IntExpr IntExpr
  | And Cond Cond
  deriving (Show)

(.==) :: PtrExpr -> PtrExpr -> Cond
infix 4 .==
x .== y = And (PtrComparable x y) (PtrOffsetEq x y)

(.<=) :: PtrExpr -> PtrExpr -> Cond
infix 4 .<=
x .<= y = And (PtrComparable x y) (PtrOffsetLe x y)

infixl 6 .+
(.+) :: PtrExpr -> IntExpr -> PtrExpr
x .+ CValue 0 = x
x .+ y = PtrAdd x y

infixl 6 .-
(.-) :: PtrExpr -> PtrExpr -> IntExpr
x .- y = PtrDiff x y

intValue :: Bytes -> IntExpr
intValue (Bytes n) = CValue (toInteger n)

-- Muxs

data Mux a
  = Mux Cond (Mux a) (Mux a)
  | MuxTable PtrExpr PtrExpr (Map Bytes (Mux a)) (Mux a)
    -- ^ 'MuxTable' encodes a lookup table: @'MuxTable' p1 p2
    -- 'Map.empty' z@ is equivalent to @z@, and @'MuxTable' p1 p2
    -- ('Map.insert' (i, x) m) z@ is equivalent to @'Mux' (p1 '.+'
    -- 'intValue' i '.==' p2) x ('MuxTable' p1 p2 m z)@.
  | MuxVar a
  deriving Show

-- Variable for mem model.

loadOffset :: Bytes -> PtrExpr
loadOffset n = Load .+ intValue n

storeOffset :: Bytes -> PtrExpr
storeOffset n = Store .+ intValue n

storeEnd :: PtrExpr
storeEnd = Store .+ StoreSize

-- | @loadInStoreRange n@ returns predicate if Store <= Load && Load <= Store + n
loadInStoreRange :: Bytes -> Cond
loadInStoreRange (Bytes 0) = Load .== Store
loadInStoreRange n = And (Store .<= Load)
                         (Load .<= Store .+ intValue n)

-- Value constructor

-- | Describes how to construct a larger LLVM value as a combination
-- of smaller components.
data ValueCtor a
  = ValueCtorVar a
    -- | Concatenates two bitvectors.
    -- The first bitvector contains values stored at the low-address bytes
    -- while the second contains values at the high-address bytes. Thus, the
    -- meaning of this depends on the endianness of the target architecture.
  | ConcatBV Bytes (ValueCtor a) Bytes (ValueCtor a)
  | BVToFloat (ValueCtor a)
  | BVToDouble (ValueCtor a)
    -- | Cons one value to beginning of array.
  | ConsArray Type (ValueCtor a) Integer (ValueCtor a)
  | AppendArray Type Integer (ValueCtor a) Integer (ValueCtor a)
  | MkArray Type (Vector (ValueCtor a))
  | MkStruct (Vector (Field Type, ValueCtor a))
  deriving (Functor, Foldable, Traversable, Show)

concatBV :: Bytes -> ValueCtor a -> Bytes -> ValueCtor a -> ValueCtor a
concatBV xw x yw y = ConcatBV xw x yw y

singletonArray :: Type -> ValueCtor a -> ValueCtor a
singletonArray tp e = MkArray tp (V.singleton e)

-- | Create value of type that splits at a particular byte offset.
splitTypeValue :: Type   -- ^ Type of value to create
               -> Offset -- ^ Bytes offset to slice type at.
               -> (Offset -> Type -> ValueCtor a) -- ^ Function for subtypes.
               -> ValueCtor a
splitTypeValue tp d subFn = assert (d > 0) $
  case typeF tp of
    Bitvector sz -> assert (d < sz) $
      concatBV d (subFn 0 (bitvectorType d))
               (sz - d) (subFn d (bitvectorType (sz - d)))
    Float -> BVToFloat (subFn 0 (bitvectorType 4))
    Double -> BVToDouble (subFn 0 (bitvectorType 8))
    Array n0 etp -> assert (n0 > 0) $ do
      let esz = typeSize etp
      let (c,part) = assert (esz > 0) $ unBytes d `divMod` unBytes esz
      let n = n0 - c
      let o = d - Bytes part -- (Bytes c) * esz
      let consPartial
            | part == 0 = subFn o (arrayType n etp)
            | n > 1 =
                ConsArray etp
                          (subFn o etp)
                          (toInteger (n-1))
                          (subFn (o+esz) (arrayType (n-1) etp))
            | otherwise = assert (n == 1) $
                singletonArray etp (subFn o etp)
      let result
            | c > 0 = assert (c < n0) $
              AppendArray etp
                          (toInteger c)
                          (subFn 0 (arrayType c etp))
                          (toInteger n)
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
  = OutOfRange a Type
    -- ^ Load from an address range disjoint from the copied bytes.
    -- The arguments represent the address and type of the load.
  | InRange b Type
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
  Type  {- ^ load type    -} ->
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

fixedOffsetRangeLoad :: Addr
                     -> Type
                     -> Addr
                     -> Mux (ValueCtor (RangeLoad Addr Addr))
fixedOffsetRangeLoad l tp s
  | s < l = do -- Store is before load.
    let sd = l - s -- Number of bytes load comes after store
    Mux (IntLe StoreSize (intValue sd)) loadFail (loadCase (sd+1))
  | le <= s = loadFail -- No load if load ends before write.
  | otherwise = loadCase 0
  where
    le = typeEnd l tp
    loadCase i
      | i < le-s  = Mux (IntEq StoreSize (intValue i)) (loadVal i) (loadCase (i+1))
      | otherwise = loadVal i
    loadVal ssz = MuxVar (rangeLoad l tp (R s (s+ssz)))
    loadFail = MuxVar (ValueCtorVar (OutOfRange l tp))

-- | @fixLoadBeforeStoreOffset pref i k@ adjusts a pointer value that is relative
-- the load address into a global pointer.  The code assumes that @load + i == store@.
fixLoadBeforeStoreOffset :: BasePreference -> Offset -> Offset -> PtrExpr
fixLoadBeforeStoreOffset pref i k
  | pref == FixedStore = Store .+ intValue (k - i)
  | otherwise = Load .+ intValue k

-- | @fixLoadAfterStoreOffset pref i k@ adjusts a pointer value that is relative
-- the load address into a global pointer.  The code assumes that @load == store + i@.
fixLoadAfterStoreOffset :: BasePreference -> Offset -> Offset -> PtrExpr
fixLoadAfterStoreOffset pref i k = assert (k >= i) $
  case pref of
    FixedStore -> Store .+ intValue k
    _          -> Load  .+ intValue (k - i)

-- | @loadFromStoreStart pref tp i j@ loads a value of type @tp@ from a range under the
-- assumptions that @load + i == store@ and @j = i + min(StoreSize, typeEnd(tp)@.
loadFromStoreStart :: BasePreference
                   -> Type
                   -> Offset
                   -> Offset
                   -> ValueCtor (RangeLoad PtrExpr IntExpr)
loadFromStoreStart pref tp i j = adjustOffset inFn outFn <$> rangeLoad 0 tp (R i j)
  where inFn = intValue
        outFn = fixLoadBeforeStoreOffset pref i

fixedSizeRangeLoad :: BasePreference -- ^ Whether addresses are based on store or load.
                   -> Type
                   -> Bytes
                   -> Mux (ValueCtor (RangeLoad PtrExpr IntExpr))
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
      where inFn = intValue
            outFn = fixLoadAfterStoreOffset pref i

    loadSucc = MuxVar (ValueCtorVar (InRange (Load .- Store) tp))
    loadFail = MuxVar (ValueCtorVar (OutOfRange Load tp))

symbolicRangeLoad :: BasePreference -> Type -> Mux (ValueCtor (RangeLoad PtrExpr IntExpr))
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
      where inFn k  = IntAdd (PtrDiff Load Store) (intValue k)
            outFn k = PtrAdd Load (intValue k)

    storeAfterLoad i
      | i < sz = Mux (loadOffset i .== Store) (loadFromOffset i) (storeAfterLoad (i+1))
      | otherwise = loadFail

    loadFromOffset i =
      assert (0 < i && i < sz) $
      Mux (IntLe (intValue (sz - i)) StoreSize) (loadVal i (i+sz)) (f (sz-1))
      where f j | j > i = Mux (IntEq (intValue (j-i)) StoreSize) (loadVal i j) (f (j-1))
                | otherwise = loadFail

    loadVal i j = MuxVar (loadFromStoreStart pref tp i j)
    loadFail = MuxVar (ValueCtorVar (OutOfRange Load tp))

-- ValueView

-- | Represents a projection of a sub-component out of a larger LLVM value.
data ValueView
  = ValueViewVar Type
    -- | Select low-address bytes in the bitvector.
    -- The sizes include the number of low bytes, and the number of high bytes.
  | SelectPrefixBV Bytes Bytes ValueView
    -- | Select the given number of high-address bytes in the bitvector.
    -- The sizes include the number of low bytes, and the number of high bytes.
  | SelectSuffixBV Bytes Bytes ValueView
  | FloatToBV ValueView
  | DoubleToBV ValueView
  | ArrayElt Word64 Type Word64 ValueView

  | FieldVal (Vector (Field Type)) Int ValueView
  deriving Show

viewType :: ValueView -> Maybe Type
viewType (ValueViewVar tp) = Just tp
viewType (SelectPrefixBV u v vv) =
  do tp <- typeF <$> viewType vv
     guard (Bitvector (u + v) == tp)
     pure $ bitvectorType u
viewType (SelectSuffixBV u v vv) =
  do tp <- typeF <$> viewType vv
     guard (Bitvector (u + v) == tp)
     pure $ bitvectorType v
viewType (FloatToBV vv) =
  do tp <- typeF <$> viewType vv
     guard (Float == tp)
     pure $ bitvectorType 4
viewType (DoubleToBV vv) =
  do tp <- typeF <$> viewType vv
     guard (Double == tp)
     pure $ bitvectorType 8
viewType (ArrayElt n etp i vv) =
  do tp <- typeF <$> viewType vv
     guard (i < n && Array n etp == tp)
     pure $ etp
viewType (FieldVal v i vv) =
  do tp <- typeF <$> viewType vv
     guard (Struct v == tp)
     view fieldVal <$> (v V.!? i)

-- | A 'ValueLoad' describes different kinds of memory loads in the
-- context of a new value stored into an old memory.
data ValueLoad v
  = OldMemory v Type
    -- ^ Load from an address range disjoint from the stored value.
    -- The arguments represent the address and type of the load.
  | LastStore ValueView
    -- ^ Load consists of valid bytes within the stored value.
  | InvalidMemory Type
    -- ^ Load touches invalid memory (e.g. trying to read struct padding bytes as a bitvector).
  deriving (Functor,Show)

loadBitvector :: Addr -> Bytes -> Addr -> ValueView -> ValueCtor (ValueLoad Addr)
loadBitvector lo lw so v = do
  let le = lo + lw
  let ltp = bitvectorType lw
  let stp = fromMaybe (error ("loadBitvector given bad view " ++ show v)) (viewType v)
  let retValue eo v' = (sz', valueLoad lo' (bitvectorType sz') eo v')
        where etp = fromMaybe (error ("Bad view " ++ show v')) (viewType v')
              esz = typeSize etp
              lo' = max lo eo
              sz' = min le (eo+esz) - lo'
  case typeF stp of
    Bitvector sw
      | so < lo -> do
        -- Number of bytes to drop.
        let d = lo - so
        -- Store is before load.
        valueLoad lo ltp lo (SelectSuffixBV d (sw - d) v)
      | otherwise -> assert (lo == so && lw < sw) $
        -- Load ends before store ends.
        valueLoad lo ltp so (SelectPrefixBV lw (sw - lw) v)
    Float -> valueLoad lo ltp lo (FloatToBV v)
    Double -> valueLoad lo ltp lo (DoubleToBV v)
    Array n tp -> snd $ foldl1 cv (val <$> r)
      where cv (wx,x) (wy,y) = (wx + wy, concatBV wx x wy y)
            esz = typeSize tp
            c0 = assert (esz > 0) $ unBytes (lo - so) `div` unBytes esz
            (c1,p1) = unBytes (le - so) `divMod` unBytes esz
            -- Get range of indices to read.
            r | p1 == 0 = assert (c1 > c0) [c0..c1-1]
              | otherwise = assert (c1 >= c0) [c0..c1]
            val i = retValue (so+(Bytes i)*esz) (ArrayElt n tp i v)
    Struct sflds -> assert (not (null r)) $ snd $ foldl1 cv r
      where cv (wx,x) (wy,y) = (wx+wy, concatBV wx x wy y)
            r = concat (zipWith val [0..] (V.toList sflds))
            val i f = v1
              where eo = so + fieldOffset f
                    ee = eo + typeSize (f^.fieldVal)
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
  Type      {- ^ load type            -} ->
  Addr      {- ^ store address        -} ->
  ValueView {- ^ view of stored value -} ->
  ValueCtor (ValueLoad Addr)
valueLoad lo ltp so v
  | le <= so = ValueCtorVar (OldMemory lo ltp) -- Load ends before store
  | se <= lo = ValueCtorVar (OldMemory lo ltp) -- Store ends before load
    -- Load is before store.
  | lo < so  = splitTypeValue ltp (so - lo) (\o tp -> valueLoad (lo+o) tp so v)
    -- Load ends after store ends.
  | se < le  = splitTypeValue ltp (le - se) (\o tp -> valueLoad (lo+o) tp so v)
  | (lo,ltp) == (so,stp) = ValueCtorVar (LastStore v)
  | otherwise =
    case typeF ltp of
      Bitvector lw -> loadBitvector lo lw so v
      Float  -> BVToFloat  $ valueLoad 0 (bitvectorType 4) so v
      Double -> BVToDouble $ valueLoad 0 (bitvectorType 8) so v
      Array ln tp ->
        let leSize = typeSize tp
            val i = valueLoad (lo+leSize*fromIntegral i) tp so v
         in MkArray tp (V.generate (fromIntegral ln) val)
      Struct lflds ->
        let val f = (f, valueLoad (lo+fieldOffset f) (f^.fieldVal) so v)
         in MkStruct (val <$> lflds)
 where stp = fromMaybe (error ("Coerce value given bad view " ++ show v)) (viewType v)
       le = typeEnd lo ltp
       se = so + typeSize stp

symbolicValueLoad ::
  BasePreference {- ^ whether addresses are based on store or load -} ->
  Type           {- ^ load type            -} ->
  ValueView      {- ^ view of stored value -} ->
  Alignment      {- ^ alignment of store and load -} ->
  Mux (ValueCtor (ValueLoad PtrExpr))
symbolicValueLoad pref tp v alignment =
  Mux (loadOffset lsz .<= Store) loadFail $
  MuxTable Load Store (prefixTable stride) $
  MuxTable Store Load (suffixTable 0) loadFail
  where
    stride = fromAlignment alignment
    lsz = typeEnd 0 tp
    Just stp = viewType v

    prefixTable :: Bytes -> Map Bytes (Mux (ValueCtor (ValueLoad PtrExpr)))
    prefixTable i
      | i < lsz = Map.insert i
        (MuxVar (fmap adjustFn <$> valueLoad 0 tp i v))
        (prefixTable (i + stride))
      | otherwise = Map.empty
      where adjustFn = fixLoadBeforeStoreOffset pref i

    suffixTable :: Bytes -> Map Bytes (Mux (ValueCtor (ValueLoad PtrExpr)))
    suffixTable i
      | i < typeSize stp =
        Map.insert i
        (MuxVar (fmap adjustFn <$> valueLoad i tp 0 v))
        (suffixTable (i + stride))
      | otherwise = Map.empty
      where adjustFn = fixLoadAfterStoreOffset pref i

    loadFail = MuxVar (ValueCtorVar (OldMemory Load tp))

-- | Create a value of the given type made up of copies of the given byte.
memsetValue :: a -> Type -> ValueCtor a
memsetValue byte = go
  where
    val = ValueCtorVar byte
    go tp =
      case typeF tp of
        Bitvector sz
          | sz <= 1 -> val
          | otherwise -> concatBV 1 val (sz - 1) (go (bitvectorType (sz - 1)))
        Float -> BVToFloat (go (bitvectorType 4))
        Double -> BVToDouble (go (bitvectorType 8))
        Array n etp -> MkArray etp (V.replicate (fromIntegral n) (go etp))
        Struct flds -> MkStruct (fldFn <$> flds)
          where fldFn fld = (fld, go (fld^.fieldVal))
