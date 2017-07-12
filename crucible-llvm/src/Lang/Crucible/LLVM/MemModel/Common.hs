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
{-# LANGUAGE TypeSynonymInstances #-}

module Lang.Crucible.LLVM.MemModel.Common
  ( Addr
  , Size

    -- * Range declarations.
  , Range(..)

    -- * Term declarations
  , Term(..)
  , foldTermM

    -- * Type declarations
  , Type(..)
  , TypeF(..)
  , bitvectorType
  , floatType
  , doubleType
  , arrayType
  , mkStruct
  , mkType
  , typeEnd
  , Field
  , fieldVal
  , fieldPad
  , fieldOffset
  , mkField

    -- * Pointer declarations
  , PtrExpr(..)
  , IntExpr(..)
  , Cond(..)

  , Mux(..)

  , ValueCtor
  , ValueCtorF(..)

  , BasePreference(..)

  , RangeLoad(..)
  , rangeLoad
  , fixedOffsetRangeLoad
  , fixedSizeRangeLoad
  , symbolicRangeLoad

  , ValueView
  , ViewF(..)

  , ValueLoad(..)
  , valueLoad
  , symbolicValueLoad

  ) where

import Control.Exception (assert)
import Control.Lens
import Control.Monad.State
import Data.Maybe
import Data.Typeable
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word

type Addr = Word64

type Size = Addr

type Offset = Size

-- | @WR i j@ denotes that the write should store in range [i..j).
data Range = R { rStart :: Addr, _rEnd :: Addr }
  deriving (Eq, Show)

-- Var

data Term f a = App (f (Term f a))
              | Var a
  deriving (Functor, Foldable, Traversable)

class ShowF f where
  showsPrecF :: Show a => Int -> f a -> ShowS

instance (ShowF f, Show a)  => Show (Term f a) where
  showsPrec p (App f) = showParen (p >= 10) (showString "App " . showsPrecF 10 f)
  showsPrec p (Var x) = showParen (p >= 10) (showString "Var " . showsPrec 10 x)

foldTermM :: (Monad m, Traversable f)
          => (a -> m r) -> (f r -> m r) -> Term f a -> m r
foldTermM f _ (Var v) = f v
foldTermM f g (App v) = g =<< traverse (foldTermM f g) v

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
  = PtrEq PtrExpr PtrExpr
  | PtrLe PtrExpr PtrExpr
  | IntEq IntExpr IntExpr
  | IntLe IntExpr IntExpr
  | And Cond Cond
  deriving (Show)

(.==) :: PtrExpr -> PtrExpr -> Cond
infix 4 .==
(.==) = PtrEq

(.<=) :: PtrExpr -> PtrExpr -> Cond
infix 4 .<=
(.<=) = PtrLe

infixl 6 .+
(.+) :: PtrExpr -> IntExpr -> PtrExpr
x .+ CValue 0 = x
x .+ y = PtrAdd x y

infixl 6 .-
(.-) :: PtrExpr -> PtrExpr -> IntExpr
x .- y = PtrDiff x y

intValue :: Integral a => a -> IntExpr
intValue x = CValue (toInteger x)

-- Muxs

data Mux a = Mux Cond (Mux a) (Mux a) | MuxVar a
  deriving Show

-- Variable for mem model.

loadOffset :: Size -> PtrExpr
loadOffset n = Load .+ intValue n

storeOffset :: Size -> PtrExpr
storeOffset n = Store .+ intValue n

storeEnd :: PtrExpr
storeEnd = Store .+ StoreSize

-- | @loadInStoreRange n@ returns predicate if Store <= Load && Load <= Store + n
loadInStoreRange :: Size -> Cond
loadInStoreRange 0 = Load .== Store
loadInStoreRange n = And (Store .<= Load)
                         (Load .<= Store .+ intValue n)

data Field v = Field { fieldOffset :: Offset
                     , _fieldVal    :: v
                     , fieldPad    :: Size
                     }
 deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable)

fieldVal :: Lens (Field a) (Field b) a b
fieldVal = lens _fieldVal (\s v -> s { _fieldVal = v })

mkField :: Offset -> v -> Size -> Field v
mkField = Field

data TypeF v
   = Bitvector Size -- ^ Size of bitvector in bytes (must be > 0).
   | Float
   | Double
   | Array Size v
   | Struct (Vector (Field v))
 deriving (Eq,Ord,Show,Typeable)

data Type = Type { typeF :: TypeF Type
                 , typeSize :: Size
                 }
  deriving (Eq,Ord,Typeable)

instance Show Type where
  showsPrec p t = showParen (p >= 10) $
    case typeF t of
      Bitvector w -> showString "bitvectorType " . shows w
      Float -> showString "float"
      Double -> showString "double"
      Array n tp -> showString "arrayType " . shows n . showString " " . showsPrec 10 tp
      Struct v -> showString "mkStruct " . shows (V.toList (fldFn <$> v))
        where fldFn f = (f^.fieldVal, fieldPad f)

mkType :: TypeF Type -> Type
mkType tf = Type tf $
  case tf of
    Bitvector w -> w
    Float -> 4
    Double -> 8
    Array n e -> n * typeSize e
    Struct flds -> assert (V.length flds > 0) (fieldEnd (V.last flds))

bitvectorType :: Size -> Type
bitvectorType w = Type (Bitvector w) w

floatType :: Type
floatType = mkType Float

doubleType :: Type
doubleType = mkType Double

arrayType :: Size -> Type -> Type
arrayType n e = Type (Array n e) (n * typeSize e)

structType :: V.Vector (Field Type) -> Type
structType flds = assert (V.length flds > 0) $
  Type (Struct flds) (fieldEnd (V.last flds))

mkStruct :: V.Vector (Type,Size) -> Type
mkStruct l = structType (evalState (traverse fldFn l) 0)
  where fldFn (tp,p) = do
          o <- get
          put $! o + typeSize tp + p
          return Field { fieldOffset = o
                       , _fieldVal = tp
                       , fieldPad = p
                       }

-- | Returns end of actual type bytes (excluded padding from structs).
typeEnd :: Addr -> Type -> Addr
typeEnd a tp = seq a $
  case typeF tp of
    Bitvector w -> a + w
    Float -> a + 4
    Double -> a + 8
    Array n etp -> typeEnd (a + (n-1) * typeSize etp) etp
    Struct flds -> typeEnd (a + fieldOffset f) (f^.fieldVal)
      where f = V.last flds

-- | Returns end of field including padding bytes.
fieldEnd :: Field Type -> Size
fieldEnd f = fieldOffset f + typeSize (f^.fieldVal) + fieldPad f

-- Value constructor

data ValueCtorF v
   = -- | Concatenates two bitvectors.
     -- The first bitvector contains values stored at the low-order bytes
     -- while the second contains values at the high-order bytes.  Thus, the
     -- meaning of this depends on the endianness of the target architecture.
     ConcatBV Size v Size v
   | BVToFloat v
   | BVToDouble v
     -- | Cons one value to beginning of array.
   | ConsArray Type v Integer v
   | AppendArray Type Integer v Integer v
   | MkArray Type (Vector v)
   | MkStruct (Vector (Field Type,v))
 deriving (Functor, Foldable, Traversable, Show)

instance ShowF ValueCtorF where
  showsPrecF = showsPrec

type ValueCtor a = Term ValueCtorF a

concatBV :: Size -> ValueCtor a -> Size -> ValueCtor a -> ValueCtor a
concatBV xw x yw y = App (ConcatBV xw x yw y)

singletonArray :: Type -> ValueCtor a -> ValueCtor a
singletonArray tp e = App (MkArray tp (V.singleton e))

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
    Float -> App (BVToFloat (subFn 0 (bitvectorType 4)))
    Double -> App (BVToDouble (subFn 0 (bitvectorType 8)))
    Array n0 etp -> assert (n0 > 0) $ do
      let esz = typeSize etp
      let (c,part) = assert (esz > 0) $ d `divMod` esz
      let result
            | c > 0 = assert (c < n0) $
              App $ AppendArray etp
                                (toInteger c)
                                (subFn 0 (arrayType c etp))
                                (toInteger (n0 - c))
                                (consPartial (c * esz) (n0 - c))
            | otherwise = consPartial 0 n0
          consPartial o n
            | part == 0 = subFn o (arrayType n etp)
            | n > 1 =
                App $ ConsArray etp
                                (subFn o etp)
                                (toInteger (n-1))
                                (subFn (o+esz) (arrayType (n-1) etp))
            | otherwise = assert (n == 1) $
                singletonArray etp (subFn o etp)
      result
    Struct flds -> App $ MkStruct (fldFn <$> flds)
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

data RangeLoad a b
      -- | Load value from old value.
    = OutOfRange a Type
      -- | In range includes offset relative to store and type.
    | InRange b Type
  deriving (Show)

adjustOffset :: (b -> d)
             -> (a -> c)
             -> RangeLoad a b -> RangeLoad c d
adjustOffset _ outFn (OutOfRange a tp) = OutOfRange (outFn a) tp
adjustOffset inFn _  (InRange b tp) = InRange (inFn b) tp

rangeLoad :: Addr -> Type -> Range -> ValueCtor (RangeLoad Addr Addr)
rangeLoad lo ltp s@(R so se)
   | so == se  = loadFail
   | le <= so  = loadFail
   | se <= lo  = loadFail
   | lo < so   = splitTypeValue ltp (so - lo) (\o tp -> rangeLoad (lo+o) tp s)
   | se < le   = splitTypeValue ltp (se - lo) (\o tp -> rangeLoad (lo+o) tp s)
   | otherwise = assert (so <= lo && le <= se) $ Var (InRange (lo - so) ltp)
 where le = typeEnd lo ltp
       loadFail = Var (OutOfRange lo ltp)

type RangeLoadMux v w = Mux (ValueCtor (RangeLoad v w))

fixedOffsetRangeLoad :: Addr
                     -> Type
                     -> Addr
                     -> RangeLoadMux Addr Addr
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
    loadFail = MuxVar (Var (OutOfRange l tp))

-- | @fixLoadBeforeStoreOffset pref i k@ adjusts a pointer value that is relative
-- the load address into a global pointer.  The code assumes that @load + i == store@.
fixLoadBeforeStoreOffset :: BasePreference -> Offset -> Offset -> PtrExpr
fixLoadBeforeStoreOffset pref i k
  | pref == FixedStore = Store .+ intValue (toInteger k - toInteger i)
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
                   -> Size
                   -> RangeLoadMux PtrExpr IntExpr
fixedSizeRangeLoad _ tp 0 = MuxVar (Var (OutOfRange Load tp))
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

    loadSucc = MuxVar (Var (InRange (Load .- Store) tp))
    loadFail = MuxVar (Var (OutOfRange Load tp))

symbolicRangeLoad :: BasePreference -> Type -> RangeLoadMux PtrExpr IntExpr
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
    loadFail = MuxVar (Var (OutOfRange Load tp))

-- ValueView

type ValueView v = Term ViewF v

data ViewF v
     -- | Select low-order bytes in the bitvector.
     -- The sizes include the number of low bytes, and the number of high bytes.
   = SelectLowBV Size Size v
     -- | Select the given number of high-order bytes in the bitvector.
     -- The sizes include the number of low bytes, and the number of high bytes.
   | SelectHighBV Size Size v
   | FloatToBV v
   | DoubleToBV v
   | ArrayElt Size Type Offset v

   | FieldVal (Vector (Field Type)) Int v
  deriving (Show, Functor, Foldable, Traversable)

instance ShowF ViewF where
  showsPrecF = showsPrec

viewOpType :: ViewF (TypeF Type) -> Maybe Type
viewOpType (SelectLowBV  u v tp) | Bitvector (u + v) == tp = pure $ bitvectorType u
viewOpType (SelectHighBV u v tp) | Bitvector (u + v) == tp = pure $ bitvectorType v
viewOpType (FloatToBV tp)        | Float == tp  = pure $ bitvectorType 4
viewOpType (DoubleToBV tp)       | Double == tp = pure $ bitvectorType 8
viewOpType (ArrayElt n etp i tp) | i < n && Array n etp == tp = pure $ etp
viewOpType (FieldVal v i     tp) | Struct v == tp          = view fieldVal <$> (v V.!? i)
viewOpType _ = Nothing

viewType :: ValueView Type -> Maybe Type
viewType = foldTermM return (viewOpType . fmap typeF)

-- ValueLoad

data ValueLoad v
  = -- Old memory that was used
    OldMemory v Type
  | LastStore (ValueView Type)
    -- | Indicates load touches memory that is invalid, and can't be
    -- read.
  | InvalidMemory Type
  deriving (Functor,Show)

loadBitvector :: Addr -> Size -> Addr -> ValueView Type -> ValueCtor (ValueLoad Addr)
loadBitvector lo lw so v = do
  let le = lo + lw
  let ltp = bitvectorType lw
  let stp = fromMaybe (error ("loadBitvector given bad view " ++ show v)) (viewType v)
  let retValue eo v' = (sz',valueLoad lo' (bitvectorType sz') eo v')
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
        valueLoad lo ltp lo (App (SelectHighBV d (sw - d) v))
      | otherwise -> assert (lo == so && lw < sw) $
        -- Load ends before store ends.
        valueLoad lo ltp so (App (SelectLowBV lw (sw - lw) v))
    Float -> valueLoad lo ltp lo (App (FloatToBV v))
    Double -> valueLoad lo ltp lo (App (DoubleToBV v))
    Array n tp -> snd $ foldl1 cv (val <$> r)
      where cv (wx,x) (wy,y) = (wx + wy, concatBV wx x wy y)
            esz = typeSize tp
            c0 = assert (esz > 0) $ (lo - so) `div` esz
            (c1,p1) = (le - so) `divMod` esz
            -- Get range of indices to read.
            r | p1 == 0 = assert (c1 > c0) [c0..c1-1]
              | otherwise = assert (c1 >= c0) [c0..c1]
            val i = retValue (so+i*esz) (App (ArrayElt n tp i v))
    Struct sflds -> assert (not (null r)) $ snd $ foldl1 cv r
      where cv (wx,x) (wy,y) = (wx+wy, concatBV wx x wy y)
            r = concat (zipWith val [0..] (V.toList sflds))
            val i f = v1
              where eo = so + fieldOffset f
                    ee = eo + typeSize (f^.fieldVal)
                    v1 | le <= eo = v2
                       | ee <= lo = v2
                       | otherwise = retValue eo (App (FieldVal sflds i v)) : v2
                    v2 | fieldPad f == 0 = []   -- Return no padding.
                       | le <= ee = [] -- Nothing of load ends before padding.
                         -- Nothing if padding ends before load begins.
                       | ee+fieldPad f <= lo = []
                       | otherwise = [(p,Var badMem)]
                      where p = min (ee+fieldPad f) le - (max lo ee)
                            tpPad  = bitvectorType p
                            badMem = InvalidMemory tpPad

-- | @valueLoad lo ltp so v@ returns a value with type @ltp@ from reading the
-- value @v@.  The load address is @lo@ and the stored address is @so@.
valueLoad :: Addr -> Type -> Addr -> ValueView Type -> ValueCtor (ValueLoad Addr)
valueLoad lo ltp so v
  | le <= so = Var (OldMemory lo ltp) -- Load ends before store
  | se <= lo = Var (OldMemory lo ltp) -- Store ends before load
    -- Load is before store.
  | lo < so  = splitTypeValue ltp (so - lo) (\o tp -> valueLoad (lo+o) tp so v)
    -- Load ends after store ends.
  | se < le  = splitTypeValue ltp (le - se) (\o tp -> valueLoad (lo+o) tp so v)
  | (lo,ltp) == (so,stp) = Var (LastStore v)
  | otherwise =
    case typeF ltp of
      Bitvector lw -> loadBitvector lo lw so v
      Float  -> App $ BVToFloat  $ valueLoad 0 (bitvectorType 4) so v
      Double -> App $ BVToDouble $ valueLoad 0 (bitvectorType 8) so v
      Array ln tp ->
        let leSize = typeSize tp
            val i = valueLoad (lo+leSize*fromIntegral i) tp so v
         in App (MkArray tp (V.generate (fromIntegral ln) val))
      Struct lflds ->
        let val f = (f, valueLoad (lo+fieldOffset f) (f^.fieldVal) so v)
         in App (MkStruct (val <$> lflds))
 where stp = fromMaybe (error ("Coerce value given bad view " ++ show v)) (viewType v)
       le = typeEnd lo ltp
       se = so + typeSize stp

type ValueLoadMux = Mux (ValueCtor (ValueLoad PtrExpr))

symbolicValueLoad :: BasePreference -- ^ Whether addresses are based on store or load.
                  -> Type
                  -> ValueView Type
                  -> ValueLoadMux
symbolicValueLoad pref tp v =
  Mux (loadOffset lsz .<= Store) loadFail (prefixL lsz)
  where
    prefixL i
      | i > 0 =
        Mux (loadOffset i .== Store)
        (MuxVar (fmap (fixLoadBeforeStoreOffset pref i) <$> valueLoad 0 tp i v))
        (prefixL (i - 1))
      | otherwise = suffixS 0
    lsz = typeEnd 0 tp
    Just stp = viewType v

    suffixS i
      | i < typeSize stp =
        Mux (Load .== storeOffset i)
        (MuxVar (fmap adjustFn <$> valueLoad i tp 0 v))
        (suffixS (i + 1))
      | otherwise = loadFail
      where adjustFn = fixLoadAfterStoreOffset pref i

    loadFail = MuxVar (Var (OldMemory Load tp))
