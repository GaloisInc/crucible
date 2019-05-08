{-|
Copyright   : (c) Galois Inc, 2015-2016
License     : BSD3
Maintainer  : jhendrix@galois.com

This module declares a set of abstract domains used by the solver.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module What4.Utils.AbstractDomains
  ( ValueBound(..)
  , minValueBound
  , maxValueBound
    -- * ValueRange
  , ValueRange(..)
  , unboundedRange
  , mapRange
  , rangeLowBound
  , rangeHiBound
  , singleRange
  , concreteRange
  , valueRange
  , addRange
  , negateRange
  , rangeScalarMul
  , mulRange
  , joinRange
  , asSingleRange
  , rangeCheckEq
  , rangeCheckLe
    -- * integer range operations
  , intAbsRange
  , intDivRange
  , intModRange
    -- * Boolean abstract value
  , absAnd
  , absOr
    -- * NatValueRange
  , NatValueRange(..)
  , natRange
  , natSingleRange
  , natRangeLow
  , natRangeHigh
  , natCheckEq
  , natCheckLe
  , natRangeAdd
  , natRangeScalarMul
  , natRangeMul
  , natRangeJoin
  , asSingleNatRange
  , unboundedNatRange
  , natRangeToRange
  , natRangeDiv
  , natRangeMod
    -- * RealAbstractValue
  , RealAbstractValue(..)
  , ravUnbounded
  , ravSingle
  , ravConcreteRange
  , ravJoin
  , ravAdd
  , ravScalarMul
  , ravMul
  , ravCheckEq
  , ravCheckLe
    -- * Abstractable
  , avTop
  , avSingle
  , avContains
  , AbstractValue
  , ConcreteValue
  , Abstractable(..)
  , withAbstractable
  , AbstractValueWrapper(..)
  , ConcreteValueWrapper(..)
  ) where

import           Control.Exception (assert)
import           Data.Kind
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableFC
import           Data.Ratio (denominator)
import           Data.Text (Text)
import           Numeric.Natural

import           What4.BaseTypes
import           What4.Utils.BVDomain (BVDomain)
import qualified What4.Utils.BVDomain as BVD
import           What4.Utils.Complex

ctxZipWith3 :: (forall (x::k) . a x -> b x -> c x -> d x)
            -> Ctx.Assignment a (ctx::Ctx.Ctx k)
            -> Ctx.Assignment b ctx
            -> Ctx.Assignment c ctx
            -> Ctx.Assignment d ctx
ctxZipWith3 f a b c =
  Ctx.generate (Ctx.size a) $ \i ->
    f (a Ctx.! i) (b Ctx.! i) (c Ctx.! i)


------------------------------------------------------------------------
-- ValueBound

-- | A lower or upper bound on a value.
data ValueBound tp
   = Unbounded
   | Inclusive !tp
  deriving (Functor, Show)

instance Applicative ValueBound where
  pure = Inclusive
  Unbounded <*> _ = Unbounded
  _ <*> Unbounded = Unbounded
  Inclusive f <*> Inclusive v = Inclusive (f v)

instance Monad ValueBound where
  return = pure
  Unbounded >>= _ = Unbounded
  Inclusive v >>= f = f v

minValueBound :: Ord tp => ValueBound tp -> ValueBound tp -> ValueBound tp
minValueBound x y = min <$> x <*> y

maxValueBound :: Ord tp => ValueBound tp -> ValueBound tp -> ValueBound tp
maxValueBound x y = max <$> x <*> y

lowerBoundIsNegative :: (Ord tp, Num tp) => ValueBound tp -> Bool
lowerBoundIsNegative Unbounded = True
lowerBoundIsNegative (Inclusive y) = y <= 0

upperBoundIsNonNeg :: (Ord tp, Num tp) => ValueBound tp -> Bool
upperBoundIsNonNeg Unbounded = True
upperBoundIsNonNeg (Inclusive y) = y >= 0

------------------------------------------------------------------------
-- ValueRange support classes.

-- | Describes a range of values in a totally ordered set.
data ValueRange tp
  = SingleRange !tp
    -- ^ Indicates that range denotes a single value
  | MultiRange !(ValueBound tp) !(ValueBound tp)
    -- ^ Indicates that the number is somewhere between the given upper and lower bound.

intAbsRange :: ValueRange Integer -> ValueRange Integer
intAbsRange r = case r of
  SingleRange x -> SingleRange (abs x)
  MultiRange (Inclusive lo) hi | 0 <= lo -> MultiRange (Inclusive lo) hi
  MultiRange lo (Inclusive hi) | hi <= 0 -> MultiRange (Inclusive (negate hi)) (negate <$> lo)
  MultiRange lo hi -> MultiRange (Inclusive 0) ((\x y -> max (abs x) (abs y)) <$> lo <*> hi)

-- | Compute an abstract range for integer division.  We are using the SMTLib
--   division operation, where the division is floor when the divisor is positive
--   and ceiling when the divisor is negative.  We compute the ranges assuming
--   that division by 0 doesn't happen, and we are allowed to return nonsense
--   ranges for these cases.
intDivRange :: ValueRange Integer -> ValueRange Integer -> ValueRange Integer
intDivRange (SingleRange x) (SingleRange y)
  | y > 0  = SingleRange (x `div` y)
  | y < 0  = SingleRange (negate (x `div` negate y))
intDivRange (MultiRange lo hi) (SingleRange y)
  | y >  0 = MultiRange
                   ((\x -> x `div` y) <$> lo)
                   ((\x -> x `div` y) <$> hi)
  | y <  0 = negateRange $ MultiRange
                    ((\x -> x `div` negate y) <$> lo)
                    ((\x -> x `div` negate y) <$> hi)

intDivRange x (MultiRange (Inclusive lo) hi)
  | 0 < lo = intDivAux x lo hi

intDivRange x (MultiRange lo (Inclusive hi))
  | hi < 0 = negateRange (intDivAux x (negate hi) (negate <$> lo))

-- The divisor interval contains 0, so we learn nothing
intDivRange _ _ = MultiRange Unbounded Unbounded


-- Here we get to assume 'lo' and 'hi' are strictly positive
intDivAux ::
  ValueRange Integer ->
  Integer -> ValueBound Integer ->
  ValueRange Integer
intDivAux x lo Unbounded = MultiRange lo' hi'
  where
  lo' = case rangeLowBound x of
           Unbounded -> Unbounded
           Inclusive z -> Inclusive (min 0 (div z lo))

  hi' = case rangeHiBound x of
           Unbounded   -> Unbounded
           Inclusive z -> Inclusive (max (-1) (div z lo))

intDivAux x lo (Inclusive hi) = MultiRange lo' hi'
  where
  lo' = case rangeLowBound x of
           Unbounded -> Unbounded
           Inclusive z -> Inclusive (min (div z hi) (div z lo))

  hi' = case rangeHiBound x of
           Unbounded   -> Unbounded
           Inclusive z -> Inclusive (max (div z hi) (div z lo))

intModRange :: ValueRange Integer -> ValueRange Integer -> ValueRange Integer
intModRange _ (SingleRange y) | y == 0 = MultiRange Unbounded Unbounded
intModRange (SingleRange x) (SingleRange y) = SingleRange (x `mod` abs y)
intModRange (MultiRange (Inclusive lo) (Inclusive hi)) (SingleRange y)
   | hi' - lo' == hi - lo = MultiRange (Inclusive lo') (Inclusive hi')
  where
  lo' = lo `mod` abs y
  hi' = hi `mod` abs y
intModRange _ y
  | Inclusive lo <- rangeLowBound yabs, lo > 0
  = MultiRange (Inclusive 0) (pred <$> rangeHiBound yabs)
  | otherwise
  = MultiRange Unbounded Unbounded
 where
 yabs = intAbsRange y


addRange :: Num tp => ValueRange tp -> ValueRange tp -> ValueRange tp
addRange (SingleRange x) (SingleRange y) = SingleRange (x+y)
addRange (SingleRange x) (MultiRange ly uy) = MultiRange ((x+) <$> ly) ((x+) <$> uy)
addRange (MultiRange lx ux) (SingleRange y) = MultiRange ((y+) <$> lx) ((y+) <$> ux)
addRange (MultiRange lx ux) (MultiRange ly uy) =
  MultiRange ((+) <$> lx <*> ly) ((+) <$> ux <*> uy)

-- | Return 'Just True if the range only contains an integer, 'Just False' if it
-- contains no integers, and 'Nothing' if the range contains both integers and
-- non-integers.
rangeIsInteger :: ValueRange Rational -> Maybe Bool
rangeIsInteger (SingleRange x) = Just (denominator x == 1)
rangeIsInteger (MultiRange (Inclusive l) (Inclusive u))
  | floor l + 1 >= (ceiling u :: Integer)
  , denominator l /= 1
  , denominator u /= 1 = Just False
rangeIsInteger _ = Nothing

-- | Multiply a range by a scalar value
rangeScalarMul :: (Ord tp, Num tp) =>  tp -> ValueRange tp -> ValueRange tp
rangeScalarMul x (SingleRange y) = SingleRange (x*y)
rangeScalarMul x (MultiRange ly uy)
  | x <  0 = MultiRange ((x*) <$> uy) ((x*) <$> ly)
  | x == 0 = SingleRange 0
  | otherwise = assert (x > 0) $ MultiRange ((x*) <$> ly) ((x*) <$> uy)

negateRange :: (Num tp) => ValueRange tp -> ValueRange tp
negateRange (SingleRange x) = SingleRange (negate x)
negateRange (MultiRange lo hi) = MultiRange (negate <$> hi) (negate <$> lo)

-- | Multiply two ranges together.
mulRange :: (Ord tp, Num tp) => ValueRange tp -> ValueRange tp -> ValueRange tp
mulRange (SingleRange x) y = rangeScalarMul x y
mulRange x (SingleRange y) = rangeScalarMul y x
mulRange (MultiRange lx ux) (MultiRange ly uy) = MultiRange lz uz
  where x_neg = lowerBoundIsNegative lx
        x_pos = upperBoundIsNonNeg ux
        y_neg = lowerBoundIsNegative ly
        y_pos = upperBoundIsNonNeg uy
             -- X can be negative and y can be positive, and also
             -- x can be positive and y can be negative.
        lz | x_neg && y_pos && x_pos && y_neg =
               minValueBound ((*) <$> lx <*> uy)
                             ((*) <$> ux <*> ly)
             -- X can be negative and Y can be positive, but
             -- either x must be negative (!x_pos) or y cannot be
             -- negative (!y_neg).
           | x_neg && y_pos = (*) <$> lx <*> uy
             -- X can be positive and Y can be negative, but
             -- either x must be positive (!x_neg) or y cannot be
             -- positive (!y_pos).
           | x_pos && y_neg = (*) <$> ux <*> ly
             -- Both x and y must be negative.
           | x_neg = assert (not x_pos && not y_pos) $ (*) <$> ux <*> uy
             -- Both x and y must be positive.
           | otherwise = (*) <$> lx <*> ly
        uz | x_neg && y_neg && x_pos && y_pos =
             maxValueBound ((*) <$> lx <*> ly)
                           ((*) <$> ux <*> uy)
             -- Both x and y can be negative, but they both can't be positive.
           | x_neg && y_neg = (*) <$> lx <*> ly
             -- Both x and y can be positive, but they both can't be negative.
           | x_pos && y_pos = (*) <$> ux <*> uy
             -- x must be positive and y must be negative.
           | x_pos = (*) <$> lx <*> uy
             -- x must be negative and y must be positive.
           | otherwise = (*) <$> ux <*> ly

-- | Return lower bound of range.
rangeLowBound :: ValueRange tp -> ValueBound tp
rangeLowBound (SingleRange x) = Inclusive x
rangeLowBound (MultiRange l _) = l

-- | Return upper bound of range.
rangeHiBound :: ValueRange tp -> ValueBound tp
rangeHiBound (SingleRange x) = Inclusive x
rangeHiBound (MultiRange _ u) = u

-- | Compute the smallest range containing both ranges.
joinRange :: Ord tp => ValueRange tp -> ValueRange tp -> ValueRange tp
joinRange (SingleRange x) (SingleRange y)
  | x == y = SingleRange x
joinRange x y = MultiRange (minValueBound lx ly) (maxValueBound ux uy)
  where lx = rangeLowBound x
        ux = rangeHiBound x
        ly = rangeLowBound y
        uy = rangeHiBound y

-- | Return true if value ranges overlap.
rangeOverlap :: Ord tp => ValueRange tp -> ValueRange tp -> Bool
rangeOverlap x y
   -- first range is before second.
  | Inclusive ux <- rangeHiBound x
  , Inclusive ly <- rangeLowBound y
  , ux < ly = False

  -- second range is before first.
  | Inclusive lx <- rangeLowBound x
  , Inclusive uy <- rangeHiBound y
  , uy < lx = False

  -- Ranges share some elements.
  | otherwise = True

-- | Return maybe Boolean if range is equal, is not equal, or indeterminant.
rangeCheckEq :: Ord tp => ValueRange tp -> ValueRange tp -> Maybe Bool
rangeCheckEq x y
    -- If ranges do not overlap return false.
  | not (rangeOverlap x y) = Just False
    -- If they are both single values, then result can be determined.
  | Just cx <- asSingleRange x
  , Just cy <- asSingleRange y
  = Just (cx == cy)
    -- Otherwise result is indeterminant.
  | otherwise = Nothing


rangeCheckLe :: Ord tp => ValueRange tp -> ValueRange tp -> Maybe Bool
rangeCheckLe x y
    -- First range upper bound is below lower bound of second.
  | Inclusive ux <- rangeHiBound x
  , Inclusive ly <- rangeLowBound y
  , ux <= ly = Just True

    -- First range lower bound is above upper bound of second.
  | Inclusive lx <- rangeLowBound x
  , Inclusive uy <- rangeHiBound y
  , uy <  lx = Just False

  | otherwise = Nothing

-- | Defines a unbounded value range.
unboundedRange :: ValueRange tp
unboundedRange = MultiRange Unbounded Unbounded

-- | Defines a unbounded value range.
concreteRange :: Eq tp => tp -> tp -> ValueRange tp
concreteRange x y
  | x == y = SingleRange x
  | otherwise = MultiRange (Inclusive x) (Inclusive y)

-- | Defines a value range containing a single element.
singleRange :: tp -> ValueRange tp
singleRange v = SingleRange v

-- | Define a value range with the given bounds
valueRange :: Eq tp => ValueBound tp -> ValueBound tp -> ValueRange tp
valueRange (Inclusive x) (Inclusive y)
  | x == y = SingleRange x
valueRange x y = MultiRange x y

-- | Check if range is just a single element.
asSingleRange :: ValueRange tp -> Maybe tp
asSingleRange (SingleRange x) = Just x
asSingleRange _ = Nothing

mapRange :: (a -> b) -> ValueRange a -> ValueRange b
mapRange f (SingleRange x) = SingleRange (f x)
mapRange f (MultiRange l u) = MultiRange (f <$> l) (f <$> u)

------------------------------------------------------------------------
-- AbstractValue definition.

-- Contains range for rational and whether value must be an integer.
data RealAbstractValue = RAV { ravRange :: !(ValueRange Rational)
                             , ravIsInteger :: !(Maybe Bool)
                             }

ravUnbounded :: RealAbstractValue
ravUnbounded = (RAV unboundedRange Nothing)

ravSingle :: Rational -> RealAbstractValue
ravSingle x = RAV (singleRange x) (Just $! denominator x == 1)

-- | Range accepting everything between lower and upper bound.
ravConcreteRange :: Rational -- ^ Lower bound
                 -> Rational -- ^ Upper bound
                 -> RealAbstractValue
ravConcreteRange l h = RAV (concreteRange l h) (Just $! b)
  where -- Return true if this is a singleton.
        b = l == h && denominator l == 1

-- | Add two real abstract values.
ravAdd :: RealAbstractValue -> RealAbstractValue -> RealAbstractValue
ravAdd (RAV xr xi) (RAV yr yi) = RAV zr zi
  where zr = addRange xr yr
        zi | (xi,yi) == (Just True, Just True) = Just True
           | otherwise = rangeIsInteger zr

ravScalarMul :: Rational -> RealAbstractValue -> RealAbstractValue
ravScalarMul x (RAV yr yi) = RAV zr zi
  where zr = rangeScalarMul x yr
        zi | denominator x == 1 && yi == Just True = Just True
           | otherwise = rangeIsInteger zr


ravMul :: RealAbstractValue -> RealAbstractValue -> RealAbstractValue
ravMul (RAV xr xi) (RAV yr yi) = RAV zr zi
  where zr = mulRange xr yr
        zi | (xi,yi) == (Just True, Just True) = Just True
           | otherwise = rangeIsInteger zr

ravJoin :: RealAbstractValue -> RealAbstractValue -> RealAbstractValue
ravJoin (RAV xr xi) (RAV yr yi) = RAV (joinRange xr yr) zi
  where zi | xi == yi = xi
           | otherwise = Nothing

ravCheckEq :: RealAbstractValue -> RealAbstractValue -> Maybe Bool
ravCheckEq (RAV xr _) (RAV yr _) = rangeCheckEq xr yr

ravCheckLe :: RealAbstractValue -> RealAbstractValue -> Maybe Bool
ravCheckLe (RAV xr _) (RAV yr _) = rangeCheckLe xr yr

-- Computing AbstractValue

absAnd :: Maybe Bool -> Maybe Bool -> Maybe Bool
absAnd (Just False) _ = Just False
absAnd (Just True) y = y
absAnd _ (Just False) = Just False
absAnd x (Just True) = x
absAnd Nothing Nothing = Nothing

absOr :: Maybe Bool -> Maybe Bool -> Maybe Bool
absOr (Just False) y = y
absOr (Just True)  _ = Just True
absOr x (Just False) = x
absOr _ (Just True)  = Just True
absOr Nothing Nothing = Nothing

data NatValueRange
  = NatSingleRange !Natural
  | NatMultiRange !Natural !(ValueBound Natural)

asSingleNatRange :: NatValueRange -> Maybe Natural
asSingleNatRange (NatSingleRange x) = Just x
asSingleNatRange _ = Nothing

natRange :: Natural -> ValueBound Natural -> NatValueRange
natRange x (Inclusive y)
  | x == y = NatSingleRange x
natRange x y = NatMultiRange x y

natSingleRange :: Natural -> NatValueRange
natSingleRange = NatSingleRange

natRangeAdd :: NatValueRange -> NatValueRange -> NatValueRange
natRangeAdd (NatSingleRange x)      (NatSingleRange y)      = NatSingleRange (x+y)
natRangeAdd (NatSingleRange x)      (NatMultiRange loy hiy) = NatMultiRange (x   + loy) ((+) <$> pure x <*> hiy)
natRangeAdd (NatMultiRange lox hix) (NatSingleRange y)      = NatMultiRange (lox + y)   ((+) <$> hix    <*> pure y)
natRangeAdd (NatMultiRange lox hix) (NatMultiRange loy hiy) = NatMultiRange (lox + loy) ((+) <$> hix    <*> hiy)

natRangeScalarMul :: Natural -> NatValueRange -> NatValueRange
natRangeScalarMul x (NatSingleRange y) = NatSingleRange (x * y)
natRangeScalarMul x (NatMultiRange lo hi) = NatMultiRange (x * lo) ((x*) <$> hi)

natRangeMul :: NatValueRange -> NatValueRange -> NatValueRange
natRangeMul (NatSingleRange x) y = natRangeScalarMul x y
natRangeMul x (NatSingleRange y) = natRangeScalarMul y x
natRangeMul (NatMultiRange lox hix) (NatMultiRange loy hiy) =
    NatMultiRange (lox * loy) ((*) <$> hix <*> hiy)

natRangeDiv :: NatValueRange -> NatValueRange -> NatValueRange
natRangeDiv (NatSingleRange x) (NatSingleRange y) | y > 0 =
  NatSingleRange (x `div` y)
natRangeDiv (NatMultiRange lo hi) (NatSingleRange y) | y > 0 =
  NatMultiRange (lo `div` y) ((`div` y) <$> hi)
natRangeDiv x (NatMultiRange lo (Inclusive hi)) | lo > 0 =
  NatMultiRange (div (natRangeLow x) hi) ((`div` lo) <$> natRangeHigh x)
natRangeDiv x (NatMultiRange lo Unbounded) | lo > 0 =
  NatMultiRange 0 ((`div` lo) <$> natRangeHigh x)
-- range contains 0
natRangeDiv _ _ =
  NatMultiRange 0 Unbounded

natRangeMod :: NatValueRange -> NatValueRange -> NatValueRange
natRangeMod (NatSingleRange x) (NatSingleRange y)
   | y > 0 = NatSingleRange (x `mod` y)
natRangeMod (NatMultiRange lo (Inclusive hi)) (NatSingleRange y)
   | y > 0
   , toInteger hi' - toInteger lo' == toInteger hi - toInteger lo
   = NatMultiRange lo' (Inclusive hi')
  where
  lo' = lo `mod` y
  hi' = hi `mod` y
natRangeMod _ (NatMultiRange lo (Inclusive hi))
  | lo > 0
  = NatMultiRange 0 (Inclusive (pred hi))
natRangeMod _ _
  = NatMultiRange 0 Unbounded

-- | Compute the smallest range containing both ranges.
natRangeJoin :: NatValueRange -> NatValueRange -> NatValueRange
natRangeJoin (NatSingleRange x) (NatSingleRange y)
  | x == y = NatSingleRange x
natRangeJoin x y = NatMultiRange (min lx ly) (maxValueBound ux uy)
  where lx = natRangeLow x
        ux = natRangeHigh x
        ly = natRangeLow y
        uy = natRangeHigh y

natRangeLow :: NatValueRange -> Natural
natRangeLow (NatSingleRange x) = x
natRangeLow (NatMultiRange lx _) = lx

natRangeHigh :: NatValueRange -> ValueBound Natural
natRangeHigh (NatSingleRange x) = Inclusive x
natRangeHigh (NatMultiRange _ u) = u

-- | Return if nat value ranges overlap.
natRangeOverlap :: NatValueRange -> NatValueRange -> Bool
natRangeOverlap x y
  | Inclusive uy <- natRangeHigh y
  , uy < natRangeLow x = False

  | Inclusive ux <- natRangeHigh x
  , ux < natRangeLow y = False

  | otherwise = True

-- | Return maybe Boolean if nat is equal, is not equal, or indeterminant.
natCheckEq :: NatValueRange -> NatValueRange -> Maybe Bool
natCheckEq x y
    -- If ranges do not overlap return false.
  | not (natRangeOverlap x y) = Just False
    -- If they are both single values, then result can be determined.
  | Just cx <- asSingleNatRange x
  , Just cy <- asSingleNatRange y
  = Just (cx == cy)
    -- Otherwise result is indeterminant.
  | otherwise = Nothing

-- | Return maybe Boolean if nat is equal, is not equal, or indeterminant.
natCheckLe :: NatValueRange -> NatValueRange -> Maybe Bool
natCheckLe x y
  | Inclusive ux <- natRangeHigh x, ux <= natRangeLow y = Just True
  | Inclusive uy <- natRangeHigh y, uy <  natRangeLow x = Just False
  | otherwise = Nothing

unboundedNatRange :: NatValueRange
unboundedNatRange = NatMultiRange 0 Unbounded

natJoinRange :: NatValueRange -> NatValueRange -> NatValueRange
natJoinRange (NatSingleRange x) (NatSingleRange y)
  | x == y = NatSingleRange x
natJoinRange x y = NatMultiRange (min lx ly) (maxValueBound ux uy)
  where
    lx = natRangeLow x
    ux = natRangeHigh x
    ly = natRangeLow y
    uy = natRangeHigh y

natRangeToRange :: NatValueRange -> ValueRange Integer
natRangeToRange (NatSingleRange x)  = SingleRange (toInteger x)
natRangeToRange (NatMultiRange l u) = MultiRange (Inclusive (toInteger l)) (toInteger <$> u)


-- | An abstract value represents a disjoint st of values.
type family AbstractValue (tp::BaseType) :: Type where
  AbstractValue BaseBoolType = Maybe Bool
  AbstractValue BaseNatType = NatValueRange
  AbstractValue BaseIntegerType = ValueRange Integer
  AbstractValue BaseRealType = RealAbstractValue
  AbstractValue BaseStringType = ()
  AbstractValue (BaseBVType w) = BVDomain w
  AbstractValue (BaseFloatType _) = ()
  AbstractValue BaseComplexType = Complex RealAbstractValue
  AbstractValue (BaseArrayType idx b) = AbstractValue b
  AbstractValue (BaseStructType ctx) = Ctx.Assignment AbstractValueWrapper ctx

newtype AbstractValueWrapper tp
      = AbstractValueWrapper { unwrapAV :: AbstractValue tp }

type family ConcreteValue (tp::BaseType) :: Type where
  ConcreteValue BaseBoolType = Bool
  ConcreteValue BaseNatType = Natural
  ConcreteValue BaseIntegerType = Integer
  ConcreteValue BaseRealType = Rational
  ConcreteValue BaseStringType = Text
  ConcreteValue (BaseBVType w) = Integer
  ConcreteValue (BaseFloatType _) = ()
  ConcreteValue BaseComplexType = Complex Rational
  ConcreteValue (BaseArrayType idx b) = ()
  ConcreteValue (BaseStructType ctx) = Ctx.Assignment ConcreteValueWrapper ctx

newtype ConcreteValueWrapper tp
      = ConcreteValueWrapper { unwrapCV :: ConcreteValue tp }

-- | Create an abstract value that contains every concrete value.
avTop :: BaseTypeRepr tp -> AbstractValue tp
avTop tp =
  case tp of
    BaseBoolRepr    ->  Nothing
    BaseNatRepr     -> unboundedNatRange
    BaseIntegerRepr -> unboundedRange
    BaseRealRepr    -> ravUnbounded
    BaseComplexRepr -> ravUnbounded :+ ravUnbounded
    BaseStringRepr  -> ()
    BaseBVRepr w    -> BVD.any w
    BaseFloatRepr{} -> ()
    BaseArrayRepr _a b -> avTop b
    BaseStructRepr flds -> fmapFC (\etp -> AbstractValueWrapper (avTop etp)) flds

-- | Create an abstract value that contains the given concrete value.
avSingle :: BaseTypeRepr tp -> ConcreteValue tp -> AbstractValue tp
avSingle tp =
  case tp of
    BaseBoolRepr -> Just
    BaseNatRepr -> natSingleRange
    BaseIntegerRepr -> singleRange
    BaseRealRepr -> ravSingle
    BaseStringRepr -> \_ -> ()
    BaseComplexRepr -> fmap ravSingle
    BaseBVRepr w -> BVD.singleton w
    BaseFloatRepr _ -> \_ -> ()
    BaseArrayRepr _a b -> \_ -> avTop b
    BaseStructRepr flds -> \vals ->
      Ctx.zipWith
        (\ftp v -> AbstractValueWrapper (avSingle ftp (unwrapCV v)))
        flds
        vals

------------------------------------------------------------------------
-- Abstractable

class Abstractable (tp::BaseType) where

  -- | Take the union of the two abstract values.
  avJoin     :: BaseTypeRepr tp -> AbstractValue tp -> AbstractValue tp -> AbstractValue tp

  -- | Returns true if the abstract values could contain a common concrete
  -- value.
  avOverlap  :: BaseTypeRepr tp -> AbstractValue tp -> AbstractValue tp -> Bool


  -- | Check equality on two abstract values.  Return true or false if we can definitively
  --   determine the equality of the two elements, and nothing otherwise.
  avCheckEq :: BaseTypeRepr tp -> AbstractValue tp -> AbstractValue tp -> Maybe Bool

avJoin' :: BaseTypeRepr tp
        -> AbstractValueWrapper tp
        -> AbstractValueWrapper tp
        -> AbstractValueWrapper tp
avJoin' tp x y = withAbstractable tp $
  AbstractValueWrapper $ avJoin tp (unwrapAV x) (unwrapAV y)

-- Abstraction captures whether Boolean is constant true or false or Nothing
instance Abstractable BaseBoolType where
  avJoin _ x y
    | x == y = x
    | otherwise = Nothing

  avOverlap _ = f
    where f Nothing _ = True
          f _ Nothing = True
          f (Just x) (Just y) = x == y

  avCheckEq _ (Just x) (Just y) = Just $! x == y
  avCheckEq _ _ _ = Nothing

instance Abstractable BaseStringType where
  avJoin _ _ _ = ()
  avOverlap _ _ _ = True
  avCheckEq _ _ _ = Nothing

-- Natural numbers have a lower and upper bound associated with them.
instance Abstractable BaseNatType where
  avJoin _ = natJoinRange
  avOverlap _ x y = rangeOverlap (natRangeToRange x) (natRangeToRange y)
  avCheckEq _ = natCheckEq

-- Integers have a lower and upper bound associated with them.
instance Abstractable BaseIntegerType where
  avJoin _ = joinRange
  avOverlap _ = rangeOverlap
  avCheckEq _ = rangeCheckEq

-- Real numbers  have a lower and upper bound associated with them.
instance Abstractable BaseRealType where
  avJoin _ = ravJoin
  avOverlap _ x y = rangeOverlap (ravRange x) (ravRange y)
  avCheckEq _ = ravCheckEq

-- Bitvectors always have a lower and upper bound (represented as unsigned numbers)
instance (1 <= w) => Abstractable (BaseBVType w) where
  avJoin (BaseBVRepr w) = BVD.union BVD.defaultBVDomainParams w
  avOverlap _ = BVD.domainsOverlap
  avCheckEq _ = BVD.eq

instance Abstractable (BaseFloatType fpp) where
  avJoin _ _ _ = ()
  avOverlap _ _ _ = True
  avCheckEq _ _ _ = Nothing

instance Abstractable BaseComplexType where
  avJoin _ (r1 :+ i1) (r2 :+ i2) = (ravJoin r1 r2) :+ (ravJoin i1 i2)
  avOverlap _ (r1 :+ i1) (r2 :+ i2) = rangeOverlap (ravRange r1) (ravRange r2)
                                   && rangeOverlap (ravRange i1) (ravRange i2)
  avCheckEq _ (r1 :+ i1) (r2 :+ i2)
    = combineEqCheck
        (rangeCheckEq (ravRange r1) (ravRange r2))
        (rangeCheckEq (ravRange i1) (ravRange i2))

instance Abstractable (BaseArrayType idx b) where
  avJoin (BaseArrayRepr _ b) x y = withAbstractable b $ avJoin b x y
  avOverlap (BaseArrayRepr _ b) x y = withAbstractable b $ avOverlap b x y
  avCheckEq (BaseArrayRepr _ b) x y = withAbstractable b $ avCheckEq b x y

combineEqCheck :: Maybe Bool -> Maybe Bool -> Maybe Bool
combineEqCheck (Just False) _ = Just False
combineEqCheck (Just True)  y = y
combineEqCheck _ (Just False) = Just False
combineEqCheck x (Just True)  = x
combineEqCheck _ _            = Nothing

instance Abstractable (BaseStructType ctx) where
  avJoin (BaseStructRepr flds) x y = ctxZipWith3 avJoin' flds x y
  avOverlap (BaseStructRepr flds) x y = Ctx.forIndex (Ctx.size flds) f True
    where f :: Bool -> Ctx.Index ctx tp -> Bool
          f b i = withAbstractable tp (avOverlap tp (unwrapAV u) (unwrapAV v)) && b
            where tp = flds Ctx.! i
                  u  = x Ctx.! i
                  v  = y Ctx.! i

  avCheckEq (BaseStructRepr flds) x y = Ctx.forIndex (Ctx.size flds) f (Just True)
    where f :: Maybe Bool -> Ctx.Index ctx tp -> Maybe Bool
          f b i = combineEqCheck b (withAbstractable tp (avCheckEq tp (unwrapAV u) (unwrapAV v)))
            where tp = flds Ctx.! i
                  u  = x Ctx.! i
                  v  = y Ctx.! i

withAbstractable
   :: BaseTypeRepr bt
   -> (Abstractable bt => a)
   -> a
withAbstractable bt k =
  case bt of
    BaseBoolRepr -> k
    BaseBVRepr _w -> k
    BaseNatRepr -> k
    BaseIntegerRepr -> k
    BaseStringRepr -> k
    BaseRealRepr -> k
    BaseComplexRepr -> k
    BaseArrayRepr _a _b -> k
    BaseStructRepr _flds -> k
    BaseFloatRepr _fpp -> k

-- | Returns true if the concrete value is a member of the set represented
-- by the abstract value.
avContains :: BaseTypeRepr tp -> ConcreteValue tp -> AbstractValue tp -> Bool
avContains tp =
  case tp of
    BaseBoolRepr -> f
      where f _ Nothing = True
            f x (Just y) = x == y
    _ -> withAbstractable tp $ \x y -> avOverlap tp (avSingle tp x) y
