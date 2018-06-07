------------------------------------------------------------------------
-- |
-- Module           : What4.Utils.Complex
-- Description      : Provides a complex representation that is more generic
--                    than Data.Complex.
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides complex numbers without the RealFloat constraints
-- that Data.Complex has.  This is useful for representing various
-- intermediate symbolic representations of complex numbers that are not
-- literally number representations.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module What4.Utils.Complex
  ( Complex((:+))
  , realPart
  , imagPart
  , magnitude
  , magnitudeSq
  , complexNegate
  , complexAdd
  , complexSub
  , complexMul
  , complexDiv
  , complexRecip
  , tryComplexSqrt
  , tryMagnitude
  , complexAsRational
  ) where

import Data.Hashable
import GHC.Generics (Generic)

import Data.Parameterized.Classes

-- | A complex pair over an arbitrary type.
data Complex a = !a :+ !a
  deriving (Eq, Ord, Foldable, Functor, Generic)

infix 6 :+

traverseComplex :: Applicative f => (a -> f b) -> Complex a -> f (Complex b)
traverseComplex = \f (x :+ y) -> (:+) <$> f x <*> f y
{-# INLINE traverseComplex #-}

instance Traversable Complex where
  traverse = traverseComplex

instance Hashable a => Hashable (Complex a) where

instance PolyEq x y => PolyEq (Complex x) (Complex y) where
  polyEqF (rx :+ ix) (ry :+ iy) = do
    Refl <- polyEqF rx ry
    Refl <- polyEqF ix iy
    return Refl

realPart :: Complex a -> a
realPart (a :+ _) = a

imagPart :: Complex a -> a
imagPart (_ :+ b) = b

instance (Eq a, Num a, Show a) => Show (Complex a) where
  show (r :+ 0) = show r
  show (0 :+ i) = show i ++ "i"
  show (r :+ i) = show r ++ " + " ++ show i ++ "i"

complexNegate :: Num a => Complex a -> Complex a
complexNegate (r :+ i) = negate r :+ negate i

complexAdd :: Num a => Complex a -> Complex a -> Complex a
complexAdd (rx :+ ix) (ry :+ iy) = (rx + ry) :+ (ix + iy)

complexSub :: Num a => Complex a -> Complex a -> Complex a
complexSub (rx :+ ix) (ry :+ iy) = (rx - ry) :+ (ix - iy)

{-# SPECIALIZE complexMul :: Complex Rational -> Complex Rational -> Complex Rational #-}
complexMul :: Num a => Complex a -> Complex a -> Complex a
complexMul (rx :+ ix) (ry :+ iy) = (rx * ry - ix * iy) :+ (ix * ry + rx * iy)

instance Floating a => Num (Complex a) where
  (+) = complexAdd
  (-) = complexSub
  negate = complexNegate
  (*) = complexMul
  abs c = magnitude c :+ 0
  signum c@(r :+ i) = r/m :+ i/m
    where m = magnitude c
  fromInteger x = fromInteger x :+ 0

instance (Ord a, Floating a) => Real (Complex a) where
  toRational = error "toRational undefined on complex numbers"

instance Floating a => Fractional (Complex a) where
  fromRational r = fromRational r :+ 0
  recip = complexRecip
  (/) = complexDiv


complexDiv :: Fractional a => Complex a -> Complex a -> Complex a
complexDiv x y = complexMul x (complexRecip y)

complexRecip :: Fractional a => Complex a -> Complex a
complexRecip (r :+ i) = (r/m) :+ (negate i/m)
  where m = r*r + i*i

-- | Returns the "complex argument" of the complex number.
phase :: RealFloat a => Complex a -> a
phase (0 :+ 0)   = 0
phase (x:+y)     = atan2 y x

instance (RealFloat a) => Floating (Complex a) where
  pi             =  pi :+ 0
  exp (x:+y)     =  expx * cos y :+ expx * sin y
    where expx = exp x
  log z          =  log (magnitude z) :+ phase z

  sqrt (0:+0)    =  0
  sqrt (x:+0) | x > 0  = sqrt x :+ 0
              | x == 0 = 0 :+ 0
              | x < 0  = 0 :+ sqrt (-x)
  sqrt (0:+y) | y > 0 = let u = sqrt (y/2) in (u :+ u)
              | y < 0 = let u = sqrt (negate y/2) in (u :+ negate u)
  sqrt z@(x:+y)  =  u :+ (if y < 0 then -v else v)
                      where m = magnitude z
                            u    = sqrt ((m + x) / 2)
                            v    = sqrt ((m - x) / 2)

  sin (x:+y) = (sin x*cosh y) :+ (cos x * sinh y)
  cos (x:+y) = (cos x*cosh y) :+ (- sin x * sinh y)
  tan (x:+y) = (sin_x*cos_x/m) :+ (sinh_y*cosh_y/m)
    where sin_x  = sin x
          cos_x  = cos x
          sinh_y = sinh y
          cosh_y = cosh y
          u = cos_x * cosh_y
          v = sin_x * sinh_y
          m = u*u + v*v



  sinh (x:+y)    =  cos y * sinh x :+ sin y * cosh x
  cosh (x:+y)    =  cos y * cosh x :+ sin y * sinh x
  tanh (x:+y)    =  (cosy*sinhx:+siny*coshx)/(cosy*coshx:+siny*sinhx)
    where siny  = sin y
          cosy  = cos y
          sinhx = sinh x
          coshx = cosh x

  asin z@(x:+y)  =  y':+(-x')
    where  (x':+y') = log (((-y):+x) + sqrt (1 - z*z))
  acos z         =  y'':+(-x'')
    where (x'':+y'') = log (z + ((-y'):+x'))
          (x':+y')   = sqrt (1 - z*z)
  atan z@(x:+y)  =  y':+(-x')
    where (x':+y') = log (((1-y):+x) / sqrt (1+z*z))

  asinh z        =  log (z + sqrt (1+z*z))
  acosh z        =  log (z + (z+1) * sqrt ((z-1)/(z+1)))
  atanh z        =  0.5 * log ((1.0+z) / (1.0-z))

instance (Ord a, Floating a) => RealFrac (Complex a) where
  properFraction = error "properFraction undefined on complex numbers"

magnitude :: Floating a => Complex a -> a
magnitude c = sqrt (magnitudeSq c)

-- | Returns square of magnitude.
magnitudeSq :: Num a => Complex a -> a
magnitudeSq (r :+ i) = r*r+i*i

tryMagnitude :: Num a
             => (a -> b) -- ^ Sqrt function
             -> Complex a
             -> b
tryMagnitude sqrtFn = sqrtFn . magnitudeSq

tryComplexSqrt :: (Ord a, Fractional a, Monad m)
               => (a -> m a) -- ^ Square-root function defined for non-negative values a.
               -> Complex a
               -> m (Complex a)
tryComplexSqrt sqrtFn c = do
  m <- sqrtFn (magnitudeSq c)
  let r = realPart c
      i = imagPart c
  r' <- sqrtFn $ (m + r) / 2
  i' <- sqrtFn $ (m - r) / 2
  let i'' = if (i >= 0) then i' else -i'
  return (r' :+ i'')

complexAsRational :: Complex Rational -> Maybe Rational
complexAsRational (r :+ i) | i == 0 = Just r
                           | otherwise = Nothing
