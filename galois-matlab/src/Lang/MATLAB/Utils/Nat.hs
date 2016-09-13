{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Lang.MATLAB.Utils.Nat
  ( Nat
  , integerAsNat
  , natAsInt
  ) where

import Control.DeepSeq
import Control.Exception (assert)
import Control.Monad
import Data.Hashable
import Data.Vector.Unboxed
import qualified Data.Vector.Generic as GV
import qualified Data.Vector.Generic.Mutable as GMV
import Text.PrettyPrint.ANSI.Leijen (Pretty)

-- | Provides a type large enough to represent any representable
-- array bounds.
--
-- This is a new-type so that we can throw errors when overflow occurs.
newtype Nat = Nat Int
  deriving (Eq, Enum, Hashable, NFData, Ord, Pretty, Real, Integral)

instance Bounded Nat where
  minBound = Nat 0
  maxBound = Nat maxBound

instance Num Nat where
  Nat x + Nat y = assert (z >= x) $ Nat z
    where z = x + y

  Nat x * Nat y = z
   where Just z = integerAsNat (toInteger x * toInteger y)


  Nat x - Nat y = assert (x >= y) (Nat (x - y))
  negate (Nat x) = assert (x == 0) (Nat x)
  abs = id
  signum (Nat x) = Nat (signum x)
  fromInteger x = n
    where Just n = integerAsNat x

instance Show Nat where
  showsPrec p (Nat i) = showsPrec p i

-- | Map integer to natural number if it is one.
integerAsNat :: Monad m => Integer -> m Nat
integerAsNat n
  | 0 <= n && n <= toInteger (maxBound :: Int) = return (Nat (fromInteger n))
  | otherwise = fail "Expected non-negative integer."

-- | Same as `Data.Coerce.coerce`, but allows us to keep the data
--   constructor private to this module for safety.
natAsInt :: Nat -> Int
natAsInt (Nat n) = n
{-# INLINE natAsInt #-}

newtype instance Vector Nat = V_Nat (Vector Int)
newtype instance MVector s Nat = MV_Nat { unMV_Nat :: MVector s Int }

instance Unbox Nat

instance GV.Vector Vector Nat where
  basicUnsafeFreeze v = V_Nat `liftM` GV.basicUnsafeFreeze (unMV_Nat v)
  basicUnsafeThaw (V_Nat v) = MV_Nat `liftM` GV.basicUnsafeThaw v
  basicLength (V_Nat v) = GV.basicLength v
  basicUnsafeSlice i j (V_Nat v) = V_Nat (GV.basicUnsafeSlice i j v)
  basicUnsafeIndexM (V_Nat v) i = Nat `liftM` GV.basicUnsafeIndexM v i
  basicUnsafeCopy (MV_Nat mv) (V_Nat v) = GV.basicUnsafeCopy mv v
  elemseq _ a x = seq a x

instance GMV.MVector MVector Nat where
#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV_Nat v) = GMV.basicInitialize v
#endif
  basicLength (MV_Nat v) = GMV.basicLength v
  basicUnsafeSlice i j (MV_Nat v) = MV_Nat (GMV.basicUnsafeSlice i j v)
  basicOverlaps (MV_Nat u) (MV_Nat v) = GMV.basicOverlaps u v
  basicUnsafeNew n = MV_Nat `liftM` GMV.basicUnsafeNew n
  basicUnsafeReplicate n (Nat v) = MV_Nat `liftM` GMV.basicUnsafeReplicate n v
  basicUnsafeRead (MV_Nat v) i = Nat `liftM` GMV.basicUnsafeRead v i
  basicUnsafeWrite (MV_Nat v) i (Nat e) = GMV.basicUnsafeWrite v i e
  basicClear (MV_Nat v) = GMV.basicClear v
  basicSet (MV_Nat v) (Nat a) = GMV.basicSet v a
  basicUnsafeCopy (MV_Nat t) (MV_Nat s) = GMV.basicUnsafeCopy t s
  basicUnsafeMove (MV_Nat t) (MV_Nat s) = GMV.basicUnsafeMove t s
  basicUnsafeGrow (MV_Nat v) n = MV_Nat `liftM` GMV.basicUnsafeGrow v n
