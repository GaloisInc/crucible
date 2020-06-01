{-# Language GADTs, DataKinds, TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language Rank2Types #-}
module Lang.Crucible.Vector
  ( module Data.Parameterized.Vector

    -- ** Bit-vectors
  , fromBV
  , toBV
  , joinVecBV
  , splitVecBV

  ) where

import Prelude hiding (length,zipWith)

import Data.Coerce
import Data.Proxy

import Data.Parameterized.NatRepr
import Data.Parameterized.Vector
import Data.Parameterized.Utils.Endian

import Lang.Crucible.Types
import Lang.Crucible.Syntax (IsExpr(..))
import Lang.Crucible.CFG.Expr ( App( BVConcat, BVSelect ) )

{- | Join the bit-vectors in a vector into a single large bit-vector.
The "Endian" parameter indicates which way to join the elemnts:
"LittleEndian" indicates that low vector indexes are less significant. -}
toBV :: forall f n w.  (1 <= w, IsExpr f) =>
  Endian ->
  NatRepr w ->
  Vector n (f (BVType w)) -> f (BVType (n * w))
toBV endian w xs = ys
  where
  xs' = coerceVec xs

  jn :: (1 <= b) => NatRepr b -> Bits f w -> Bits f b -> Bits f (w + b)
  jn  = case endian of
          LittleEndian -> jnLittle w
          BigEndian    -> jnBig w

  Bits ys = joinWith jn w xs'
{-# Inline toBV #-}

coerceVec :: Coercible a b => Vector n a -> Vector n b
coerceVec = coerce

newtype Bits f n = Bits (f (BVType n))


-- | Earlier indexes are more signficant.
jnBig :: (IsExpr f, 1 <= a, 1 <= b) =>
         NatRepr a -> NatRepr b ->
         Bits f a -> Bits f b -> Bits f (a + b)
jnBig la lb (Bits a) (Bits b) =
  case leqAdd (leqProof (Proxy :: Proxy 1) la) lb of { LeqProof ->
    Bits (app (BVConcat la lb a b)) }
{-# Inline jnBig #-}

-- | Earlier indexes are less signficant.
jnLittle :: (IsExpr f, 1 <= a, 1 <= b) =>
            NatRepr a -> NatRepr b ->
            Bits f a -> Bits f b -> Bits f (a + b)
jnLittle la lb (Bits a) (Bits b) =
  case leqAdd (leqProof (Proxy :: Proxy 1) lb) la of { LeqProof ->
  case plusComm lb la                             of { Refl     ->
    Bits (app (BVConcat lb la b a)) }}
{-# Inline jnLittle #-}

-- | Split a bit-vector into a vector of bit-vectors.
fromBV :: forall f w n.
  (1 <= w, 1 <= n, IsExpr f) =>
  Endian ->
  NatRepr n -> NatRepr w -> f (BVType (n * w)) -> Vector n (f (BVType w))

fromBV e n w xs = coerceVec (splitWith e sel n w (Bits xs))
  where
  sel :: (i + w <= n * w) =>
          NatRepr (n * w) -> NatRepr i -> Bits f (n * w) -> Bits f w
  sel totL i (Bits val) =
    case leqMulPos n w of { LeqProof ->
      Bits (app (BVSelect i w totL val)) }
{-# Inline fromBV #-}

-- | Turn a vector of bit-vectors,
-- into a shorter vector of longer bit-vectors.
joinVecBV :: (IsExpr f, 1 <= i, 1 <= w, 1 <= n) =>
  Endian              {- ^ How to append bit-vectors -} ->
  NatRepr w           {- ^ Width of bit-vectors in input -} ->
  NatRepr i           {- ^ Number of bit-vectors to join togeter -} ->
  Vector (n * i) (f (BVType w)) ->
  Vector n (f (BVType (i * w)))
joinVecBV e w i xs = toBV e w <$> split (divNat (length xs) i) i xs
{-# Inline joinVecBV #-}


-- | Turn a vector of large bit-vectors,
-- into a longer vector of shorter bit-vectors.
splitVecBV :: (IsExpr f, 1 <= i, 1 <= w) =>
  Endian ->
  NatRepr i {- ^ Split bit-vectors in this many parts -} ->
  NatRepr w {- ^ Length of bit-vectors in the result -} ->
  Vector n (f (BVType (i * w))) -> Vector (n*i) (f (BVType w))
splitVecBV e i w xs = join i (fromBV e i w <$> xs)
{-# Inline splitVecBV #-}
