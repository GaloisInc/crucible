{-# Language GADTs, DataKinds, TypeOperators, BangPatterns #-}
{-# Language TypeApplications, ScopedTypeVariables #-}
{-# Language Rank2Types #-}
-- | A vector fixed-size vector of typed elements.
module Lang.Crucible.Vector
  ( Vector

    -- * Construction
  , vecFromList
  , vecFromBV
  , vecSlice

    -- * Query
  , vecLenght
  , vecElemAt
  , vecElemAtMaybe
  , vecElemAtUnsafe
  , vecUncons

    -- * Maps
  , vecZip

    -- * Reorder
  , vecShuffle
  , vecRotateL
  , vecRotateR
  , vecShiftL
  , vecShiftR

    -- * Splitting and joining
  , vecJoinWith
  , vecSplitWith

  , vecJoinBV
  , vecJoinVecBV
  , vecSplitVecBV

  , vecSplit
  , vecJoin

  ) where

import qualified Data.Vector as Vector
import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MVector
import Control.Monad.ST
import Data.Parameterized.NatRepr
import Data.Proxy
import Unsafe.Coerce
import Data.Coerce

import Lang.Crucible.Types
import Lang.Crucible.Syntax
import Lang.Crucible.CFG.Expr
import Lang.Crucible.Utils.Endian

-- | Fixed-size non-empty vectors.
data Vector n a where
  Vector :: (1 <= n) => !(Vector.Vector a) -> Vector n a


-- | Length of the vector.
-- @O(1)@
vecLenght :: Vector n a -> NatRepr n
vecLenght (Vector xs) =
  unsafeCoerce (fromIntegral (Vector.length xs) :: Integer)
{-# INLINE vecLenght #-}

vecElemAt :: ((i+1) <= n) => NatRepr i -> Vector n a -> a
vecElemAt n (Vector xs) = xs Vector.! widthVal n

-- | Get the element at the given index.
-- @O(1)@
vecElemAtMaybe :: Int -> Vector n a -> Maybe a
vecElemAtMaybe n (Vector xs) = xs Vector.!? n
{-# INLINE vecElemAt #-}

-- | Get the element at the given index.
-- Raises an exception if the element is not in the vector's domain.
-- @O(1)@
vecElemAtUnsafe :: Int -> Vector n a -> a
vecElemAtUnsafe n (Vector xs) = xs Vector.! n
{-# INLINE vecElemAtUnsafe #-}

-- | Proof that the length of this vector is not 0.
vecNonEmpty :: Vector n a -> LeqProof 1 n
vecNonEmpty (Vector _) = LeqProof
{-# Inline vecNonEmpty #-}



-- | Remove the first element of the vector, and return the rest, if any.
vecUncons :: forall n a.
                  Vector n a -> (a, Either (n :~: 1) (Vector (n-1) a))
vecUncons v@(Vector xs) = (Vector.head xs, mbTail)
  where
  n = vecLenght v

  mbTail :: Either (n :~: 1) (Vector (n - 1) a)
  mbTail = case testStrictLeq (knownNat @1) n of
             Left n2_leq_n ->
               do LeqProof <- return (leqSub2 n2_leq_n (leqRefl (knownNat @1)))
                  return (Vector (Vector.tail xs))
             Right Refl    -> Left Refl
{-# Inline vecUncons #-}


--------------------------------------------------------------------------------

-- | Make a vector of the given length and element type.
-- Returns "Nothing" if the input list does not have the right number of
-- elements.
-- @O(n)@.
vecFromList :: (1 <= n) => NatRepr n -> [a] -> Maybe (Vector n a)
vecFromList n xs
  | widthVal n == Vector.length v = Just (Vector v)
  | otherwise                     = Nothing
  where
  v = Vector.fromList xs
{-# INLINE vecFromList #-}


-- | Extract a subvector of the given vector.
vecSlice :: (i + w <= n, 1 <= w) =>
            NatRepr i {- ^ Start index -} ->
            NatRepr w {- ^ Width of sub-vector -} ->
            Vector n a -> Vector w a
vecSlice i w (Vector xs) = Vector (Vector.slice (widthVal i) (widthVal w) xs)
{-# INLINE vecSlice #-}




--------------------------------------------------------------------------------

instance Functor (Vector n) where
  fmap f (Vector xs) = Vector (Vector.map f xs)
  {-# Inline fmap #-}

-- | Zip two vectors, potentially changing types.
-- @O(n)@
vecZip :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
vecZip f (Vector xs) (Vector ys) = Vector (Vector.zipWith f xs ys)
{-# INLINE vecZip #-}


--------------------------------------------------------------------------------

{- | Move the elements around, as specified by the given function.
  * Note: the reindexing function says where each of the elements
          in the new vector come from.
  * Note: it is OK for the same input element to end up in mulitple places
          in the result.
@O(n)@
-}
vecShuffle :: (Int -> Int) -> Vector n a -> Vector n a
vecShuffle f (Vector xs) = Vector ys
  where
  ys = Vector.generate (Vector.length xs) (\i -> xs Vector.! f i)
{-# Inline vecShuffle #-}


-- | Rotate "left".  The first element of the vector is on the "left", so
-- rotate left moves all elemnts toward the corresponding smaller index.
-- Elements that fall off the beginning end up at the end.
vecRotateL :: Int -> Vector n a -> Vector n a
vecRotateL !n xs = vecShuffle rotL xs
  where
  !len   = widthVal (vecLenght xs)
  rotL i = (i + n) `mod` len          -- `len` is known to be >= 1
{-# Inline vecRotateL #-}

-- | Rotate "right".  The first element of the vector is on the "left", so
-- rotate right moves all elemnts toward the corresponding larger index.
-- Elements that fall off the end, end up at the beginning.
vecRotateR :: Int -> Vector n a -> Vector n a
vecRotateR !n xs = vecShuffle rotR xs
  where
  !len   = widthVal (vecLenght xs)
  rotR i = (i - n) `mod` len        -- `len` is known to be >= 1
{-# Inline vecRotateR #-}

{- | Move all elements towards smaller indexes.
Elements that "fall" off the front are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
vecShiftL :: Int -> a -> Vector n a -> Vector n a
vecShiftL x a (Vector xs) = Vector ys
  where
  !len = Vector.length xs
  ys    = Vector.generate len (\i -> let j = i + x
                                     in if j >= len then a else xs Vector.! j)
{-# Inline vecShiftL #-}

{- | Move all elements towards the larger indexes.
Elements that "fall" off the end are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
vecShiftR :: Int -> a -> Vector n a -> Vector n a
vecShiftR !x a (Vector xs) = Vector ys
  where
  !len = Vector.length xs
  ys   = Vector.generate len (\i -> let j = i - x
                                    in if j < 0 then a else xs Vector.! j)
{-# Inline vecShiftR #-}

-------------------------------------------------------------------------------i

vecAppend :: Vector m a -> Vector n a -> Vector (m + n) a
vecAppend v1@(Vector xs) v2@(Vector ys) =
  case leqAddPos (vecLenght v1) (vecLenght v2) of { LeqProof ->
    Vector (xs Vector.++ ys)
  }
{-# Inline vecAppend #-}


--------------------------------------------------------------------------------


lemmaMul :: (1 <= n) => p w -> q n -> (w + (n-1) * w) :~: (n * w)
lemmaMul = unsafeCoerce Refl

{- | Join the bit-vectors in a vector into a single large bit-vector.
The "Endian" parameter indicates which way to join the elemnts:
"LittleEndian" indicates that low vector indexes are less significant. -}
vecJoinBV :: forall f n w.  (1 <= w, IsExpr f) =>
  Endian ->
  NatRepr w ->
  Vector n (f (BVType w)) -> f (BVType (n * w))
vecJoinBV endian w xs = ys
  where
  xs' = coerceVec xs

  jn :: (1 <= b) => NatRepr b -> Bits f w -> Bits f b -> Bits f (w + b)
  jn  = case endian of
          LittleEndian -> jnLittle w
          BigEndian    -> jnBig w

  Bits ys = vecJoinWith jn w xs'
{-# Inline vecJoinBV #-}

coerceVec :: Coercible a b => Vector n a -> Vector n b
coerceVec = coerce

newtype Bits f n = Bits (f (BVType n))


jnBig :: (IsExpr f, 1 <= a, 1 <= b) =>
         NatRepr a -> NatRepr b ->
         Bits f a -> Bits f b -> Bits f (a + b)
jnBig la lb (Bits a) (Bits b) =
  case leqAdd (leqProof (Proxy :: Proxy 1) la) lb of { LeqProof ->
    Bits (app (BVConcat la lb a b)) }
{-# Inline jnBig #-}

jnLittle :: (IsExpr f, 1 <= a, 1 <= b) =>
            NatRepr a -> NatRepr b ->
            Bits f a -> Bits f b -> Bits f (a + b)
jnLittle la lb (Bits a) (Bits b) =
  case leqAdd (leqProof (Proxy :: Proxy 1) lb) la of { LeqProof ->
  case plusComm lb la                             of { Refl     ->
    Bits (app (BVConcat lb la b a)) }}
{-# Inline jnLittle #-}


-- | Join a vector of values, using the given function.
vecJoinWith ::
  forall f n w.
  (1 <= w) =>
  (forall l. (1 <= l) => NatRepr l -> f w -> f l -> f (w + l)) ->
  NatRepr w -> Vector n (f w) -> f (n * w)

vecJoinWith jn w = fst . go
  where
  go :: forall l. Vector l (f w) -> (f (l * w), NatRepr (l * w))
  go exprs =
    case vecUncons exprs of
      (a, Left Refl) -> (a, w)
      (a, Right rest) ->
        let vLen = vecLenght rest         in
        case vecNonEmpty rest             of { LeqProof ->
        case leqMulPos vLen w             of { LeqProof ->
        case vecNonEmpty exprs            of { LeqProof ->
        case lemmaMul w (vecLenght exprs) of { Refl ->
        let (res,sz) = go rest            in
          (jn sz a res, addNat w sz) }}}}
{-# Inline vecJoinWith #-}


-- | Split a bit-vector into a vector of bit-vectors.
vecFromBV :: forall f w n.
  (IsExpr f, 1 <= w, 1 <= n) =>
  NatRepr n -> NatRepr w -> f (BVType (n * w)) -> Vector n (f (BVType w))

vecFromBV n w xs = coerceVec (vecSplitWith sel n w (Bits xs))
  where
  sel :: (i + w <= n * w) =>
          NatRepr (n * w) -> NatRepr i -> Bits f (n * w) -> Bits f w
  sel totL i (Bits val) =
    case leqMulPos n w of { LeqProof ->
       Bits (app (BVSelect i w totL val)) }
{-# Inline vecFromBV #-}


-- | Split a bit-vector into a vector of bit-vectors.
vecSplitWith :: forall f w n.
  (1 <= w, 1 <= n) =>
  (forall i. (i + w <= n * w) =>
             NatRepr (n * w) -> NatRepr i -> f (n * w) -> f w) ->
  NatRepr n -> NatRepr w -> f (n * w) -> Vector n (f w)
vecSplitWith select n w val = Vector (Vector.create initializer)
  where
  initializer :: forall s. ST s (MVector s (f w))
  initializer =
    do LeqProof <- return (leqMulPos n w)
       LeqProof <- return (leqMulMono n w)

       v <- MVector.new (widthVal n)
       let fill :: NatRepr i -> ST s ()
           fill i =
             let end = addNat i w in
             case testLeq end inLen of
               Just LeqProof ->
                 do MVector.write v (widthVal n) (select inLen i val)
                    fill end
               Nothing -> return ()


       fill (knownNat @0)
       return v

  inLen :: NatRepr (n * w)
  inLen = natMultiply n w
{-# Inline vecSplitWith #-}


newtype Vec a n = Vec (Vector n a)

vSlice :: (i + w <= l, 1 <= w) =>
  NatRepr w -> NatRepr l -> NatRepr i -> Vec a l -> Vec a w
vSlice w _ i (Vec xs) = Vec (vecSlice i w xs)
{-# Inline vSlice #-}

vAppend :: NatRepr n -> Vec a m -> Vec a n -> Vec a (m + n)
vAppend _ (Vec xs) (Vec ys) = Vec (vecAppend xs ys)
{-# Inline vAppend #-}

-- | Split a vector into a vector of vectors.
vecSplit :: (1 <= w, 1 <= n) =>
        NatRepr n -> NatRepr w -> Vector (n * w) a -> Vector n (Vector w a)
vecSplit n w xs = coerceVec (vecSplitWith (vSlice w) n w (Vec xs))
{-# Inline vecSplit #-}

-- | Join a vector of vectors into a single vector.
vecJoin :: (1 <= w) => NatRepr w -> Vector n (Vector w a) -> Vector (n * w) a
vecJoin w xs = ys
  where Vec ys = vecJoinWith vAppend w (coerceVec xs)
{-# Inline vecJoin #-}



-- | Turn a vector of bit-vectors,
-- into a shorter vector of longer bit-vectors.
vecJoinVecBV :: (IsExpr f, 1 <= i, 1 <= w, 1 <= n) =>
  Endian              {- ^ How to append bit-vectors -} ->
  NatRepr w           {- ^ Width of bit-vectors in input -} ->
  NatRepr i           {- ^ Number of bit-vectors to join togeter -} ->
  Vector (n * i) (f (BVType w)) ->
  Vector n (f (BVType (i * w)))
vecJoinVecBV e w i xs =
  vecJoinBV e w <$> vecSplit (divNat (vecLenght xs) i) i xs
{-# Inline vecJoinVecBV #-}


-- | Turn a vector of large bit-vectors,
-- into a longer vector of shorter bit-vectors.
vecSplitVecBV :: (IsExpr f, 1 <= i, 1 <= w) =>
  NatRepr i {- ^ Split bit-vectors in this many parts -} ->
  NatRepr w {- ^ Length of bit-vectors in the result -} ->
  Vector n (f (BVType (i * w))) -> Vector (n*i) (f (BVType w))
vecSplitVecBV i w xs = vecJoin i (vecFromBV i w <$> xs)
{-# Inline vecSplitVecBV #-}


