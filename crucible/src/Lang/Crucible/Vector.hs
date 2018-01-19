{-# Language GADTs, DataKinds, TypeOperators, BangPatterns #-}
{-# Language TypeApplications, ScopedTypeVariables #-}
{-# Language Rank2Types #-}
-- | A vector fixed-size vector of typed elements.
module Lang.Crucible.Vector
  ( Vector

    -- * Construction
  , vecFromList
  , vecFromListUnsafe

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
  , vecJoin
  , vecJoinWith
  , vecSplit

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
  Vector :: (1 <= n) =>
             !(NatRepr n)         {- ^ Number of elements -} ->
             !(Vector.Vector a)   {- ^ The elements -}       ->
              Vector n a


-- | Length of the vector.
-- @O(1)@
vecLenght :: Vector n a -> NatRepr n
vecLenght (Vector n _) = n
{-# INLINE vecLenght #-}

vecElemAt :: ((i+1) <= n) => NatRepr i -> Vector n a -> a
vecElemAt n (Vector _ xs) = xs Vector.! widthVal n

-- | Get the element at the given index.
-- @O(1)@
vecElemAtMaybe :: Int -> Vector n a -> Maybe a
vecElemAtMaybe n (Vector _ xs) = xs Vector.!? n
{-# INLINE vecElemAt #-}

-- | Get the element at the given index.
-- Raises an exception if the element is not in the vector's domain.
-- @O(1)@
vecElemAtUnsafe :: Int -> Vector n a -> a
vecElemAtUnsafe n (Vector _ xs) = xs Vector.! n
{-# INLINE vecElemAtUnsafe #-}

-- | Remove the first element of the vector, and return the rest, if any.
vecUncons :: forall n a.
                  Vector n a -> (a, Either (n :~: 1) (Vector (n-1) a))
vecUncons (Vector n xs) = (Vector.head xs, mbTail)
  where
  mbTail :: Either (n :~: 1) (Vector (n - 1) a)
  mbTail = case testStrictLeq (knownNat @1) n of

             Left n2_leq_n ->
                do LeqProof <- return (leqSub2 n2_leq_n (leqRefl (knownNat @1)))
                   let newLen = subNat n (knownNat @1)
                   return (Vector newLen (Vector.tail xs))

             Right Refl -> Left Refl


-- | Proof that the length of this vector is not 0.
vecNonEmpty :: Vector n a -> LeqProof 1 n
vecNonEmpty (Vector _ _) = LeqProof

--------------------------------------------------------------------------------

-- | Make a vector of the given length and element type.
-- Returns "Nothing" if the input list does not have the right number of
-- elements.
-- @O(n)@.
vecFromList :: (1 <= n) => NatRepr n -> [a] -> Maybe (Vector n a)
vecFromList n xs
  | widthVal n == Vector.length v = Just (Vector n v)
  | otherwise                     = Nothing
  where
  v = Vector.fromList xs
{-# INLINE vecFromList #-}

-- | Make a vector of the given length and element type.
-- The length of the input list is assumed to have the correct length (unche)
-- @O(n)@.
vecFromListUnsafe :: (1 <= n) => NatRepr n -> [a] -> Vector n a
vecFromListUnsafe n xs = Vector n (Vector.fromList xs)
{-# INLINE vecFromListUnsafe #-}



--------------------------------------------------------------------------------

instance Functor (Vector n) where
  fmap f (Vector n xs) = Vector n (Vector.map f xs)

-- | Zip two vectors, potentially changing types.
-- @O(n)@
vecZip :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
vecZip f (Vector n xs) (Vector _ ys) = Vector n (Vector.zipWith f xs ys)
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
vecShuffle f (Vector n xs) = Vector n ys
  where
  ys = Vector.generate (Vector.length xs) (\i -> xs Vector.! f i)


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
vecShiftL x a (Vector n xs) = Vector n ys
  where
  !len = widthVal n
  ys    = Vector.generate len (\i -> let j = i + x
                                     in if j >= len then a else xs Vector.! j)
{-# Inline vecShiftL #-}

{- | Move all elements towards the larger indexes.
Elements that "fall" off the end are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
vecShiftR :: Int -> a -> Vector n a -> Vector n a
vecShiftR !x a (Vector n xs) = Vector n ys
  where
  !len = widthVal n
  ys   = Vector.generate len (\i -> let j = i - x
                                    in if j < 0 then a else xs Vector.! j)
{-# Inline vecShiftR #-}

--------------------------------------------------------------------------------


lemmaMul :: (1 <= n) => p w -> q n -> (w + (n-1) * w) :~: (n * w)
lemmaMul = unsafeCoerce Refl

{- | Join the bit-vectors in a vector into a single large bit-vector.
The "Endian" parameter indicates which way to join the elemnts:
"LittleEndian" indicates that low vector indexes are less significant. -}
vecJoin :: forall f n w.  (1 <= w, IsExpr f) =>
            Endian ->  NatRepr w -> Vector n (f (BVType w)) -> f (BVType (n * w))
vecJoin endian w xs = ys
  where
  xs' = coerceVec xs

  jn :: (1 <= b) => NatRepr b -> Bits f w -> Bits f b -> Bits f (w + b)
  jn  = case endian of
          LittleEndian -> jnLittle w
          BigEndian    -> jnBig w

  Bits ys = vecJoinWith jn w xs'

coerceVec :: Coercible a b => Vector n a -> Vector n b
coerceVec = coerce

newtype Bits f n = Bits (f (BVType n))


jnBig :: (IsExpr f, 1 <= a, 1 <= b) =>
         NatRepr a -> NatRepr b ->
         Bits f a -> Bits f b -> Bits f (a + b)
jnBig la lb (Bits a) (Bits b) =
  case leqAdd (leqProof (Proxy :: Proxy 1) la) lb of { LeqProof ->
    Bits (app (BVConcat la lb a b)) }

jnLittle :: (IsExpr f, 1 <= a, 1 <= b) =>
            NatRepr a -> NatRepr b ->
            Bits f a -> Bits f b -> Bits f (a + b)
jnLittle la lb (Bits a) (Bits b) =
  case leqAdd (leqProof (Proxy :: Proxy 1) lb) la of { LeqProof ->
  case plusComm lb la                             of { Refl     ->
    Bits (app (BVConcat lb la b a)) }}


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
vecSplit :: forall f w n.
  (IsExpr f, 1 <= w, 1 <= n) =>
  NatRepr n -> NatRepr w -> f (BVType (n * w)) -> Vector n (f (BVType w))

vecSplit n w xs = coerceVec (vecSplitWith sel n w (Bits xs))
  where
  sel :: (i + w <= n * w) =>
          NatRepr (n * w) -> NatRepr i -> Bits f (n * w) -> Bits f w
  sel totL i (Bits val) =
    case leqMulPos n w of { LeqProof ->
       Bits (app (BVSelect i w totL val)) }
{-# Inline vecSplit #-}


-- | Split a bit-vector into a vector of bit-vectors.
vecSplitWith :: forall f w n.
  (1 <= w, 1 <= n) =>
  (forall i. (i + w <= n * w) =>
             NatRepr (n * w) -> NatRepr i -> f (n * w) -> f w) ->
  NatRepr n -> NatRepr w -> f (n * w) -> Vector n (f w)
vecSplitWith select n w val = Vector n (Vector.create initializer)
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




-- vecJoinVec :: Vector (n * i) (f (BVType w)) -> Vector n (f (BVType (i * w)))
-- vecSplitVec :: Vector n (f (BVType (i * w)) -> Vector (n*i) (f (BVType w))


