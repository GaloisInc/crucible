{-# Language GADTs, DataKinds, TypeOperators, BangPatterns #-}
{-# Language TypeApplications, ScopedTypeVariables #-}
{-# Language Rank2Types #-}
-- | A vector fixed-size vector of typed elements.
module Lang.Crucible.Vector
  ( Vector

    -- * Lists
  , fromList
  , toList

    -- * Length
  , length
  , nonEmpty
  , lengthInt

  -- * Indexing
  , elemAt
  , elemAtMaybe
  , elemAtUnsafe

  -- * Update
  , insertAt
  , insertAtMaybe

    -- * Sub sequences
  , uncons
  , slice

    -- * Zipping
  , zipWith

    -- * Reorder
  , shuffle
  , rotateL
  , rotateR
  , shiftL
  , shiftR

    -- * Splitting and joining
    -- * General
  , joinWith
  , splitWith

    -- ** Bit-vectors
  , fromBV
  , toBV
  , joinVecBV
  , splitVecBV

    -- ** Vectors
  , split
  , join
  , append

  ) where

import qualified Data.Vector as Vector
import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MVector
import Control.Monad.ST
import Data.Parameterized.NatRepr
import Data.Proxy
import Unsafe.Coerce
import Data.Coerce
import Prelude hiding (length,zipWith)

import Lang.Crucible.Types
import Lang.Crucible.Syntax
import Lang.Crucible.CFG.Expr
import Lang.Crucible.Utils.Endian

-- | Fixed-size non-empty vectors.
data Vector n a where
  Vector :: (1 <= n) => !(Vector.Vector a) -> Vector n a

-- | Get the elements of the vector as a list, lowest index first.
toList :: Vector n a -> [a]
toList (Vector v) = Vector.toList v
{-# Inline toList #-}

-- | Length of the vector.
-- @O(1)@
length :: Vector n a -> NatRepr n
length (Vector xs) = unsafeCoerce (fromIntegral (Vector.length xs) :: Integer)
{-# INLINE length #-}

-- | The length of the vector as an "Int".
lengthInt :: Vector n a -> Int
lengthInt (Vector xs) = Vector.length xs
{-# Inline lengthInt #-}

elemAt :: ((i+1) <= n) => NatRepr i -> Vector n a -> a
elemAt n (Vector xs) = xs Vector.! widthVal n

-- | Get the element at the given index.
-- @O(1)@
elemAtMaybe :: Int -> Vector n a -> Maybe a
elemAtMaybe n (Vector xs) = xs Vector.!? n
{-# INLINE elemAt #-}

-- | Get the element at the given index.
-- Raises an exception if the element is not in the vector's domain.
-- @O(1)@
elemAtUnsafe :: Int -> Vector n a -> a
elemAtUnsafe n (Vector xs) = xs Vector.! n
{-# INLINE elemAtUnsafe #-}


-- | Insert an element at the given vector position.
-- @O(n)@.
insertAt :: ((i + 1) <= n) => NatRepr i -> a -> Vector n a -> Vector n a
insertAt n a (Vector xs) = Vector (Vector.unsafeUpd xs [(widthVal n,a)])

-- | Insert an element at the given index.
-- Return 'Nothing' if the element is outside the vector bounds.
insertAtMaybe :: Int -> a -> Vector n a -> Maybe (Vector n a)
insertAtMaybe n a (Vector xs)
  | 0 <= n && n < Vector.length xs =
                              Just (Vector (Vector.unsafeUpd xs [(n,a)]))
  | otherwise = Nothing





-- | Proof that the length of this vector is not 0.
nonEmpty :: Vector n a -> LeqProof 1 n
nonEmpty (Vector _) = LeqProof
{-# Inline nonEmpty #-}



-- | Remove the first element of the vector, and return the rest, if any.
uncons :: forall n a.  Vector n a -> (a, Either (n :~: 1) (Vector (n-1) a))
uncons v@(Vector xs) = (Vector.head xs, mbTail)
  where
  mbTail :: Either (n :~: 1) (Vector (n - 1) a)
  mbTail = case testStrictLeq (knownNat @1) (length v) of
             Left n2_leq_n ->
               do LeqProof <- return (leqSub2 n2_leq_n (leqRefl (knownNat @1)))
                  return (Vector (Vector.tail xs))
             Right Refl    -> Left Refl
{-# Inline uncons #-}


--------------------------------------------------------------------------------

-- | Make a vector of the given length and element type.
-- Returns "Nothing" if the input list does not have the right number of
-- elements.
-- @O(n)@.
fromList :: (1 <= n) => NatRepr n -> [a] -> Maybe (Vector n a)
fromList n xs
  | widthVal n == Vector.length v = Just (Vector v)
  | otherwise                     = Nothing
  where
  v = Vector.fromList xs
{-# INLINE fromList #-}


-- | Extract a subvector of the given vector.
slice :: (i + w <= n, 1 <= w) =>
            NatRepr i {- ^ Start index -} ->
            NatRepr w {- ^ Width of sub-vector -} ->
            Vector n a -> Vector w a
slice i w (Vector xs) = Vector (Vector.slice (widthVal i) (widthVal w) xs)
{-# INLINE slice #-}




--------------------------------------------------------------------------------

instance Functor (Vector n) where
  fmap f (Vector xs) = Vector (Vector.map f xs)
  {-# Inline fmap #-}

instance Foldable (Vector n) where
  foldMap f (Vector xs) = foldMap f xs

instance Traversable (Vector n) where
  traverse f (Vector xs) = Vector <$> traverse f xs
  {-# Inline traverse #-}

-- | Zip two vectors, potentially changing types.
-- @O(n)@
zipWith :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith f (Vector xs) (Vector ys) = Vector (Vector.zipWith f xs ys)
{-# INLINE zipWith #-}


--------------------------------------------------------------------------------

{- | Move the elements around, as specified by the given function.
  * Note: the reindexing function says where each of the elements
          in the new vector come from.
  * Note: it is OK for the same input element to end up in mulitple places
          in the result.
@O(n)@
-}
shuffle :: (Int -> Int) -> Vector n a -> Vector n a
shuffle f (Vector xs) = Vector ys
  where
  ys = Vector.generate (Vector.length xs) (\i -> xs Vector.! f i)
{-# Inline shuffle #-}


-- | Rotate "left".  The first element of the vector is on the "left", so
-- rotate left moves all elemnts toward the corresponding smaller index.
-- Elements that fall off the beginning end up at the end.
rotateL :: Int -> Vector n a -> Vector n a
rotateL !n xs = shuffle rotL xs
  where
  !len   = lengthInt xs
  rotL i = (i + n) `mod` len          -- `len` is known to be >= 1
{-# Inline rotateL #-}

-- | Rotate "right".  The first element of the vector is on the "left", so
-- rotate right moves all elemnts toward the corresponding larger index.
-- Elements that fall off the end, end up at the beginning.
rotateR :: Int -> Vector n a -> Vector n a
rotateR !n xs = shuffle rotR xs
  where
  !len   = lengthInt xs
  rotR i = (i - n) `mod` len        -- `len` is known to be >= 1
{-# Inline rotateR #-}

{- | Move all elements towards smaller indexes.
Elements that fall off the front are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
shiftL :: Int -> a -> Vector n a -> Vector n a
shiftL !x a (Vector xs) = Vector ys
  where
  !len = Vector.length xs
  ys   = Vector.generate len (\i -> let j = i + x
                                    in if j >= len then a else xs Vector.! j)
{-# Inline shiftL #-}

{- | Move all elements towards the larger indexes.
Elements that "fall" off the end are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
shiftR :: Int -> a -> Vector n a -> Vector n a
shiftR !x a (Vector xs) = Vector ys
  where
  !len = Vector.length xs
  ys   = Vector.generate len (\i -> let j = i - x
                                    in if j < 0 then a else xs Vector.! j)
{-# Inline shiftR #-}

-------------------------------------------------------------------------------i

append :: Vector m a -> Vector n a -> Vector (m + n) a
append v1@(Vector xs) v2@(Vector ys) =
  case leqAddPos (length v1) (length v2) of { LeqProof ->
    Vector (xs Vector.++ ys)
  }
{-# Inline append #-}


--------------------------------------------------------------------------------


lemmaMul :: (1 <= n) => p w -> q n -> (w + (n-1) * w) :~: (n * w)
lemmaMul = unsafeCoerce Refl

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
joinWith ::
  forall f n w.
  (1 <= w) =>
  (forall l. (1 <= l) => NatRepr l -> f w -> f l -> f (w + l)) ->
  NatRepr w -> Vector n (f w) -> f (n * w)

joinWith jn w = fst . go
  where
  go :: forall l. Vector l (f w) -> (f (l * w), NatRepr (l * w))
  go exprs =
    case uncons exprs of
      (a, Left Refl) -> (a, w)
      (a, Right rest) ->
        case nonEmpty rest                of { LeqProof ->
        case leqMulPos (length rest) w    of { LeqProof ->
        case nonEmpty exprs               of { LeqProof ->
        case lemmaMul w (length exprs)    of { Refl ->
        let (res,sz) = go rest            in
          (jn sz a res, addNat w sz) }}}}
{-# Inline joinWith #-}


-- | Split a bit-vector into a vector of bit-vectors.
fromBV :: forall f w n.
  (IsExpr f, 1 <= w, 1 <= n) =>
  NatRepr n -> NatRepr w -> f (BVType (n * w)) -> Vector n (f (BVType w))

fromBV n w xs = coerceVec (splitWith sel n w (Bits xs))
  where
  sel :: (i + w <= n * w) =>
          NatRepr (n * w) -> NatRepr i -> Bits f (n * w) -> Bits f w
  sel totL i (Bits val) =
    case leqMulPos n w of { LeqProof ->
       Bits (app (BVSelect i w totL val)) }
{-# Inline fromBV #-}


-- | Split a bit-vector into a vector of bit-vectors.
splitWith :: forall f w n.
  (1 <= w, 1 <= n) =>
  (forall i. (i + w <= n * w) =>
             NatRepr (n * w) -> NatRepr i -> f (n * w) -> f w) ->
  NatRepr n -> NatRepr w -> f (n * w) -> Vector n (f w)
splitWith select n w val = Vector (Vector.create initializer)
  where
  initializer :: forall s. ST s (MVector s (f w))
  initializer =
    do LeqProof <- return (leqMulPos n w)
       LeqProof <- return (leqMulMono n w)

       v <- MVector.new (widthVal n)
       let fill :: Int -> NatRepr i -> ST s ()
           fill loc i =
             let end = addNat i w in
             case testLeq end inLen of
               Just LeqProof ->
                 do MVector.write v loc (select inLen i val)
                    fill (loc + 1) end
               Nothing -> return ()


       fill 0 (knownNat @0)
       return v

  inLen :: NatRepr (n * w)
  inLen = natMultiply n w
{-# Inline splitWith #-}


newtype Vec a n = Vec (Vector n a)

vSlice :: (i + w <= l, 1 <= w) =>
  NatRepr w -> NatRepr l -> NatRepr i -> Vec a l -> Vec a w
vSlice w _ i (Vec xs) = Vec (slice i w xs)
{-# Inline vSlice #-}

vAppend :: NatRepr n -> Vec a m -> Vec a n -> Vec a (m + n)
vAppend _ (Vec xs) (Vec ys) = Vec (append xs ys)
{-# Inline vAppend #-}

-- | Split a vector into a vector of vectors.
split :: (1 <= w, 1 <= n) =>
        NatRepr n -> NatRepr w -> Vector (n * w) a -> Vector n (Vector w a)
split n w xs = coerceVec (splitWith (vSlice w) n w (Vec xs))
{-# Inline split #-}

-- | Join a vector of vectors into a single vector.
join :: (1 <= w) => NatRepr w -> Vector n (Vector w a) -> Vector (n * w) a
join w xs = ys
  where Vec ys = joinWith vAppend w (coerceVec xs)
{-# Inline join #-}



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
  NatRepr i {- ^ Split bit-vectors in this many parts -} ->
  NatRepr w {- ^ Length of bit-vectors in the result -} ->
  Vector n (f (BVType (i * w))) -> Vector (n*i) (f (BVType w))
splitVecBV i w xs = join i (fromBV i w <$> xs)
{-# Inline splitVecBV #-}


