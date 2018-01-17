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
  , vecElemType
  , vecLenght
  , vecElemAt
  , vecElemAtMaybe
  , vecElemAtUnsafe
  , vecUncons

    -- * Maps
  , vecMapPoly
  , vecMap
  , vecZipPoly
  , vecZip

    -- * Reorder
  , vecShuffle
  , vecRotateL
  , vecRotateR
  , vecShiftL
  , vecShiftR

  ) where

import qualified Data.Vector as Vector
import Data.Parameterized.NatRepr
import Data.Proxy
import Unsafe.Coerce

import Lang.Crucible.Types
import Lang.Crucible.Syntax

-- | Fixed-size non-empty vectors.
data Vector f n tp where
  Vector :: (1 <= n) =>
             !(NatRepr n)              {- ^ Number of elements -} ->
             !(TypeRepr tp)            {- ^ Type of elements -}   ->
             !(Vector.Vector (f tp))   {- ^ The elements -}       ->
              Vector f n tp


-- | Type of elemtns of the vector.
-- @O(1)@
vecElemType :: Vector f n a -> TypeRepr a
vecElemType (Vector _ t _) = t
{-# INLINE vecElemType #-}

-- | Length of the vector.
-- @O(1)@
vecLenght :: Vector f n a -> NatRepr n
vecLenght (Vector n _ _) = n
{-# INLINE vecLenght #-}

vecElemAt :: ((i+1) <= n) => NatRepr i -> Vector f n a -> f a
vecElemAt n (Vector _ _ xs) = xs Vector.! widthVal n

-- | Get the element at the given index.
-- @O(1)@
vecElemAtMaybe :: Int -> Vector f n a -> Maybe (f a)
vecElemAtMaybe n (Vector _ _ xs) = xs Vector.!? n
{-# INLINE vecElemAt #-}

-- | Get the element at the given index.
-- Raises an exception if the element is not in the vector's domain.
-- @O(1)@
vecElemAtUnsafe :: Int -> Vector f n a -> f a
vecElemAtUnsafe n (Vector _ _ xs) = xs Vector.! n
{-# INLINE vecElemAtUnsafe #-}

-- | Remove the first element of the vector, and return the rest, if any.
vecUncons :: forall f n a.
                  Vector f n a -> (f a, Either (n :~: 1) (Vector f (n-1) a))
vecUncons (Vector n t xs) = (Vector.head xs, mbTail)
  where
  mbTail :: Either (n :~: 1) (Vector f (n - 1) a)
  mbTail = case testStrictLeq (knownNat @1) n of

             Left n2_leq_n ->
                do LeqProof <- return (leqSub2 n2_leq_n (leqRefl (knownNat @1)))
                   let newLen = subNat n (knownNat @1)
                   return (Vector newLen t (Vector.tail xs))

             Right Refl -> Left Refl


-- | Proof that the length of this vector is not 0.
vecNonEmpty :: Vector f n a -> LeqProof 1 n
vecNonEmpty (Vector _ _ _) = LeqProof

--------------------------------------------------------------------------------

-- | Make a vector of the given length and element type.
-- Returns "Nothing" if the input list does not have the right number of
-- elements.
-- @O(n)@.
vecFromList :: (1 <= n) =>
               NatRepr n -> TypeRepr tp -> [f tp] -> Maybe (Vector f n tp)
vecFromList n tp xs
  | widthVal n == Vector.length v = Just (Vector n tp v)
  | otherwise                     = Nothing
  where
  v = Vector.fromList xs
{-# INLINE vecFromList #-}

-- | Make a vector of the given length and element type.
-- The length of the input list is assumed to have the correct length (unche)
-- @O(n)@.
vecFromListUnsafe :: (1 <= n) =>
                     NatRepr n -> TypeRepr tp -> [f tp] -> Vector f n tp
vecFromListUnsafe n tp xs = Vector n tp (Vector.fromList xs)
{-# INLINE vecFromListUnsafe #-}



--------------------------------------------------------------------------------

-- | Apply a function to each element of a vector,
-- potentially changing the type.
-- @O(n)@
vecMapPoly :: TypeRepr b            {- ^ Result type -} ->
              (f a -> f b)          {- ^ Change elements -} ->
              Vector f n a -> Vector f n b
vecMapPoly b f (Vector n _ xs) = Vector n b (Vector.map f xs)
{-# INLINE vecMapPoly #-}

-- | Apply a function to each element of a vector,
-- without changing the type.
-- A special case of "vecMapPoly".
-- @O(n)@
vecMap :: (f a -> f a) -> Vector f n a -> Vector f n a
vecMap f xs = vecMapPoly (vecElemType xs) f xs
{-# INLINE vecMap #-}


-- | Zip two vectors, potentially changing types.
-- @O(n)@
vecZipPoly :: TypeRepr c          {- ^ Result type -} ->
             (f a -> f b -> f c)  {- ^ Combining function -} ->
             Vector f n a -> Vector f n b -> Vector f n c
vecZipPoly c f (Vector n _ xs) (Vector _ _ ys) =
  Vector n c (Vector.zipWith f xs ys)
{-# INLINE vecZipPoly #-}

-- | Zip two vectors without changing types.
-- A common special case of "vecZipPoly".
-- @O(n)@
vecZip :: (f a -> f a -> f a) ->
          Vector f n a -> Vector f n a -> Vector f n a
vecZip f xs ys = vecZipPoly (vecElemType xs) f xs ys

--------------------------------------------------------------------------------

{- | Move the elements around, as specified by the given function.
  * Note: the reindexing function says where each of the elements
          in the new vector come from.
  * Note: it is OK for the same input element to end up in mulitple places
          in the result.
@O(n)@
-}
vecShuffle :: (Int -> Int) -> Vector f n a -> Vector f n a
vecShuffle f (Vector n tp xs) = Vector n tp ys
  where
  ys = Vector.generate (Vector.length xs) (\i -> xs Vector.! f i)


-- | Rotate "left".  The first element of the vector is on the "left", so
-- rotate left moves all elemnts toward the corresponding smaller index.
-- Elements that fall off the beginning end up at the end.
vecRotateL :: Int -> Vector f n a -> Vector f n a
vecRotateL !n xs = vecShuffle rotL xs
  where
  !len   = widthVal (vecLenght xs)
  rotL i = (i + n) `mod` len          -- `len` is known to be >= 1
{-# Inline vecRotateL #-}

-- | Rotate "right".  The first element of the vector is on the "left", so
-- rotate right moves all elemnts toward the corresponding larger index.
-- Elements that fall off the end, end up at the beginning.
vecRotateR :: Int -> Vector f n a -> Vector f n a
vecRotateR !n xs = vecShuffle rotR xs
  where
  !len   = widthVal (vecLenght xs)
  rotR i = (i - n) `mod` len        -- `len` is known to be >= 1
{-# Inline vecRotateR #-}

{- | Move all elements towards smaller indexes.
Elements that "fall" off the front are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
vecShiftL :: Int -> f a -> Vector f n a -> Vector f n a
vecShiftL x a (Vector n tp xs) = Vector n tp ys
  where
  !len = widthVal n
  ys    = Vector.generate len (\i -> let j = i + x
                                     in if j >= len then a else xs Vector.! j)
{-# Inline vecShiftL #-}

{- | Move all elements towards the larger indexes.
Elements that "fall" off the end are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
vecShiftR :: Int -> f a -> Vector f n a -> Vector f n a
vecShiftR !x a (Vector n tp xs) = Vector n tp ys
  where
  !len = widthVal n
  ys   = Vector.generate len (\i -> let j = i - x
                                    in if j < 0 then a else xs Vector.! j)
{-# Inline vecShiftR #-}

--------------------------------------------------------------------------------


{-
vecSplit :: (1 <= w, 1 <= n) => NatRepr n -> NatRepr w ->
                        f (BVType (n * w)) -> Vector f n (BVType w)

vecSplit n w v = Vector n (BVRepr w) (Vector.generate (widthVal n) elementAt)
  where
  elementAt i = undefined


-- | Split a single bit-vector value into a vector of value of the given width.
vecSplit :: forall s n w arch. (?lc::TyCtx.LLVMContext,HasPtrWidth w, w ~ ArchWidth arch, 1 <= n) =>
  NatRepr n  {- ^ Length of a single element -} ->
  LLVMExpr s arch {- ^ Bit-vector value -} ->
  Maybe [ LLVMExpr s arch ]
vecSplit elLen expr =
  do Scalar (BVRepr totLen) e <- return (asScalar expr)
     let getEl :: NatRepr offset -> Maybe [ LLVMExpr s arch ]
         getEl offset = let end = addNat offset elLen
                        in case testLeq end totLen of
                             Just LeqProof ->
                               do rest <- getEl end
                                  let x = bitVal elLen
                                            (BVSelect offset elLen totLen e)
                                  return (x : rest)
                             Nothing ->
                               do Refl <- testEquality offset totLen
                                  return []
     els <- getEl (knownNat @0)
     -- in `els` the least significant chunk is first

     return $! case lay ^. intLayout of
                 LittleEndian -> els
                 BigEndian    -> reverse els
  where
  lay = TyCtx.llvmDataLayout ?lc



-}

{-
-- | Join the elements of a vector into a single bit-vector value.
-- The resulting bit-vector would be of length at least one.

-}

xxx :: (1 <= n) => f w -> f n -> (w + (n-1) * w) :~: (n * w)
xxx = unsafeCoerce Refl

vecJoinWith :: forall f n w bits.
               (IsExpr f, 1 <= w) =>
              (forall x y. f (bits x) -> f (bits y) -> f (bits (x + y))) ->
              Vector f n (bits w) -> f (bits (n * w))
vecJoinWith jn exprs =
  case vecUncons exprs of
    (a, Left Refl) -> a
    (a, Right rest) ->
      case vecNonEmpty exprs of
        LeqProof ->
          case xxx (Proxy :: Proxy w) (Proxy :: Proxy n) of
            Refl -> jn a (vecJoinWith jn rest)
      -- Proof: w + (n-1) * w = n * w

{-
  case vecUncons exprs of
    (a,Nothing) -> a

  do (a,ys) <- List.uncons exprs
     Scalar (BVRepr n) e1 <- return (asScalar a)
     if null ys
       then do LeqProof <- testLeq (knownNat @1) n
               return (BaseExpr (BVRepr n) e1)
       else do BaseExpr (BVRepr m) e2 <- vecJoin ys
               let p1 = leqProof (knownNat @0) n
                   p2 = leqProof (knownNat @1) m
               (LeqProof,LeqProof) <- return (leqAdd2 p1 p2, leqAdd2 p2 p1)
               let bits u v x y = bitVal (addNat u v) (BVConcat u v x y)
               return $! case TyCtx.llvmDataLayout ?lc ^. intLayout of
                           LittleEndian -> bits m n e2 e1
                           BigEndian    -> bits n m e1 e2


-}
