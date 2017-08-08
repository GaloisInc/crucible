------------------------------------------------------------------------
-- |
-- Module           : Lang.MATLAB.MultiDimArray
-- Description      : Multi-dimensional arrays with 1-based indexing.
-- Copyright        : (c) Galois, Inc 2013-2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides multi-dimensional arrays with 1-based
-- indexing.  The goal is to provide an interface similar to MATLAB
-- arrays.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Lang.MATLAB.MultiDimArray
  ( -- * Array dim
    ArrayDim
  , singletonDim
  , matrixDim
  , fromDimList
  , dimCount
    -- ** Array dimension operations
  , concatInDims
  , removeDim
  , insertDim
  , setDim
  , permuteDim
  , forIndicesM_
    -- * HasDim operations
  , HasDim(..)
  , rowDim
  , colDim
  , higherDims
  , firstNonSingleDim
  , dimAt
  , splitDim
  , asDimList
  , asDimListN
  , asDimVectorN
  , ppDim
    -- ** Dimension predicates
  , is2d
  , isSquare
  , isRowVector
  , isColVector
  , isVector
    -- * Index into a multi dimensional arrays
  , Index
  , indexLength
  , asIndexPair
  , indexToList
  , indexToVector
  , indexFromList
  , indexFromVector
  , onDiagonal
  , (!!)
  , (!?)
    -- * Multi dimensional arrays
  , MultiDimArray
  , mdVec
  , generate
  , generateM

  , empty
  , singleton
  , identity
  , asSingleton
  , asRowVector
  , asColVector
  , asVector

  , row
  , col
  , rowVector
  , colVector
  , map
  , zip
  , unzip
  , zipWith
  , zipWithM
  , mdFromVector

  , replicate
  , replicateM
  , asRows
  , fromRows
  , pp2d
  , ppMDA
  , ppVector
  , (!)
  , (!!?)
  , set
  , tryEltIndex
  , mdConcatAtDim
  , arrayProduct
  , extractAtDim
  , mergeAtDim
  , reduceDim
  , squeeze
    -- ** Permutations
  , Perm
  , checkPerm
  , reversePerm
  , transpose
  , permute
  , ipermute
  , circshift
    -- * Utilities
  , dimsMatch
    -- * CharArray
  , CharArray
  ) where


import Control.Exception
import Control.Monad (when, zipWithM_)
import Control.Monad.ST
import Data.Maybe
import qualified Data.Monoid as Monoid
import Data.STRef.Strict
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Data.Word
import Numeric.Natural
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import Lang.MATLAB.Utils.List
import Lang.MATLAB.Utils.PrettyPrint

import qualified Prelude
import Prelude hiding (null, replicate, unzip, zip, zipWith, (!!), map)

type CharArray = MultiDimArray Word16

-- | Return true if dimensions are the same.
dimsMatch :: [Natural] -> [Natural] -> Bool
dimsMatch (x:xl) (y:yl) = x == y && dimsMatch xl yl
dimsMatch [] l = all (==1) l
dimsMatch l [] = all (==1) l

-- | Return true if dimensions are the same.
dimsOrd :: [Natural] -> [Natural] -> Ordering
dimsOrd (x:xl) (y:yl) = compare x y Monoid.<> dimsOrd xl yl
dimsOrd [] (1:l) = dimsOrd [] l
dimsOrd (1:l) [] = dimsOrd l []
dimsOrd [] [] = EQ
dimsOrd [] _ = LT
dimsOrd _ [] = GT

asCons :: [Natural] -> (Natural,[Natural])
asCons [] = (1,[])
asCons (e:l) = (e,l)

------------------------------------------------------------------------
-- ArrayDim

-- | Datatype representing the dimension specification of a multi-dimensional
-- array. The arguments to 'Dim' are: number of rows, number of columns, and a
-- list of the higher dimensions.
--
-- For example, the dimensions of a singleton array are represented by
-- 'Dim 1 1 []'; and an NxM matrix by 'Dim N M []'.
--
-- Note that trailing higher dimensions which are equal to 1 are ignored
-- and/or stripped away by many operations, see 'dimsMatch'.
data ArrayDim = Dim !Natural !Natural ![Natural]

instance Eq ArrayDim where
  Dim rx cx hx == Dim ry cy hy = rx == ry && cx == cy && hx `dimsMatch` hy

instance Ord ArrayDim where
  compare (Dim rx cx hx) (Dim ry cy hy)
    = compare rx ry
    Monoid.<> compare cx cy
    Monoid.<> dimsOrd hx hy

instance Show ArrayDim where
  show = show . ppDim

singletonDim :: ArrayDim
singletonDim = Dim 1 1 []

matrixDim :: Natural -> Natural -> ArrayDim
matrixDim r c = Dim r c []

-- | Removes the value "1" from the end of the list.
dropTrailing1 :: [Natural] -> [Natural]
dropTrailing1 [] = []
dropTrailing1 (1:l) =
  case dropTrailing1 l of
    [] -> []
    r -> 1:r
dropTrailing1 (x:l) = x:dropTrailing1 l

-- | Create a dimension from a list.
fromDimList :: [Natural] -> ArrayDim
fromDimList l =
  case l of
    []    -> Dim 1 1 []
    [r]   -> Dim r 1 []
    r:c:h -> Dim r c (dropTrailing1 h)

-- | Squeeze array dimensions.
squeezeDim :: ArrayDim -> ArrayDim
squeezeDim a =
  fromDimList (filter (/= 1) (asDimList a))

-- @removeDim i d@ removes dimension @i@ from @d@.
removeDim :: Int -> ArrayDim -> ArrayDim
removeDim 0 (Dim _ r (asCons -> (c,l))) = Dim r c l
removeDim 1 (Dim r _ (asCons -> (c,l))) = Dim r c l
removeDim i (Dim r c l0) = assert (i >= 2) $ Dim r c (dropTrailing1 (go (i-2) l0))
  where -- Recursively evaluate dimensions.
        go j (asCons -> (e,l))
          | j == 0 = l
          | True   = e : go (j-1) l

-- @insertDim i n d@ inserts @n@ as dimension @i@ in @d@.
insertDim :: Int -> Natural -> ArrayDim -> ArrayDim
insertDim 0 n (Dim r c l) = Dim n r (c:l)
insertDim 1 n (Dim r c l) = Dim r n (c:l)
insertDim i n (Dim r c l0) = assert (i >= 2) $ seq n $ Dim r c (dropTrailing1 (go (i-2) l0))
  where -- Recursively evaluate dimensions.
        go 0 h = n:h
        go j (asCons -> (e,l)) = (:) e $! go (j-1) l

-- @setDim i n d@ set dimension @i@ in @d@ to @n@.  This will
-- expand the number of dimensions in @d@ to be at least @i+1@.
setDim :: Natural -> Natural -> ArrayDim -> ArrayDim
setDim 0 n (Dim _ c l) = Dim n c l
setDim 1 n (Dim r _ l) = Dim r n l
setDim i n (Dim r c l0) = assert (i >= 2) $ seq n $ Dim r c (dropTrailing1 (go (i-2) l0))
  where -- Recursively evaluate dimensions.
        go :: Natural -> [Natural] -> [Natural]
        go j (asCons -> (e,l))
          | j == 0 = (:l) $! n
          | True   = (e:) $! (go (j-1) l)

-- | Return number of dimensions in array dim.
-- For example, @dimCount "2*3*4"@ returns @3@.
dimCount :: ArrayDim -> Int
dimCount (Dim _ _ l) = 2 + length l

-- | Concat array dims together in given dimension.
concatInDims :: Int -> ArrayDim -> [ArrayDim] -> ArrayDim
concatInDims i d0 rest = fromDimList (setIndex (asDimList d0) i s)
  where s = sum $ (\d -> defIndex (asDimList d) i 1) <$> (d0:rest)

------------------------------------------------------------------------
-- HasDim

class HasDim d where
  -- | Returns dimensions
  dim :: d -> ArrayDim

  -- | Returns true when value is empty.
  null :: d -> Bool
  null (dim -> Dim r c l) = any (==0) (r:c:l)

  -- | Returns true if this has a single element.
  isSingleton :: d -> Bool
  isSingleton (dim -> Dim r c h) = r == 1 && c == 1 && Prelude.all (==1) h

  -- | Returns total size of array dimensions.
  -- For example, @dimSize "2*3*4"@ returns @24@.
  dimSize :: d -> Natural
  dimSize (dim -> Dim rcnt ccnt higherdim) = rcnt * ccnt * product higherdim

instance HasDim ArrayDim where
  dim = id

-- | Number of rows.
rowDim :: HasDim d => d -> Natural
rowDim (dim -> Dim r _ _) = r

-- | Number of columns.
colDim :: HasDim d => d -> Natural
colDim (dim -> Dim _ c _) = c

-- | Sizes in higher dimensions.
higherDims :: HasDim d => d -> [Natural]
higherDims (dim -> Dim _ _ h) = h

-- | Return index of first dimension that has length not equal to one.
firstNonSingleDim :: HasDim d => d -> Maybe Natural
firstNonSingleDim d = go 1 (asDimList d)
  where go _ [] = Nothing
        go i (e:l) | e /= 1 = Just i
                   | otherwise = seq j $ go j l
          where j = i+1

-- | Return size of dimension at given index (indices are one-based).
dimAt :: HasDim d => d -> Natural -> Natural
dimAt (dim -> Dim r c l) i
  | i == 0    = error "internal error: Looking up 0-th dimension of an array"
  | i == 1    = r
  | i == 2    = c
  | otherwise = (l ++ repeat 1) Prelude.!! (fromIntegral i - 3)

-- | Returns true if value has no non-singular dimensions
-- at index 3 or higher.
is2d :: HasDim d => d -> Bool
is2d d = Prelude.null (higherDims d)

-- | Returns true if this is a 2d square matrix.
isSquare :: HasDim d => d -> Bool
isSquare (dim -> Dim r c h) = r == c && Prelude.null h

-- | Returns true if this is a 2d matrix with a single row.
isRowVector :: HasDim d => d -> Bool
isRowVector (dim -> Dim r _ h) = r == 1 && Prelude.null h

-- | Returns true if this is a 2d matrix with a single row or column.
isColVector :: HasDim d => d -> Bool
isColVector (dim -> Dim _ c h) = c == 1 && Prelude.null h

-- | Returns true if this is a 2d matrix with a single row or column.
isVector :: HasDim d => d -> Bool
isVector (dim -> Dim r c h) = (r == 1 || c == 1) && Prelude.null h

-- | Return list of dimensions.
asDimList :: HasDim d => d -> [Natural]
asDimList (dim -> Dim rcnt ccnt higherdim) = rcnt : ccnt : higherdim

-- | Resizes a list of dimensions according to the semantics of the
--   MATLAB size() function.  In particular, when growing a list of
--   dimensions, each added position in the list is given the value
--   @1@; when shrinking a list of dimensions, all the removed
--   positions are multiplied onto the last element of the new
--   truncated list.
resizeDimList :: Int -> [Natural] -> [Natural]
resizeDimList n _ | n <= 0 = []
resizeDimList 1 ds = [product ds]
resizeDimList n [] = Prelude.replicate n 1
resizeDimList n (d:ds) = d:(resizeDimList (n-1) ds)

-- | Return list of dimensions as resized by @resizeDimList@.
asDimListN :: HasDim d => Natural -> d -> [Natural]
asDimListN c0 d = resizeDimList (fromIntegral c0) (asDimList d)

-- | Return list of dimensions as resized by @resizeDimList@.
asDimVectorN :: HasDim d => Natural -> d -> V.Vector Natural
asDimVectorN c0 d = V.fromList $ resizeDimList (fromIntegral c0) (asDimList d)

-- | @splitDim d i@ returns two lists of dimensions, the first
--   containing those dimensions whose indices are smaller than @i@,
--   and the second containing those dimensions whose indices are
--   greater than or equal to @i@.
splitDim :: HasDim d => d -> Natural -> ([Natural],[Natural])
splitDim d i =
  let i' = fromIntegral i - 1
      (l, r) = splitAt i' (asDimList d)
      l' = take i' $ l ++ repeat 1
   in (l', r)

-- | Pretty print an array dimension.
ppDim :: HasDim d => d -> Doc
ppDim d = encloseSep PP.empty PP.empty (text "*") $ integer . toInteger <$> asDimList d

------------------------------------------------------------------------
-- Index

-- | An index is a vector of natural numbers used as an index into a
-- multi-dimensional array.
newtype Index = Index { unIndex :: V.Vector Natural }
  deriving (Eq, Ord)

indexTake :: Int -> Index -> Index
indexTake n (Index v) = Index (V.take n v)

onDiagonal :: Index -> Bool
onDiagonal (Index v) | V.null v = True
  | otherwise =
     let a = v V.! 0
      in V.all (== a) (V.tail v)

instance Show Index where
  show (Index v) | V.null v = "()"
                 | otherwise = concat $ (\i -> ',' : show i) <$> V.toList v

{-# DEPRECATED (!!) "Use !?" #-}

(!!) :: Index -> Int -> Natural
(!!) v i = n
  where Just n = unIndex v V.!? i

-- | Lookup nat at given position in index.
(!!?) :: Index -> Int -> Maybe Natural
(!!?) v i = unIndex v V.!? i

asSingleIndex :: Index -> Maybe Natural
asSingleIndex (Index i) | V.length i == 1 = Just (i V.! 0)
                        | otherwise = Nothing

indexLength :: Index -> Int
indexLength (Index i) = V.length i

indexFromList :: [Natural] -> Index
indexFromList = Index . V.fromList

indexFromVector :: V.Vector Natural -> Index
indexFromVector v = Index (V.generate (V.length v) (v V.!))

indexToVector :: Index -> V.Vector Natural
indexToVector (Index v) = V.generate (V.length v) (v V.!)

indexToList :: Index -> [Natural]
indexToList = V.toList . unIndex

indexPair :: Natural -> Natural -> Index
indexPair i j = Index (V.fromList [i,j])

asIndexPair :: Index -> Maybe (Natural,Natural)
asIndexPair (Index v) | V.length v == 2 = Just (v V.! 0, v V.! 1)
                      | otherwise = Nothing

-- | forIndicesM_ calls the function on each legal index of an arraydim.
forIndicesM_ :: forall m . Applicative m => ArrayDim -> (Index -> m ()) -> m ()
forIndicesM_ d _ | null d = pure ()
forIndicesM_ d f =
    let dv = V.fromList (asDimList d)
     in go dv (V.replicate (V.length dv) 1)
  where -- Call f on array value and then try next index.
        go :: V.Vector Natural -> V.Vector Natural -> m ()
        go dv idxv = f (Index idxv) *> update dv idxv 0
        -- Increment next index.
        -- Takes counts, current vector and current index.
        update :: V.Vector Natural -> V.Vector Natural -> Int -> m ()
        update dv idxv i
          | i == d_cnt = pure ()
            -- Update at index i if we can.
          | v < dv V.! i =
            let prefix  = V.replicate i 1
                postfix = V.drop (i + 1) idxv
             in go dv $! (prefix V.++ V.cons (v+1) postfix)
          | otherwise =
            -- Check to see if we can update at a later index.
            update dv idxv (i+1)
         where d_cnt = V.length dv
               v = idxv V.! i -- Index at value.
{-# INLINABLE forIndicesM_ #-}

------------------------------------------------------------------------
-- MultiDimArray

data MultiDimArray v =
  MultiDimArray { mdDim :: !ArrayDim
                , mdVec :: !(V.Vector v)
                  -- ^ A dense matrix where rows are continuous, columns
                  -- are next, and higher dimensions after that.
                }
  deriving (Eq, Functor, Foldable)

instance Traversable MultiDimArray where
  traverse = \f a -> (\v -> a { mdVec = v }) <$> traverse f (mdVec a)
  {-# INLINE traverse #-}

instance HasDim (MultiDimArray v) where
  dim = mdDim
  null a = V.null (mdVec a)
  dimSize a = fromIntegral (V.length (mdVec a))

empty :: MultiDimArray v
empty =
  MultiDimArray { mdDim = matrixDim 0 0
                , mdVec = V.empty
                }

singleton :: v -> MultiDimArray v
singleton v = seq v $
  MultiDimArray { mdDim = matrixDim 1 1
                , mdVec = V.singleton v
                }

-- | Returns the identity matrix with the given number of dimensions.
identity :: Num v => Natural -> MultiDimArray v
identity n = MultiDimArray (matrixDim n n) (V.generate n2 go)
  where n2 = fromIntegral (n*n)
        n' = fromIntegral n
        go i = if q == r then 1 else 0
          where (q,r) = i `quotRem` n'

-- | Create a multidim array from a vector.
mdFromVector :: ArrayDim -> V.Vector v -> MultiDimArray v
mdFromVector d v = assert (dimSize d == fromIntegral (V.length v)) $
  MultiDimArray { mdDim = d
                , mdVec = v
                }

-- | Create a multidimarray from a vector as a single row.
rowVector :: V.Vector v -> MultiDimArray v
rowVector v = MultiDimArray { mdDim = matrixDim 1 (fromIntegral (V.length v))
                            , mdVec = v
                            }

-- | Create a multidimarray from a vector as a single col.
colVector :: V.Vector v -> MultiDimArray v
colVector v = MultiDimArray { mdDim = matrixDim (fromIntegral (V.length v)) 1
                            , mdVec = v
                            }

-- | If array is a single element, this returns that element.
asSingleton :: MultiDimArray v -> Maybe v
asSingleton a
  | V.length (mdVec a) == 1 = Just (mdVec a V.! 0)
  | otherwise = Nothing

-- | If array is a single row, this returns that row.
asRowVector :: MultiDimArray v -> Maybe (V.Vector v)
asRowVector a
  | isRowVector a = Just (mdVec a)
  | otherwise = Nothing

-- | If array is a single column, this returns that column.
asColVector :: MultiDimArray v -> Maybe (V.Vector v)
asColVector a
  | isColVector a = Just (mdVec a)
  | otherwise = Nothing

-- | If array is a row or column vector, this returns that vector.
asVector :: Monad m => MultiDimArray v -> m (V.Vector v)
asVector a
  | isVector a = return (mdVec a)
  | otherwise = fail "Expected vector."

-- | Convert multidimarray into a vector of rows.
-- Higher dimensions are concatenated together so that the number
-- of columns in the result is equal to the product of the higher
-- dimensions and columns in the input matrix.
asRows :: MultiDimArray v -> V.Vector (V.Vector v)
asRows a =
        V.generate (fromIntegral r) $ \j ->
          V.generate (fromIntegral c) $ \k ->
            let u = (fromIntegral k)*r+fromIntegral j
             in v V.! fromIntegral u
  where r = rowDim a
        c = product (colDim a : higherDims a)
        v = mdVec a

-- | Convert vector of rows into a MultiDimArray.
fromRows :: Natural -- ^ Number of rows
         -> Natural -- ^ Number of columns
         -> V.Vector (V.Vector v)
         -> MultiDimArray v
fromRows rc cc a
   | V.length a == rci && V.all (== cci) (V.length <$> a) = res
   | otherwise = error "MultiDimArray.fromRows given bad inputs"
  where rci = fromIntegral rc
        cci = fromIntegral cc
        v = V.generate cci $ \c ->
              V.generate rci $ \r -> a V.! r V.! c
        res = MultiDimArray { mdDim = matrixDim rc cc
                            , mdVec = V.concatMap id v
                            }

-- | Return a value at a given location in the array.
-- An assertion will fail if value is out of range.
(!?) :: Monad m => MultiDimArray v -> Index -> m v
a !? l0 = resolve <$> tryEltIndex (asDimList a) l0
  where v = mdVec a
        resolve o = assert (0 <= o && o < fromIntegral (V.length v)) (v V.! fromIntegral o)
{-# INLINE (!?) #-}

-- | Return a value at a given location in the array.
-- An assertion will fail if value is out of range.
(!) :: MultiDimArray v -> Index -> v
a ! l =
  case tryEltIndex (asDimList a) l of
    Just o -> mdVec a V.! fromIntegral o
    Nothing -> error $ "internal error: Looking up of index " ++ show l
                       ++ " at array with dimensions " ++ show (dim a) ++ "."

-- | Return the vector of elements along a single row in a 2d array.
row :: MultiDimArray a -> Natural -> V.Vector a
row a r = assert (Prelude.null (higherDims d))
        $ assert (1 <= r && r <= rowDim d)
        $ V.generate (fromIntegral (colDim d)) eltFn
  where d = dim a
        eltFn c = a ! indexPair r (fromIntegral (c+1))

-- | Return the vector of elements along a single column in a 2d array.
col :: MultiDimArray a -> Natural -> V.Vector a
col a c = assert (Prelude.null (higherDims d))
        $ assert (1 <= c && c <= colDim d)
        $ V.generate (fromIntegral (rowDim d)) eltFn
  where d = dim a
        eltFn r = a ! indexPair (fromIntegral (r+1)) c

checkDim :: Monad m
         => Natural -- ^ Length
         -> Natural -- ^ Index
         -> m ()
checkDim n i = do
  when (i <= 0) $ fail "Subscript index must be positive."
  when (i > n) $ fail "Index exceeds matrix dimensions."

-- | Compute index of element in vector given bounds of array and indices to lookup.
tryEltIndex :: Monad m
            => [Natural] -- ^ Bounds on dimensions of elements.
            -> Index -- ^ Indices to lookup
            -> m Natural
tryEltIndex dl0 (Index idx0) | V.length idx0 == 0 = return 0
                             | otherwise = go 0 1 dl0 idx0 0
 where go :: Monad m => Natural -> Natural -> [Natural] -> V.Vector Natural -> Int -> m Natural
       go o p cl idx j | j + 1 == V.length idx = do
         let i = idx V.! j
         checkDim (product cl) i
         return (o+p*(i-1))
       go o p (c:cl) idx j = do
         let i = idx V.! j
         checkDim  c i
         go (o+p*(i-1)) (p*c) cl idx (j+1)
       go o _ [] idx j = do
         V.mapM_ (checkDim 1) (V.drop j idx)
         return o
{-# INLINABLE tryEltIndex #-}

-- | Expand dimension to cover index.
maxDim :: ArrayDim -> Index -> ArrayDim
maxDim d0 l0 = fromDimList $ go (asDimList d0) (indexToList l0)
  where go (a:l) (b:r) = max a b : go l r
        go [] l = l
        go l [] = l

-- | Attemtp to update array at a given index, and return new array or 'Nothing'
-- if the operation fails (which can only happen if a single index is given and
-- the array must be resized).
--
-- This will typically, grow the array as necessary to accommodate the index and
-- return a new array.
--
-- However, if the index is a single value, and the array is not a single row or
-- column, then this will fail as we cannot determine which dimension to resize.
set :: MultiDimArray v -- ^ Multi-dim array to update.
    -> v     -- ^ Value to use for new values in array if we need to expand array.
    -> Index -- ^ Index to update
    -> v     -- ^ New value
    -> Maybe (MultiDimArray v) -- ^ New array
set a dv (asSingleIndex -> Just i) e
  | null a = assert (1 <= i) $ do
      let i' = fromIntegral i
      let ifn j | j+1 == i' = e
                | otherwise = dv
      Just $! rowVector (V.generate i' ifn)
  | i <= dimSize a =
      Just $! a { mdVec = mdVec a V.// [(fromIntegral i-1,e)] }
  | rowDim d == 1 && Prelude.null (higherDims d) = do
      let n = max (colDim d) i
      Just $! mdFromVector (matrixDim 1 n) (V.generate (fromIntegral n) fn)
  | colDim d == 1 && Prelude.null (higherDims d) = do
      let n = max (rowDim d) i
      Just $! mdFromVector (matrixDim n 1) (V.generate (fromIntegral n) fn)
  | otherwise =
      Nothing -- fail "In assignments with a single index, the array cannot be resized."
 where -- Get old dimensions
       d = dim a
       -- Define function for getting element.
       fn j | j+1 == fromIntegral i  = e -- Use new value at index
            | otherwise = fromMaybe dv $ mdVec a V.!? j
set oldArray defVal setIdx0 newVal = Just $! generate d' fn
  where -- Get old dimensions
        d = dim oldArray
        -- Get new dimensions
        d' = maxDim d setIdx0
        -- Clear trailing one.
        setIdx = indexTake (dimCount d') setIdx0
        -- Define function for getting element.
        fn i | i == setIdx = newVal -- Use new value at index
             | otherwise   = fromMaybe defVal $ oldArray !? i

{-# INLINABLE generate #-}
generate :: ArrayDim -> (Index -> a) -> MultiDimArray a
generate d _ | null d = mdFromVector d V.empty
generate d f = runST $ do
  mv <- MV.new (fromIntegral (dimSize d))
  let dv = V.fromList $ asDimList d

  let d_cnt = V.length dv
  idx_ref <- MV.replicate d_cnt 1

  cnt_ref <- newSTRef 0

  let go = do
        -- Write array value.
        idxv <- V.freeze idx_ref
        i <- readSTRef cnt_ref
        writeSTRef cnt_ref (i+1)
        MV.unsafeWrite mv i $! f (Index idxv)
        update 0
      update i | i == d_cnt = return ()
      update i = do
        -- Go to next index.
        v <- MV.unsafeRead idx_ref i
        if v < dv V.! i then do
          MV.unsafeWrite idx_ref i $! (v+1)
          go
        else do
          MV.unsafeWrite idx_ref i $! 1
          update (i+1)
  go
  mdFromVector d <$> V.unsafeFreeze mv

-- | Create a multidimarray with the given dimensions that replicates
-- the value.
replicate :: ArrayDim -> v -> MultiDimArray v
replicate d v = mdFromVector d (V.replicate n v)
  where n = fromIntegral (dimSize d)

-- | Create a multidimarray by executing the function for each index.
replicateM :: Applicative m => ArrayDim -> m v -> m (MultiDimArray v)
replicateM d m = mdFromVector d <$> traverse (\_ -> m) (V.replicate n (0::Natural))
  where n = fromIntegral (dimSize d)

-- | Create a multidimarray by executing the function for each index.
generateM :: Applicative m => ArrayDim -> (Index -> m v) -> m (MultiDimArray v)
generateM d f = sequenceA (generate d f)

map :: (x -> y) -> MultiDimArray x -> MultiDimArray y
map f (MultiDimArray d v) = MultiDimArray d (V.map f v)

zip :: MultiDimArray x -> MultiDimArray y -> MultiDimArray (x,y)
zip = zipWith (,)

unzip :: MultiDimArray (x, y) -> (MultiDimArray x, MultiDimArray y)
unzip ar = let d = dim ar
               (vx, vy) = V.unzip (mdVec ar) in
           (MultiDimArray d vx, MultiDimArray d vy)

zipWith :: (x -> y -> z) -> MultiDimArray x -> MultiDimArray y -> MultiDimArray z
zipWith f x y = assert (dim x == dim y) $
  MultiDimArray { mdDim = dim x
                , mdVec = V.zipWith f (mdVec x) (mdVec y)
                }

-- | Apply a monad operation to elements in two arrays pairwise.
-- The arrays should have the same dimensions.
zipWithM :: Monad m
         => (x -> y -> m z)
         -> MultiDimArray x
         -> MultiDimArray y
         -> m (MultiDimArray z)
zipWithM f x y = assert (dim x == dim y) $ do
  v <- V.zipWithM f (mdVec x) (mdVec y)
  return $! MultiDimArray { mdDim = mdDim x
                          , mdVec = v
                          }
{-# INLINABLE zipWithM #-}

-- | Given a list of bounds @l@, returns a list of positive integers that are
-- pairwise less-than-or-equal to the bounds @l@.
-- e.g. indexList [2,3] = [[1,1],[2,1],[1,2],[2,2],[1,3],[2,3]]
indexList :: V.Vector Natural -> [Index]
indexList d | V.any (== 0) d = []
indexList dv0 = Index first : nextIndex first dv0 0
  where first = V.replicate (V.length dv0) 1
        nextIndex v _ i | i == V.length v = []
        nextIndex v dv i
            | vi < c =
              let gen_new j | j <  i = 1
                            | j == i = vi+1
                            | True   = v V.! j
                  next = V.generate (V.length v) gen_new
               in Index next : nextIndex next dv 0
            | otherwise = nextIndex v dv $! i+1
         where vi = v V.! i
               c  = dv V.! i

-- | Convert a multidimensional array into a list of 2-dimensional arrays.
-- The indices in each pair are the higher idmension indices for the array.
mdAs2dMatrices :: MultiDimArray x -> [(Index, MultiDimArray x)]
mdAs2dMatrices x = sliceMatrix <$> indexList (V.fromList (higherDims x))
  where v = mdVec x
        r = rowDim x
        c = colDim x
        n = r * c
        d = matrixDim r c
        sliceMatrix idx = (idx, mdFromVector d (V.slice (fromIntegral (n*i)) (fromIntegral n) v) )
          where Just i = tryEltIndex (higherDims x) idx

-- | Pretty print 2-dimensional matrixes.
pp2d :: (MultiDimArray x -> Doc)
     -> String -> MultiDimArray x -> Doc
pp2d pp nm a =
    case higherDims a of
      [] -> ppM ([] :: [Natural]) a
      _ ->  vcat $ (\(i,v) -> ppM (indexToList i) v) <$> mdAs2dMatrices a
  where ppM il m = ppNameEqual (nm ++ res) (pp m)
          where res | Prelude.null il = ""
                    | otherwise       = "(:,:" ++ ild ++ ")"
                ild = concat $ (\i -> ',' : show i) <$> il

-- | Pretty print elements in a multidimarray.
ppMDA :: (x -> String) -> String -> MultiDimArray x -> Doc
ppMDA f = pp2d ppM
  where ppM a = do
          let rc = fromIntegral (rowDim a)
              cc = fromIntegral (colDim a)
          ppAlignedMatrix rc cc (\_ -> leftAlign) $ \r c ->
            f (a ! indexPair (fromIntegral r+1) (fromIntegral c+1))

-- show instance mainly for debugging
instance Show a => Show (MultiDimArray a) where
  showsPrec _ a = displayS $ renderPretty 1.0 80 $ ppMDA show "ans" a

ppVector :: String -> (a -> String) -> MultiDimArray a -> Doc
ppVector nm pp t
  | Just e <- asSingleton t =
    ppNameEqual nm $ text $ pp e
  | otherwise = ppMDA pp nm t

-- | Concatenate arrays together in a specific dimensions.
mdConcatAtDim :: Int -- ^ Zero-based index of dimension to concatenate.
              -> MultiDimArray v -- ^ First array for concatenation.
              -> [MultiDimArray v] -- ^ Rest of arrays for concatenation.
              -> MultiDimArray v
mdConcatAtDim catDim fv rest
    = mdFromVector (concatInDims catDim (dim fv) (dim <$> rest))
    $ V.concatMap (sliceAllDim vals)
    $ V.enumFromN 0 (fromIntegral (product (drop (catDim+1) (asDimList fv))))
  where -- Get number of elements in low-dimensions.
        -- Extract rows*cols for one set of values.
        slice1Dim :: Natural -> MultiDimArray v -> V.Vector v
        slice1Dim i a = V.slice (fromIntegral (i*lowSize)) (fromIntegral lowSize) (mdVec a)
          where lowSize = product (take (1+catDim) (asDimList a))
        -- Slice dimensions at higher-order index for all values.
        sliceAllDim :: V.Vector (MultiDimArray v) -> Natural -> V.Vector v
        sliceAllDim v i = V.concatMap (slice1Dim i) v
        vals = V.fromList (fv:rest)

-- | Create a multi-dimensional array from a crosswise product of the
-- inputs.
--
-- In the single dimension case, this has the same shape as its input,
-- otherwise the ith dimension of the result has the same length as the
-- total number of entries in he ith array in the input.
--
-- arrayProduct [ [1 2] [3 4]] becomes [[1,3] [1,4]; [2,3] [2,4]]
arrayProduct :: [MultiDimArray v] -> MultiDimArray [v]
arrayProduct [] = error "arrayProduct expects at least one element."
arrayProduct [x] = fmap (\v -> [v]) x
arrayProduct l@(_:_:_) = a
  where a = MultiDimArray { mdDim = fromDimList (dimSize <$> l)
                          , mdVec = go l
                          }
        go :: [MultiDimArray v] -> V.Vector [v]
        go [] = V.fromList [[]]
        go (h:r) = V.concatMap (\v -> (:v) <$> ha) (go r)
          where ha = mdVec h

-- | Takes an array of arbitrary shape with elements of type a, along
--   with a specified dimension number d, and produces an array of the
--   same shape except now having length 1 in the d-th dimension, and
--   having elements of type Vector a, each Vector being of the same
--   length as the original array was long in dimension d.  In other
--   words, collapses an array along a specified dimension, replacing
--   say each column in a matrix with a single cell that itself
--   contains a vector of elements that used to constitute the
--   column.  Returns a pair consisting of the new array and the
--   uniform length of its elements.
extractAtDim :: forall a
              . Natural -- ^ Dimension to extract
             -> MultiDimArray a -- ^ Input array
             -> (MultiDimArray (V.Vector a), Natural)
extractAtDim n ar = assert (n > 0) $ (mdFromVector d new_elts, q')
  -- We'll be traversing the linear vector that represents the MDA
  -- and gathering elements which have different coordinates in
  -- dimension n, but share the same coordinates in all other
  -- dimensions, into individual vectors.
  where
    -- Get the relevant dimensions.
    (ld, asCons -> (q', hd)) = splitDim ar n

    -- The dimensions of the output array.
    d = fromDimList (ld ++ 1 : hd)

    -- Get the linear vector that represents the MDA.
    old_elts :: V.Vector a
    old_elts = mdVec ar

    -- Factorize the length of old_elts appropriately.
    l = fromIntegral (product ld)
    q = fromIntegral q'
    h = fromIntegral (product hd)

    -- Here, the total number of elements in the array (and thus in
    -- old_elts) is l*q*h.  Each output vector is specified by a tuple
    -- of lower coordinates, of which there are l many possible, and a
    -- tuple of higher coordinates, of which there are h many possible.
    -- We want to put our output vectors in new_elts in the correct
    -- order, so we must lexicographically cycle through all possible
    -- combinations of these two tuples, with the lower coordinates
    -- cycling in the "inner loop".  Each time we increase the lower
    -- coordinates, the positions of the values want inside old_elts
    -- shift by one to the right.  But each time we increase the higher
    -- coordinates, the extra dimension q needs to be "reinserted".  For
    -- example, suppose we start with a 3x4x2 array.  Then the positions
    -- of the elements of the array in old_elts will be like this:
    --
    --     0  3  6  9
    --     1  4  7  10
    --     2  5  8  11
    --
    --     12 15 18 21
    --     13 16 19 22
    --     14 17 20 23
    --
    -- Suppose we try to extract the second dimension (horizontal) into
    -- vectors.  Then the positions of the elements of the resulting
    -- 3x1x2 array in old_elts will be
    --
    --     0--0--0--0
    --     1--1--1--1
    --     2--2--2--2
    --
    --     3--3--3--3
    --     4--4--4--4
    --     5--5--5--5
    --
    -- Note that the data at output positions 0, 1, 2, 3, 4, 5 begin at
    -- input positions 0, 1, 2, 12, 13, and 14, not a linear
    -- progression.  Hence the following formula:

    -- | The linear vector that will represent the output array.
    new_elts :: V.Vector (V.Vector a)
    new_elts = V.generate (l*h) $ \ik ->
      let --  ik = i*l + k
          (i, k) = quotRem ik l
      in V.generate q $ \j ->
      old_elts V.! (i*l*q + j*l + k {- ∈ [0, l*q*h) -})

-- | Performs the inverse operation of extractAtDim
mergeAtDim :: forall a
            . Natural
           -- ^ Index of dimension
           -> (MultiDimArray (V.Vector a), Natural)
           -- ^ The array and its new length in the dimension (each
           --   element of the array must be a vector of this length)
           -> MultiDimArray a
mergeAtDim n (ar, q') = assert (n > 0) $ mdFromVector d new_elts
  where
    -- Get the relevant dimensions.  If the pattern match here fails,
    -- it means we are trying to merge along a non-singleton dimension.
    (ld, asCons -> (1, hd)) = splitDim ar n

    -- The dimensions of the output array.
    d = fromDimList (ld ++ q' : hd)

    -- Get the linear vector that represents the MDA.
    old_elts :: V.Vector (V.Vector a)
    old_elts = mdVec ar

    -- Factorize the length of old_elts appropriately.
    l = fromIntegral (product ld)
    q = fromIntegral q'
    h = fromIntegral (product hd)

    -- | The linear vector that will represent the output array.
    new_elts :: V.Vector a
    new_elts = V.generate (l*q*h) $ \ijk ->
      let -- ijk  = i*l*q + j*l + k = (i*q+j)*l + k
          (ij, k) = quotRem ijk l
          (i,  j) = quotRem ij q
      in old_elts V.! (i*l + k {- ∈ [0, l*h) -}) V.! j {- ∈ [0, q) -}

-- | Perform an operation to collapse a vector of elements along a dimension
-- into a single value.
reduceDim :: Applicative m
          => (V.Vector a -> m b)
             -- ^ Operation for reduction.
          -> MultiDimArray a
             -- ^ Input array
          -> Natural
             -- ^ Dimension to reduce (first dimension starts with 1).
          -> m (MultiDimArray b)
reduceDim f a i = assert (i > 0) $ traverse f . fst . extractAtDim i $ a

-- | Squeeze one dimensional dimensions out of array.
-- See definition of MATLAB squeeze function.
squeeze :: MultiDimArray a -> MultiDimArray a
squeeze a
  | Prelude.null (higherDims (dim a)) = a
  | otherwise = a { mdDim = squeezeDim (mdDim a) }

------------------------------------------------------------------------
-- Perm

-- | A list of integers treated as a permutation.  As an example,
-- the permutation that maps an array with dimensions m*n*p to
-- an array with dimensions n*p*m is represented as the list
-- [2,3,1].
type Perm = [Int]

-- | Reverse a permutation.
reversePerm :: Perm -> Either String Perm
reversePerm l = do
  let n = length l
  let inRange e = 1 <= e && e <= n
  if all inRange l then do
    runST $ do
      mv <- MV.replicate n 0
      let run i e = MV.write mv (e-1) i
      zipWithM_ run [1..] l
      v <- V.freeze mv
      if V.elem 0 v then
        return $ Left "Permutation contains duplicate elements."
      else
        return $ Right $! V.toList v
  else
    Left "Permutation index out of range."


checkPerm :: Monad m => Perm -> m ()
checkPerm p =
  case reversePerm p of
    Left m -> fail m
    Right{} -> return ()

-- | Permute array dimensions.
permuteDim :: ArrayDim -> Perm -> ArrayDim
permuteDim d perm
    = assert (all (`inRange` dimCount d) perm)
    $ assert (length perm >= 2)
    $ fromDimList $ dimAt d . fromIntegral <$> perm
  where inRange i n = 1 <= i && i <= n

-- | Permute the elements in a dimension given a permutation
-- and its inverse.
permuteGen :: (Perm,Perm)
           -> MultiDimArray a
           -> MultiDimArray a
permuteGen (perm,iperm) a = generate sizes ((a!) . permuteIndices)
  where d = dim a
        sizes = permuteDim d perm

        iperm0 = (\v -> v - 1) `V.map` V.fromList iperm

        -- This function computes an old array index given a new array index by applying
        -- the dimension permutation in reverse.
        --
        -- NB: The permuteIndices function handles a subtle corner case.
        -- Whenever a dimension of size 1 is permuted to the end of the list of
        -- dimensions, that dimension magically disppears from the dimension list.
        -- Thus, the new array can sometimes have fewer dimensions than the original.
        -- When inverting the index permutation to generate the new array, we have
        -- to check if we are asking for a dimension position that is out of range
        -- in the new array; if so, the old dimension must have had size 1, and we return 1.
        permuteIndices :: Index -- new index
                       -> Index -- old index
        permuteIndices i = Index $ lookupDim `V.map` iperm0
           where lookupDim :: Int -> Natural
                 lookupDim x
                  | x < V.length (unIndex i) = unIndex i V.! x
                  | otherwise = 1 -- corner case

-- | Permute the elements in an array.
permute :: Perm
        -> MultiDimArray a
        -> MultiDimArray a
permute perm = permuteGen (perm,iperm)
  where Right iperm = reversePerm perm

-- | Invert permutation of elements in a dimension.
ipermute :: Perm
         -> MultiDimArray a
         -> MultiDimArray a
ipermute perm = permuteGen (iperm,perm)
  where Right iperm = reversePerm perm

transpose :: MultiDimArray a -> MultiDimArray a
transpose a = assert (is2d a) $ permute [2,1] a

-- | @ensureLength n d l@ returns a list with length @n@ that
-- contains the first @n@ elements of @l@ followed by elements
-- with value @d@ as needed.
ensureLength :: Int -> a -> [a] -> [a]
ensureLength i d l | nl > i = Prelude.take i l
                   | nl < i = l ++ Prelude.replicate (i-nl) d
                   | otherwise = l
  where nl = length l

-- @circshift a n@ returns @a@ where indices have been shifted by @sl@.
circshift :: MultiDimArray a -> [Integer] -> MultiDimArray a
circshift a sl0 = generate (dim a) idxFn
  where dl = asDimList a
        -- Make sure shift length is correct.
        sl = ensureLength (length dl) 0 sl0
        -- Compute original index location given new index by subtracting
        -- shift from each coordinate.
        shiftFn :: Natural -> Integer -> Natural -> Natural
        shiftFn i s n = fromInteger $ 1 + ((toInteger i - s - 1) `mod` toInteger n)
        -- Resolve index in a.
        idxFn il = v
          where il' = zipWith3 shiftFn (indexToList il) sl dl
                Just v = a !? indexFromList il'
