{-# Language GADTs, KindSignatures, FunctionalDependencies, FlexibleInstances #-}
{-# Language TypeOperators, DataKinds, UndecidableInstances #-}
{-# Language RankNTypes #-}
module Lang.Crucible.Simulator.VecValue
  ( VecVal
  
    -- * Constructors
  , vecValLit
  , muxVector
  , muxVector'
  , vecValReplicate
  , vecValCons
  , vecValSnoc
  , vecValSetEntry
  , vecValSetEntryConcrete
  , vecValAdjEntry
  , vecValInit
  , vecValTail
  , vecValTake
  , vecValDrop
  , vecValAppend
  , vecValMap
  , vecValZipWith

    -- * Observers
  , vecValToVec
  , vecValIsEmpty
  , vecValSize
  , vecValSizeConcrete

  , vecValGetEntry
  , vecValGetEntryConcrete
  , vecValHead
  , vecValLast
  , vecValFold

  

  -- * Partial Vectors
  , vecValToPartial
  , vecValUninit
  , vecValResize
  , vecValResizePartial

   -- * Bounds Checking
  , ensureInRange

  -- * Interface classes
  , IsRegValue(..)
  , VecSize(..)
  , VecMonad(..)

  ) where

import GHC.Natural(Natural)
import GHC.TypeLits(KnownNat)
import Data.Maybe(fromMaybe)
import Data.Kind(Type)
import qualified Data.Vector as V
import Control.Monad(guard)
import Control.Monad.IO.Class(MonadIO, liftIO)
import What4.Interface
import What4.Partial
import What4.Expr(BVExpr)
import qualified Data.BitVector.Sized as BV
import Lang.Crucible.Types
import Lang.Crucible.Backend
import Lang.Crucible.Simulator.SimError

-- | We expect this to have one instance: for `RegValue'`.
-- We don't use that type directly to avoid recursive module dependencies.
class IsExprBuilder sym => IsRegValue sym f | f -> sym where

  -- | Convert a partial expression into a value of a @Maybe@ type.
  partialToMaybe :: PartExpr (Pred sym) (f tp) -> f (MaybeType tp)

-- | We expect this to have two instances:
-- One for 'IO', used by the symbolic evaluator,
-- and one for 'MuxLeafT' used by `crucible-mir`
class MonadIO m => VecMonad sym m where

  -- | We use this for partial operations (e.g., indexing a vector out of bounds).
  vecAbort :: IsSymBackend sym bak => bak -> SimErrorReason -> m a

  -- | A pre-condition on the current operation.  Assertions we generate
  -- are conditional on this.
  vecPre   :: IsExprBuilder sym => sym -> m (Pred sym)

instance VecMonad sym IO where
  vecAbort = addFailedAssertion 
  vecPre = pure . truePred

-- | Type suitable for indexing into vectors, or getting the size of a vector.
-- Instances:
--  * one for symbolic natural numbers,
--  * one for bit-vector types (i.e., usize),
-- * one for concrete natural numbers
class IsExprBuilder sym => VecSize sym t where
  vecSizeIsConcrete :: sym -> t -> Maybe Int
  vecSizeLit        :: sym -> Natural -> IO t
  vecSizeEq         :: sym -> t -> t -> IO (Pred sym)
  vecSizeLeq        :: sym -> t -> t -> IO (Pred sym)



instance IsExprBuilder sym => VecSize sym (SymNat sym) where
  vecSizeIsConcrete _ i =
    do
      n <- asNat i
      guard (n <= fromIntegral (maxBound :: Int))
      pure (fromIntegral n)

  vecSizeLit sym i = natLit sym (fromIntegral i)
  vecSizeEq        = natEq
  vecSizeLeq       = natLe

instance (1 <= w, KnownNat w, IsExprBuilder sym, SymBV sym w ~ BVExpr s w) => VecSize sym (BVExpr s w) where
  vecSizeIsConcrete _ i =
    do BV.BV n <- asBV i
       guard (n <= toInteger (maxBound :: Int))
       pure (fromIntegral n)
  vecSizeLit sym n = bvLit sym knownNat (BV.mkBV knownNat (toInteger n))
  vecSizeEq        = bvEq
  vecSizeLeq       = bvUle

instance IsExprBuilder sym => VecSize sym Natural where
  vecSizeIsConcrete _ n = Just (fromIntegral n) -- assumes it fits
  vecSizeLit _ = pure
  vecSizeEq sym x y = pure (backendPred sym (x == y))
  vecSizeLeq sym x y = pure (backendPred sym (x <= y))


instance IsExprBuilder sym => VecSize sym Integer where
  vecSizeIsConcrete _ n = Just (fromIntegral n) -- assumes it fits
  vecSizeLit _ = pure . fromIntegral -- assumes it fits
  vecSizeEq sym x y = pure (backendPred sym (x == y))
  vecSizeLeq sym x y = pure (backendPred sym (x <= y))



--------------------------------------------------------------------------------



data VecVal (f :: CrucibleType -> Type) (tp :: CrucibleType) where
  VecVal :: V.Vector (f tp) -> VecVal f tp

vecValLit :: V.Vector (f tp) -> VecVal f tp
vecValLit xs = VecVal xs

vecValToVec :: VecVal f tp -> IO (V.Vector (f tp))
vecValToVec (VecVal xs) = pure xs

vecValReplicate ::
  (IsExprBuilder sym, VecSize sym i) =>
  sym -> i -> f tp -> IO (VecVal f tp)
vecValReplicate sym n v =
  case vecSizeIsConcrete sym n of
    Just sz -> pure (VecVal (V.replicate sz v))
    Nothing -> throwUnsupported sym "Vector replicate on symbolic size."

vecValIsEmpty :: IsExprBuilder sym => sym -> VecVal f tp -> IO (Pred sym)
vecValIsEmpty sym (VecVal xs) = pure (backendPred sym (V.null xs))

vecValSize :: VecSize sym i => sym -> VecVal f tp -> IO i
vecValSize sym (VecVal xs) = vecSizeLit sym (fromIntegral (V.length xs))

vecValSizeConcrete :: VecVal f tp -> Int
vecValSizeConcrete (VecVal xs) = V.length xs

vecValZipWith ::
  (IsExprBuilder sym) =>
  sym ->
  (f a -> f b -> IO (f c)) ->
  VecVal f a -> VecVal f b -> IO (VecVal f c)
vecValZipWith _sym f (VecVal xs) (VecVal ys) = VecVal <$> V.zipWithM f xs ys

vecValMap ::
  (IsExprBuilder sym) =>
  sym ->
  (f a -> IO (f b)) ->
  VecVal f a -> IO (VecVal f b)
vecValMap _sym f (VecVal xs) = VecVal <$> mapM f xs
  
vecValFold ::
  (IsExprBuilder sym) =>
  sym ->
  (a -> f tp -> IO a) ->
  a ->
  VecVal f tp ->
  IO a
vecValFold _sym f acc (VecVal xs) = V.foldM f acc xs
  

-- | Get the value at the given index.
vecValGetEntry ::
  (VecMonad sym m, VecSize sym i, IsSymBackend sym bak) =>
  bak                                       {- ^ Symbolic backend -} ->
  (Pred sym -> f tp -> f tp -> IO (f tp))   {- ^ Ite function -} ->
  VecVal f tp                               {- ^ Vector to index -} ->
  i                                         {- ^ Position -} ->
  m (f tp)                                  {- ^ Value at the given position -}
vecValGetEntry bak ite (VecVal xs) i = indexVector bak ite xs i

-- | Get the value at the given index.
vecValGetEntryConcrete ::
  (VecMonad sym m, IsSymBackend sym bak) =>
  bak                                       {- ^ Symbolic backend -} ->
  VecVal f tp                               {- ^ Vector to index -} ->
  Int                                         {- ^ Position -} ->
  m (f tp)                                  {- ^ Value at the given position -}
vecValGetEntryConcrete bak (VecVal xs) i = indexVectorConcrete bak xs i

-- | Update a vector at the given index.
vecValSetEntry :: (VecMonad sym m, IsSymBackend sym bak, VecSize sym i) =>
  bak                                       {- ^ Symbolic backend -} ->
  (Pred sym -> f tp -> f tp -> IO (f tp))   {- ^ Ite function -} ->
  VecVal f tp                               {- ^ Vector to update -} ->
  i                                         {- ^ Index to update -} ->
  f tp                                      {- ^ New value to assign -} ->
  m (VecVal f tp)
vecValSetEntry bak ite vec i v =
  vecValAdjEntry bak ite vec i (const (pure v))

vecValSetEntryConcrete :: (VecMonad sym m, IsSymBackend sym bak) =>
  bak -> VecVal f tp -> Int -> f tp -> m (VecVal f tp)
vecValSetEntryConcrete bak (VecVal xs) i v =
  VecVal <$> adjVectorConcrete bak xs i (const (pure v))

vecValAdjEntry :: (VecMonad sym m, IsSymBackend sym bak, VecSize sym i) =>
  bak                                       {- ^ Symbolic backend -} ->
  (Pred sym -> f tp -> f tp -> IO (f tp))   {- ^ Ite function -} ->
  VecVal f tp                               {- ^ Vector to update -} ->
  i                                         {- ^ Index to update -} ->
  (f tp -> m (f tp))                        {- ^ New value, given the old value -} ->
  m (VecVal f tp)
vecValAdjEntry bak ite (VecVal xs) i adj =
  VecVal <$> adjVector bak ite xs i adj

-- | Add an element to the front of a vector.
vecValCons :: IsExprBuilder sym => sym -> f tp -> VecVal f tp -> IO (VecVal f tp)
vecValCons _sym x (VecVal xs) = pure (VecVal (V.cons x xs))

-- | Add an element to the end of a vector.
vecValSnoc :: IsExprBuilder sym => sym -> VecVal f tp -> f tp -> IO (VecVal f tp)
vecValSnoc _sym (VecVal xs) x = pure (VecVal (V.snoc xs x))

-- | Get the first element of a vector if any.
vecValHead :: (IsExprBuilder sym, IsRegValue sym f) => sym -> VecVal f tp -> IO (f (MaybeType tp))
vecValHead sym (VecVal xs) =
  pure (partialToMaybe (maybePartExpr sym (xs V.!? 0)))

vecValLast :: (IsExprBuilder sym, IsRegValue sym f) => sym -> VecVal f tp -> IO (f (MaybeType tp))
vecValLast sym (VecVal xs) =
  pure (partialToMaybe (if V.null xs then Unassigned else justPartExpr sym (V.last xs)))

-- | Get the tail of a vector. If the vector is empty, it stays empty.
vecValTail :: (IsExprBuilder sym) => sym -> VecVal f tp -> IO (VecVal f tp)
vecValTail _sym (VecVal xs)
  | V.null xs = pure (VecVal xs)
  | otherwise = pure (VecVal (V.tail xs))

-- | Get all but the last element of a vector.  If the vector is empty, it stays empty.
vecValInit :: (IsExprBuilder sym) => sym -> VecVal f tp -> IO (VecVal f tp)
vecValInit _sym (VecVal xs)
  | V.null xs = pure (VecVal xs)
  | otherwise = pure (VecVal (V.init xs))

-- | Append two vectors.
vecValAppend :: (IsExprBuilder sym) => sym -> VecVal f tp -> VecVal f tp -> IO (VecVal f tp)
vecValAppend _sym (VecVal xs) (VecVal ys) = pure (VecVal (xs <> ys))

-- | Take the given number of elements from the front of the vector.
vecValTake :: (IsExprBuilder sym, VecSize sym i) => sym -> VecVal f tp -> i -> IO (VecVal f tp)
vecValTake sym (VecVal xs) i =
  case vecSizeIsConcrete sym i of
    Just n  -> pure (VecVal (V.take n xs))
    Nothing -> throwUnsupported sym "Taking a symbolic number of elements from a vector."

-- | Remove the given number of elements from the front of the vector.
vecValDrop :: (IsExprBuilder sym, VecSize sym i) => sym -> VecVal f tp -> i -> IO (VecVal f tp)
vecValDrop sym (VecVal xs) i =
  case vecSizeIsConcrete sym i of
    Just n -> pure (VecVal (V.drop n xs))
    Nothing -> throwUnsupported sym "Dropping a symbolic number of elements from a vector."  


type MuxFn p v = p -> v -> v -> IO v

{-# INLINE muxVector #-}
-- | Mux two vectors of the same length.
muxVector :: IsExprBuilder sym =>
             sym -> MuxFn p (f tp) -> MuxFn p (VecVal f tp)
muxVector sym f p (VecVal x) (VecVal y)
  | V.length x == V.length y = VecVal <$> V.zipWithM (f p) x y
  | otherwise =
      throwUnsupported sym "Cannot merge vectors with different dimensions."


-- | Mux two vectors, possibly of different lengths.
muxVector' ::
  f tp {- ^ Use this value to pad the shorter array -} ->
  MuxFn p (f tp) ->
  MuxFn p (VecVal f tp)
muxVector' undef f c (VecVal pv1) (VecVal pv2) =
  do
    let len = max (V.length pv1) (V.length pv2)
    xs <- V.generateM len $ \i ->
      do
        let x = getPE i pv1
        let y = getPE i pv2
        f c x y
    pure (VecVal xs)
  where
  getPE i pv = fromMaybe undef (pv V.!? i)

--------------------------------------------------------------------------------
-- Partial Vectors


-- | Convert a total vector to a partial one, where all values are initialized.
vecValToPartial ::
  (IsRegValue sym f) =>
  sym ->
  TypeRepr tp ->
  VecVal f tp -> IO (VecVal f (MaybeType tp))
vecValToPartial sym _tp (VecVal xs) =
  pure (VecVal (partialToMaybe . justPartExpr sym <$> xs))

-- | Make a completely uninitialized partial vector
vecValUninit ::
  (IsSymExprBuilder sym, VecSize sym i, IsRegValue sym f) =>
  sym       {- ^ Symbolic expression builder -} ->
  i         {- ^ Size of vector -} ->
  IO (VecVal f (MaybeType tp))
vecValUninit sym sz =
  case vecSizeIsConcrete sym sz of
    Just n -> pure (VecVal (V.replicate n (partialToMaybe Unassigned)))
    Nothing ->
      throwUnsupported sym "Uninitialized vector of symbolic size."


-- | Resize a partial vector to a different size.
vecValResizePartial ::
  (IsSymExprBuilder sym, VecSize sym i, IsRegValue sym f) =>
  sym                           {- ^ Symbolic expression builder -} ->
  i                             {- ^ New size of vector -} ->
  VecVal f (MaybeType tp)       {- ^ Vector to resize -} ->
  IO (VecVal f (MaybeType tp))  {- ^ Resized vector -}
vecValResizePartial sym sz (VecVal xs) =
  case vecSizeIsConcrete sym sz of
    Just new_sz -> pure $ VecVal $ V.generate new_sz $ \i ->
      fromMaybe (partialToMaybe Unassigned) (xs V.!? i)
    Nothing -> throwUnsupported sym "Resize to symbolic size."

-- | Resize a vector to a different size.
vecValResize ::
  (IsSymExprBuilder sym, VecSize sym i, IsRegValue sym f) =>
  sym           {- ^ Symbolic expression builder -} ->
  i             {- ^ New size of vector -} ->
  VecVal f tp   {- ^ Vector to resize -} ->
  IO (VecVal f (MaybeType tp))  {- ^ Resized vector -}
vecValResize sym sz (VecVal xs) =
  case vecSizeIsConcrete sym sz of
    Just new_sz -> pure $ VecVal $ V.generate new_sz $ \i ->
      partialToMaybe (maybePartExpr sym (xs V.!? i))
    Nothing -> throwUnsupported sym "Resize to symbolic size."

  


--------------------------------------------------------------------------------


-- | Ensure that symbolic index is in the given concrete range
ensureInRange ::
  (VecMonad sym m, VecSize sym i, IsSymBackend sym bak) =>
  bak             {- ^ Symbolic back-end -} ->
  Natural         {- ^ Lower bound (inclusive) -} ->
  Natural         {- ^ Upper bound (inclusive_ -} ->
  i               {- ^ Index -} ->
  String          {- ^ Note for error messages -} ->
  m ()
ensureInRange bak l h si msg =
  vecPre sym >>= \pre ->
  liftIO $
  do    
     l_sym   <- vecSizeLit sym l
     h_sym   <- vecSizeLit sym h
     above   <- vecSizeLeq sym l_sym si   
     below   <- vecSizeLeq sym si h_sym
     both    <- andPred sym above below
     inRange <- impliesPred sym pre both
     assert bak inRange (AssertFailureSimError msg details)
  where
  sym = backendGetSym bak
  details = unwords ["Range is", show (l, h)]


indexVectorConcrete ::
  (VecMonad sym m, IsSymBackend sym bak) =>
  bak                                     {- ^ Symbolic backend -} ->
  V.Vector a                              {- ^ Lookup in this vector -} ->
  Int                                     {- ^ Index -} ->
  m a
indexVectorConcrete bak xs i =
  case xs V.!? i of
    Just a -> pure a
    Nothing -> vecAbort bak (AssertFailureSimError msg details)
  where
  msg     = "Vector index out of range"
  details = unwords ["Range is", show (0 :: Int, V.length xs)]

-- | Get value stored in vector at a symbolic index.
indexVector ::
  (VecMonad sym m, VecSize sym i, IsSymBackend sym bak) =>
  bak                                     {- ^ Symbolic backend -} ->
  (Pred sym -> a -> a -> IO a)            {- ^ Ite function -} ->
  V.Vector a                              {- ^ Lookup in this vector -} ->
  i                                       {- ^ Index -} ->
  m a
indexVector bak iteFn v si
  | n > 0 =
    case vecSizeIsConcrete sym si of
      Just i -> indexVectorConcrete bak v i
      Nothing
        | n > 0 ->
          do 
             let predFn i = vecSizeEq sym si =<< vecSizeLit sym i
             let getElt i = pure (v V.! fromIntegral i)
             let ub       = fromIntegral (n - 1)
             ensureInRange bak 0 ub si msg
             liftIO (muxRange predFn iteFn getElt 0 ub)
  | otherwise = vecAbort bak (AssertFailureSimError msg details)
  where
  sym     = backendGetSym bak
  n       = V.length v
  msg     = "Vector index out of range"
  details = unwords ["Range is", show (0 :: Int, n)]


-- | Update a vector at a given index.
adjVectorConcrete ::
  (VecMonad sym m, IsSymBackend sym bak) =>
  bak                           {- ^ Symbolic backend -} ->
  V.Vector a                    {- ^ Vector to update -} ->
  Int                           {- ^ Index to update -} ->
  (a -> m a)                    {- ^ Apply this to compute the new value from the old value -} ->
  m (V.Vector a)
adjVectorConcrete bak v i newVal
  | i < V.length v =
    do
      new <- newVal (v V.! i)
      pure (v V.// [(fromIntegral i, new)])
  | otherwise = vecAbort bak (AssertFailureSimError msg details)
  where
  msg       = "Illegal vector index"
  details   = "Illegal index " ++ show i ++ "given to updateVector"


-- | Update a vector at a given index.
adjVector ::
  (VecMonad sym m, VecSize sym i, IsSymBackend sym bak) =>
  bak                           {- ^ Symbolic backend -} ->
  (Pred sym -> a -> a -> IO a)  {- ^ Ite function -} ->
  V.Vector a                    {- ^ Vector to update -} ->
  i                             {- ^ Index to update -} ->
  (a -> m a)                    {- ^ Apply this to compute the new value from the old value -} ->
  m (V.Vector a)
adjVector bak iteFn v si newVal =
  case vecSizeIsConcrete sym si of
    Just i  -> adjVectorConcrete bak v i newVal
    Nothing ->
      do
        ensureInRange bak 0 (fromIntegral (n-1)) si msg
        V.generateM n setFn
      where
      setFn j =
        do
          let old = v V.! j
          pre <- vecPre sym
          new <- newVal old
          liftIO $
            do
              c <- andPred sym pre =<<
                    (vecSizeEq sym si =<< vecSizeLit sym (fromIntegral j))
              iteFn c new old
  where
  sym       = backendGetSym bak
  n         = V.length v
  msg       = "Illegal vector index"

