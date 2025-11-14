{-# Language GADTs, KindSignatures #-}
module Lang.Crucible.Simulator.VecValue
  ( VecVal
  , vecValLit
  , muxVector
  , vecValToVec
  , vecValReplicate
  , vecValIsEmpty
  , vecValSize
  , vecValGetEntry
  , vecValSetEntry
  , vecValCons

  , ensureInRange
  ) where

import GHC.Natural(Natural)
import Data.Kind(Type)
import qualified Data.Vector as V
import Control.Monad(join)
import qualified Control.Exception as Ex
import What4.Interface
import Lang.Crucible.Types
import Lang.Crucible.Backend
import Lang.Crucible.Simulator.SimError

data VecVal (f :: CrucibleType -> Type) (tp :: CrucibleType) where
  VecVal :: V.Vector (f tp) -> VecVal f tp

vecValLit :: V.Vector (f tp) -> VecVal f tp
vecValLit xs = VecVal xs

vecValToVec :: VecVal f tp -> IO (V.Vector (f tp))
vecValToVec (VecVal xs) = pure xs

vecValReplicate :: IsExprBuilder sym => sym -> Natural -> f tp -> IO (VecVal f tp)
vecValReplicate _sym n v = pure (VecVal (V.replicate (fromIntegral n) v))

vecValIsEmpty :: IsExprBuilder sym => sym -> VecVal f tp -> IO (Pred sym)
vecValIsEmpty sym (VecVal xs) = pure (backendPred sym (V.null xs))

vecValSize :: IsExprBuilder sym => sym -> VecVal f tp -> IO (SymNat sym)
vecValSize sym (VecVal xs) = natLit sym (fromIntegral (V.length xs))

vecValGetEntry ::
  IsSymBackend sym bak =>
  bak ->
  (Pred sym -> f tp -> f tp -> IO (f tp))   {- ^ Ite function -} ->
  VecVal f tp ->
  SymNat sym ->
  IO (f tp)
vecValGetEntry bak ite (VecVal xs) i = indexVectorWithSymNat bak ite xs i

-- | Update a vector at a given natural number index.
vecValSetEntry :: IsSymBackend sym bak =>
  bak                                       {- ^ Symbolic backend -} ->
  (Pred sym -> f tp -> f tp -> IO (f tp))   {- ^ Ite function -} ->
  VecVal f tp                               {- ^ Vector to update -} ->
  SymNat sym                                {- ^ Index to update -} ->
  f tp                                      {- ^ New value to assign -} ->
  IO (VecVal f tp)
vecValSetEntry bak ite (VecVal xs) i v =
  VecVal <$> updateVectorWithSymNat bak ite xs i v

vecValCons :: IsExprBuilder sym => sym -> f tp -> VecVal f tp -> IO (VecVal f tp)
vecValCons _sym x (VecVal xs) = pure (VecVal (V.cons x xs))

type MuxFn p v = p -> v -> v -> IO v

{-# INLINE muxVector #-}
muxVector :: IsExprBuilder sym =>
             sym -> MuxFn p (f tp) -> MuxFn p (VecVal f tp)
muxVector sym f p (VecVal x) (VecVal y)
  | V.length x == V.length y = VecVal <$> V.zipWithM (f p) x y
  | otherwise =
      throwUnsupported sym "Cannot merge vectors with different dimensions."

-- | Get value stored in vector at a symbolic index.
indexVectorWithSymNat :: IsSymBackend sym bak
                      => bak
                      -> (Pred sym -> a -> a -> IO a)
                         -- ^ Ite function
                      -> V.Vector a
                      -> SymNat sym
                      -> IO a
indexVectorWithSymNat bak iteFn v si =
  Ex.assert (n > 0) $
  case asNat si of
    Just i | 0 <= i && i < n -> return (v V.! fromIntegral i)
           | otherwise -> addFailedAssertion bak (AssertFailureSimError msg details)
    Nothing ->
      do let sym = backendGetSym bak
         let predFn i = natEq sym si =<< natLit sym i
         let getElt i = return (v V.! fromIntegral i)
         ensureInRange bak 0 (n - 1) si msg
         muxRange predFn iteFn getElt 0 (n - 1)
  where
  n   = fromIntegral (V.length v)
  msg = "Vector index out of range"
  details = unwords ["Range is", show (0 :: Natural, n)]


-- | Update a vector at a given natural number index.
updateVectorWithSymNat :: IsSymBackend sym bak
                       => bak
                          -- ^ Symbolic backend
                       -> (Pred sym -> a -> a -> IO a)
                          -- ^ Ite function
                       -> V.Vector a
                          -- ^ Vector to update
                       -> SymNat sym
                          -- ^ Index to update
                       -> a
                          -- ^ New value to assign
                       -> IO (V.Vector a)
updateVectorWithSymNat bak iteFn v si new_val = do
  adjustVectorWithSymNat bak iteFn v si (\_ -> return new_val)

-- | Update a vector at a given natural number index.
adjustVectorWithSymNat :: IsSymBackend sym bak
                       => bak
                          -- ^ Symbolic backend
                       -> (Pred sym -> a -> a -> IO a)
                          -- ^ Ite function
                       -> V.Vector a
                          -- ^ Vector to update
                       -> SymNat sym
                          -- ^ Index to update
                       -> (a -> IO a)
                          -- ^ Adjustment function to apply
                       -> IO (V.Vector a)
adjustVectorWithSymNat bak iteFn v si adj =
  case asNat si of
    Just i

      | i < fromIntegral n ->
        do new_val <- adj (v V.! fromIntegral i)
           return $ v V.// [(fromIntegral i, new_val)]

      | otherwise ->
        addFailedAssertion bak $ AssertFailureSimError msg (details i)

    Nothing ->
      do ensureInRange bak 0 (fromIntegral (n-1)) si msg
         V.generateM n setFn
      where
      setFn j =
        do  let sym = backendGetSym bak
            -- Compare si and j.
            c <- natEq sym si =<< natLit sym (fromIntegral j)
            -- Select old value or new value
            case asConstantPred c of
              Just True  -> adj (v V.! j)
              Just False -> return (v V.! j)
              Nothing ->
                do new_val <- adj (v V.! j)
                   iteFn c new_val (v V.! j)

  where
  n = V.length v
  msg = "Illegal vector index"
  details i = "Illegal index " ++ show i ++ "given to updateVectorWithSymNat"



ensureInRange ::
  IsSymBackend sym bak =>
  bak ->
  Natural ->
  Natural ->
  SymNat sym ->
  String ->
  IO ()
ensureInRange bak l h si msg =
  do let sym = backendGetSym bak
     l_sym <- natLit sym l
     h_sym <- natLit sym h
     inRange <- join $ andPred sym <$> natLe sym l_sym si <*> natLe sym si h_sym
     assert bak inRange (AssertFailureSimError msg details)
  where details = unwords ["Range is", show (l, h)]