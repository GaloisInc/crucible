{-# LANGUAGE GADTs #-}
{-|
Module           : Lang.Crucible.Utils.PartitioningMuxTree
Copyright        : (c) Galois, Inc 2018-2021
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>

This module defines a @PartitioningMuxTree@ type that notionally represents
a collection of values organized into an if-then-else tree.  This
data structure allows values that otherwise do not have a useful notion
of symbolic values to nonetheless be merged as control flow merge points
by simply remembering which concrete values were obtained, and the
logical conditions under which they were found.

Unlike the 'Lang.Crucible.Utils.MuxTree.MuxTree', this data structure can mux
values that contain symbolic parts.  To use this, the type must be
/partitionable/ into a concrete 'Skeleton' and a symbolic portion.  The concrete
'Skeleton' is specified by implementing the 'OrdSkel' class for the type.  The
symbolic portion is specified by the type-specific mux function provided by
'toPartitioningMuxTree'.

-}

module Lang.Crucible.Utils.PartitioningMuxTree (
  PartitioningMuxTree,
  toPartitioningMuxTree,
  viewPartitioningMuxTree,
  mergePartitioningMuxTree,
  Skeleton(..),
  OrdSkel(..)
  ) where

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.List.NonEmpty as DLN
import qualified Data.Map.Merge.Strict as MapMerge
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Classes as PC
import           GHC.Stack ( HasCallStack )
import qualified What4.Interface as WI

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Panic as CP

-- | A newtype around values that delegates its 'Ord' and 'Eq' instances to 'OrdSkel'
--
-- The idea is that the 'Skeleton' represents the non-symbolic portion of a
-- value (i.e., partitioning the value into symbolic and concrete portions).
--
-- This delegation enables partial equality/ordering comparisons to not pollute
-- the global 'Ord' instance pool.
newtype Skeleton a = Skeleton a

-- | An ordering over the concrete (i.e., non symbolic) portions of a structure of type @t@
--
--
class OrdSkel t where
  compareSkel :: t -> t -> Ordering

compareSkelF :: (PC.OrdF t) => t a -> t b -> Ordering
compareSkelF x y = PC.toOrdering $ PC.compareF x y

compareSkelF2 :: (PC.OrdF t, PC.OrdF (u a)) => t a -> u a b -> t a' -> u a' b' -> Ordering
compareSkelF2 x x2 y y2 =
  case PC.compareF x y of
    PC.LTF -> LT
    PC.EQF -> compareSkelF x2 y2
    PC.GTF -> GT

instance OrdSkel a => Eq (Skeleton a) where
    Skeleton x == Skeleton y = compareSkel x y == EQ

instance OrdSkel a => Ord (Skeleton a) where
    compare (Skeleton x) (Skeleton y) = compareSkel x y

-- | A mux tree that selects values of type @a@ based on a condition (expressed
-- as a 'WI.Pred')
--
-- NOTE: The invariant is that the mux tree cannot be empty
newtype PartitioningMuxTree sym a = PartitioningMuxTree (Map.Map (Skeleton a) (a, WI.Pred sym))

toPartitioningMuxTree :: (CB.IsSymInterface sym)
                      => sym
                      -> a
                      -> PartitioningMuxTree sym a
toPartitioningMuxTree sym a =
  PartitioningMuxTree (Map.singleton (Skeleton a) (a, WI.truePred sym))

-- | View the mapping from values to the predicates under which they are selected
viewPartitioningMuxTree :: PartitioningMuxTree sym a -> DLN.NonEmpty (a, WI.Pred sym)
viewPartitioningMuxTree (PartitioningMuxTree m) =
  case DLN.nonEmpty (Map.elems m) of
    Just l -> l
    Nothing -> CP.panic "PartitioningMuxTree" ["Empty PartitioningMuxTrees are not possible"]

-- | Construct a 'PartitioningMuxTree' from a list of values and the conditions
-- ('WI.Pred') under which they are selected
buildPartitioningMuxTree
  :: (CB.IsSymInterface sym, OrdSkel a)
  => sym
  -- ^ The symbolic backend
  -> (WI.Pred sym -> a -> a -> IO a)
  -- ^ The operation to mux the symbolic portions of two values
  --
  -- This operation sinks the predicate (under which decides
  -- to take the first value or the second when the concrete
  -- skeletons are the same) into any symbolic values in the
  -- @a@.
  -> [(a, WI.Pred sym)]
  -- ^ The values in the tree paired with the conditions
  -- under which they are selected
  -> IO (PartitioningMuxTree sym a)
buildPartitioningMuxTree sym mux values =
  PartitioningMuxTree <$> buildMuxTree Map.empty values
  where
    buildMuxTree m [] = return m
    buildMuxTree m ((value, condition) : rest) =
      case WI.asConstantPred condition of
        Just True -> buildMuxTree (Map.insert (Skeleton value) (value, WI.truePred sym) m) rest
        Just False -> buildMuxTree m rest
        Nothing -> do
          let doUpdate old =
                case old of
                  Nothing ->
                    -- If there was no entry, just add this one
                    return (Just (value, condition))
                  Just (prevValue, prevCondition) -> do
                    -- If there was already an entry for this (concrete
                    -- skeleton) value so we need to mux the two values together
                    muxed <- mux condition value prevValue
                    combinedCondition <- WI.orPred sym condition prevCondition
                    return (Just (muxed, combinedCondition))

          m' <- Map.alterF doUpdate (Skeleton value) m
          buildMuxTree m' rest

-- | Mux together two 'PartitioningMuxTree' values
--
-- NOTE: The object-level mux function /must/ be the same as the one used to
-- construct the initial 'PartitioningMuxTree's.
mergePartitioningMuxTree
  :: (CB.IsSymInterface sym, OrdSkel a, MonadIO m)
  => sym
  -> (WI.Pred sym -> a -> a -> m a)
  -> WI.Pred sym
  -> PartitioningMuxTree sym a
  -> PartitioningMuxTree sym a
  -> m (PartitioningMuxTree sym a)
mergePartitioningMuxTree sym mux p (PartitioningMuxTree m1) (PartitioningMuxTree m2) = do
  notp <- liftIO $ WI.notPred sym p
  m3 <- MapMerge.mergeA (MapMerge.traverseMaybeMissing (filterLeaf p))
                        (MapMerge.traverseMaybeMissing (filterLeaf notp))
                        (MapMerge.zipWithMaybeAMatched mergeLeaf)
                        m1 m2
  return (PartitioningMuxTree m3)
  where
    filterLeaf p_ _k (x, q) = do
      pq <- liftIO $ WI.andPred sym p_ q
      -- Throw away synactically false branches
      case WI.asConstantPred pq of
        Just False -> return Nothing
        _ -> return (Just (x, pq))
    mergeLeaf _k (x, q) (y, r) = do
      qr <- liftIO $ WI.itePred sym p q r
      case WI.asConstantPred qr of
        Just False -> return Nothing
        _ -> do
          xy <- mux p x y
          return (Just (xy, qr))
