{-|
Module           : Lang.Crucible.Utils.MuxTree
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : Rob Dockins <rdockins@galois.com>

This module defines a @MuxTree@ type that notionally represents
a collection of values organized into an if-then-else tree.  This
data structure allows values that otherwise do not have a useful notion
of symbolic values to nonetheless be merged as control flow merge points
by simply remembering which concrete values were obtained, and the
logical conditions under which they were found.

Note that we require an @Ord@ instance on the type @a@ over which we are
building the mux trees.  It is sufficent that this operation be merely
syntactic equality; it is not necessary for correctness that terms with
the same semantics compare equal.
-}

{-# LANGUAGE FlexibleContexts #-}
module Lang.Crucible.Utils.MuxTree
  ( MuxTree
  , toMuxTree
  , mergeMuxTree
  , viewMuxTree
  , muxTreeUnaryOp
  , muxTreeBinOp
  , muxTreeCmpOp
  , collapseMuxTree
  ) where

import           Control.Lens (folded)

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Map

import           What4.Interface
import           Lang.Crucible.Panic

-- | A mux tree represents a collection of if-then-else branches over
--   a collection of values.  Generally, a mux tree is used to provide
--   a way to conditionally merge values that otherwise do not
--   naturally have a merge operation.
newtype MuxTree sym a = MuxTree (Map a (Pred sym))
{- INVARIANT: The map inside a mux tree is non-empty! -}

-- Turn a single value into a trivial mux tree
toMuxTree :: IsExprBuilder sym => sym -> a -> MuxTree sym a
toMuxTree sym v = MuxTree (Map.singleton v (truePred sym))

-- View all the leaf values of the mux tree, along with the
-- conditions that lead to those values.
viewMuxTree :: MuxTree sym a -> [(a, Pred sym)]
viewMuxTree (MuxTree m) = Map.toList m

_conditionMuxTree :: IsExprBuilder sym => sym -> Pred sym -> MuxTree sym a -> IO (MuxTree sym a)
_conditionMuxTree sym p (MuxTree m) = MuxTree <$> Map.traverseMaybeWithKey (conditionMuxTreeLeaf sym p) m

-- | Compute a binary boolean predicate between two mux trees.
--   This operation decomposes the mux trees and compares the
--   all combinations of the underlying values, conditional on
--   the path conditions leading to those values.
muxTreeCmpOp ::
  IsExprBuilder sym =>
  sym ->
  (a -> a -> IO (Pred sym)) {- ^ compute the predicate on the underlying type -} ->
  MuxTree sym a ->
  MuxTree sym a ->
  IO (Pred sym)
muxTreeCmpOp sym f xt yt = orOneOf sym folded =<< sequence zs
  where
  zs = [ do pf <- f x y
            andPred sym pf =<< andPred sym px py
       | (x,px) <- xs
       , (y,py) <- ys
       ]
  xs = viewMuxTree xt
  ys = viewMuxTree yt

-- | Use the provided if-then-else operation to collapse the given mux tree
--   into its underlying type.
collapseMuxTree ::
  IsExprBuilder sym =>
  sym ->
  (Pred sym -> a -> a -> IO a) ->
  MuxTree sym a ->
  IO a
collapseMuxTree _sym ite xt = go (viewMuxTree xt)
  where
  go []         = panic "collapseMuxTree" ["empty mux tree"]
  go [(x,_p)]   = return x
  go ((x,p):xs) = ite p x =<< go xs

buildMuxTree ::
  (Ord a, IsExprBuilder sym) =>
  sym ->
  [(a, Pred sym)] ->
  IO (MuxTree sym a)
buildMuxTree _sym [] = panic "buildMuxTree" ["empty mux tree"]
buildMuxTree sym  xs = go Map.empty xs
  where
  go m [] = return (MuxTree m)
  go m ((z,p):zs) =
     case Map.lookup z m of
       Nothing -> go (Map.insert z p m) zs
       Just q -> do pq <- orPred sym p q
                    case asConstantPred pq of
                      Just False -> go m zs
                      _ -> go (Map.insert z pq m) zs

-- | Apply a unary operation through a mux tree.  The provided operation
--   is applied to each leaf of the tree.
muxTreeUnaryOp ::
  (Ord b, IsExprBuilder sym) =>
  sym ->
  (a -> IO b) ->
  MuxTree sym a ->
  IO (MuxTree sym b)
muxTreeUnaryOp sym op xt =
  do let xs = viewMuxTree xt
     zs <- sequence
            [ do z <- op x
                 return (z,p)
            | (x,p) <- xs
            ]
     buildMuxTree sym zs

-- | Apply a binary operation through two mux trees.  The provided operation
--   is applied pairwise to each leaf of the two trees, and appropriate path
--   conditions are computed for the resulting values.
muxTreeBinOp ::
  (Ord c, IsExprBuilder sym) =>
  sym ->
  (a -> b -> IO c) ->
  MuxTree sym a ->
  MuxTree sym b ->
  IO (MuxTree sym c)
muxTreeBinOp sym op xt yt =
  do let xs = viewMuxTree xt
     let ys = viewMuxTree yt
     zs <- sequence
           [ do p <- andPred sym px py
                z <- op x y
                return (z,p)
           | (x,px) <- xs
           , (y,py) <- ys
           ]
     buildMuxTree sym zs


conditionMuxTreeLeaf ::
  IsExprBuilder sym => sym -> Pred sym -> a -> Pred sym -> IO (Maybe (Pred sym))
conditionMuxTreeLeaf sym p _v pv =
   do p' <- andPred sym p pv
      case asConstantPred p' of
        Just False -> return Nothing
        _ -> return (Just p')

-- | Compute the if-then-else operation on mux trees.
mergeMuxTree ::
  (Ord a, IsExprBuilder sym) =>
  sym ->
  Pred sym ->
  MuxTree sym a ->
  MuxTree sym a ->
  IO (MuxTree sym a)
mergeMuxTree sym p (MuxTree mx) (MuxTree my) =
   do np <- notPred sym p
      MuxTree <$> doMerge np mx my

  where
  f _v px py =
    do p' <- itePred sym p px py
       case asConstantPred p' of
         Just False -> return Nothing
         _ -> return (Just p')

  doMerge np = Map.mergeA (Map.traverseMaybeMissing (conditionMuxTreeLeaf sym p))
                          (Map.traverseMaybeMissing (conditionMuxTreeLeaf sym np))
                          (Map.zipWithMaybeAMatched f)
