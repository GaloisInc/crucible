------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Analysis.DFS
-- Description : Depth-first search algorithm on Crucible CFGs
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Rob Dockins <rdockins@galois.com>
-- Stability   : provisional
--
-- This module defines a generic algorithm for depth-first search
-- traversal of a control flow graph.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Lang.Crucible.Analysis.DFS
( -- * Basic DFS types and algorithms
  DFSEdgeType(..)
, DFSNodeFunc
, DFSEdgeFunc
, dfs
, run_dfs

  -- * Some specific DFS traversals
, dfs_backedge_targets
, dfs_backedges
, dfs_list
, dfs_preorder
, dfs_postorder
) where

import Prelude hiding (foldr)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Foldable

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core

type SomeBlockID blocks = Some (BlockID blocks)

data DFSEdgeType
    = TreeEdge              -- ^ This edge is on the spanning forrest computed by this DFS
    | ForwardOrCrossEdge    -- ^ This edge is either a forward (to a direct decendent in the spanning tree)
                            --   or a cross edge (to a cousin node)
    | BackEdge              -- ^ This edge is a back edge (to an ancestor in the spanning tree).  Every cycle in
                            --   the graph must traverse at least one back edge.
  deriving (Eq, Ord, Show)

-- | Function to update the traversal state when we have finished visiting
--   all of a nodes's reachable children.
type DFSNodeFunc ext blocks a = forall ret ctx. Block ext blocks ret ctx -> a -> a

-- | Function to update the traversal state when traversing an edge.
type DFSEdgeFunc blocks a = DFSEdgeType -> SomeBlockID blocks -> SomeBlockID blocks -> a -> a


-- | Use depth-first search to calculate a set of all the block IDs that
--   are the target of some back-edge, i.e., a set of nodes through which
--   every loop passes.
dfs_backedge_targets :: CFG ext blocks init ret -> Set (SomeBlockID blocks)
dfs_backedge_targets =
  dfs (\_ x -> x)
      (\et _ m x ->
        case et of
          BackEdge -> Set.insert m x
          _ -> x)
      Set.empty


-- | Compute a sequence of all the back edges found in a depth-first search of the given CFG.
dfs_backedges :: CFG ext blocks init ret -> Seq (SomeBlockID blocks, SomeBlockID blocks)
dfs_backedges =
  dfs (\_ x -> x)
      (\et n m x ->
          case et of
            BackEdge -> x Seq.|> (n,m)
            _ -> x)
      Seq.empty

{-
dfs_backedges_string :: CFG blocks init ret -> String
dfs_backedges_string = unlines . map showEdge . toList . dfs_backedges
  where showEdge :: (SomeBlockID blocks, SomeBlockID blocks) -> String
        showEdge (Some n, Some m) = show (n,m)
-}

-- | Compute a sequence of all the edges visited in a depth-first search of the given CFG.
dfs_list :: CFG ext blocks init ret -> Seq (DFSEdgeType, SomeBlockID blocks, SomeBlockID blocks)
dfs_list =
  dfs (\_ x -> x)
      (\et n m x -> x Seq.|> (et,n,m))
      Seq.empty

-- | Compute a postorder traversal of all the reachable nodes in the CFG
dfs_postorder :: CFG ext blocks init ret -> Seq (SomeBlockID blocks)
dfs_postorder =
  dfs (\blk x -> x Seq.|> (Some (blockID blk)))
      (\_ _ _ x -> x)
      Seq.empty

-- | Compute a preorder traversal of all the reachable nodes in the CFG
dfs_preorder :: CFG ext blocks init ret -> Seq (SomeBlockID blocks)
dfs_preorder =
  dfs (\_ x -> x)
      (\et _n m x ->
          case et of
            TreeEdge -> x Seq.|> m
            _ -> x)
      Seq.empty

{-
dfs_list_string :: CFG blocks init ret -> String
dfs_list_string = unlines . map showEdge . toList . dfs_list
  where showEdge :: (DFSEdgeType, SomeBlockID blocks, SomeBlockID blocks) -> String
        showEdge (et, Some n, Some m) = show (et,n,m)
-}

-- | A depth-first search algorithm on a block map.
--
--   The DFSNodeFunc and DFSEdgeFunc define what we are computing. The DFSEdgeFunc is called
--   on each edge.  The edges are classified according to standard depth-first search
--   terminology.  A tree edge is an edge in the discovered spanning tree.  A back edge
--   goes from a child to an ancestor in the spanning tree.  A ForwardOrCross edge travels
--   either from an ancestor to a child (but not a tree edge), or between two unrelated nodes.
--   The forward/cross case can be distinguished, if desired, by tracking the order in which
--   nodes are found.  A forward edge goes from a low numbered node to a high numbered node,
--   but a cross edge goes from a high node to a low node.
--
--   The DFSNodeFunc is called on each block _after_ the DFS has processed all its fresh reachable
--   children; that is, as the search is leaving the given node.  In particular, using the DFSNodeFunc
--   to put the blocks in a queue will give a postorder traversal of the discovered nodes.
--   Contrarywise, using the DFSEdgeFunc to place blocks in a queue when they occur in a TreeEdge
--   will give a preorder traversal of the discovered nodes.
--
--   We track the lifecycle of nodes by using two sets; an ancestor set and a black set.
--   Nodes are added to the ancestor set as we pass down into recursive calls, and changes
--   to this set are discarded upon return.  The black set records black nodes (those whose
--   visit is completed), and changes are threaded through the search.
--
--   In the standard parlance, a node is white if it has not yet been discovered; it is
--   in neither the ancestor nor black set.  A node is grey if it has been discovered, but
--   not yet completed; such a node is in the ancestor set, but not the black set.  A node
--   is black if its visit has been completed; it is in the black set and not in the ancestor
--   set.  INVARIANT: at all times, the ancestor set and black set are disjoint.
--   After a DFS is completed, all visited nodes will be in the black set; any nodes not in the
--   black set are unreachable from the initial node.

dfs :: DFSNodeFunc ext blocks a
    -> DFSEdgeFunc blocks a
    -> a
    -> CFG ext blocks init ret
    -> a
dfs visit edge x cfg =
   fst $ run_dfs
             visit
             edge
             (cfgBlockMap cfg)
             Set.empty
             (cfgEntryBlockID cfg)
             (x, Set.empty)


-- | Low-level depth-first search function.  This exposes more of the moving parts
--   than `dfs` for algorithms that need more access to the guts.
run_dfs :: forall ext blocks a ret cxt
         . DFSNodeFunc ext blocks a      -- ^ action to take after a visit is finished
        -> DFSEdgeFunc blocks a      -- ^ action to take for each edge
        -> BlockMap ext blocks ret       -- ^ CFG blocks to search
        -> Set (SomeBlockID blocks)  -- ^ ancestor nodes
        -> BlockID blocks cxt        -- ^ a white node to visit
        -> (a, Set (SomeBlockID blocks)) -- ^ Partially-computed value and initial black set
        -> (a, Set (SomeBlockID blocks)) -- ^ Computed value and modified black set
run_dfs visit edge bm = visit_id

 where visit_id :: forall cxt'
                 . Set (SomeBlockID blocks)
                -> BlockID blocks cxt'
                -> (a, Set (SomeBlockID blocks))
                -> (a, Set (SomeBlockID blocks))
       visit_id an i (x,black) =
          let block = getBlock i bm
              -- Insert index 'i' into the ancestor set before the recursive call
              (x',black') = visit_block (Set.insert (Some i) an) block (x, black)

              -- After the recursive call has completed, add 'i' to the black set
              -- and call the node visit function
           in (visit block x', Set.insert (Some i) black')

       visit_block :: Set (SomeBlockID blocks)
                   -> Block ext blocks ret ctx
                   -> (a, Set (SomeBlockID blocks))
                   -> (a, Set (SomeBlockID blocks))
       visit_block an block =
           -- Get a list of all the next block ids we might jump to next, and visit them one by one,
           -- composting together their effects on the partial computation and black set.
           withBlockTermStmt block $ \_loc t ->
              foldr (\m f -> f . visit_edge an (Some (blockID block)) m) id
                 $ fromMaybe [] $ termStmtNextBlocks t

       -- Given source and target block ids, examine the ancestor and black sets
       -- to discover if the node we are about to visit is a white, grey or black node
       -- and classify the edge accordingly.  Recursively visit the target node if it is white.
       visit_edge :: Set (SomeBlockID blocks) -- ^ ancestor set
                  -> SomeBlockID blocks       -- ^ source block id
                  -> SomeBlockID blocks       -- ^ target block id
                  -> (a, Set (SomeBlockID blocks))
                  -> (a, Set (SomeBlockID blocks))
       visit_edge an n m@(Some m') (x, black)
           | Set.member m an =    -- grey node, back edge
                (edge BackEdge n m x, black)

           | Set.member m black = -- black node, forward/cross edge
                (edge ForwardOrCrossEdge n m x, black)

           | otherwise =          -- white node, tree edge; recusively visit
                visit_id an m' (edge TreeEdge n m x, black)
