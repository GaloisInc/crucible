-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Analysis.Postdom
-- Description      : Populates postdominator entries in CFG blocks.
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides a method for populating the postdominator fields
-- in blocks of a Core SSA-form CFG.
------------------------------------------------------------------------
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
module Lang.Crucible.Analysis.Postdom
  ( postdomInfo
  , breakpointPostdomInfo
  , validatePostdom
  ) where

import           Control.Monad.State
import qualified Data.Bimap as Bimap
import           Data.Functor.Const
import qualified Data.Graph.Inductive as G
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import qualified Data.Set as Set

import           Lang.Crucible.CFG.Core

-- | Convert a block ID to a node
toNode :: BlockID blocks ctx -> G.Node
toNode (BlockID b) = 1 + Ctx.indexVal b

-- | Create
reverseEdge :: Int -> Block ext blocks ret ctx -> G.LEdge ()
reverseEdge d b = (d, toNode (blockID b), ())

-- | For a given block with out edges l, return edges from
-- each block in @l@ to @b@.
inEdges :: Block ext blocks ret ctx -> [G.LEdge ()]
inEdges b =
  case withBlockTermStmt b (\_ -> termStmtNextBlocks) of
    Nothing -> [reverseEdge 0 b]
    Just l -> (\(Some n) -> toNode n `reverseEdge` b) <$> l

inEdgeGraph :: BlockMap ext blocks ret -> [Some (BlockID blocks)] -> G.UGr
inEdgeGraph m breakpointIds = G.mkGraph ((,()) <$> nodes) edges
  where nodes = 0 : toListFC (toNode . blockID) m
        cfgEdges = foldMapFC inEdges m
        breakpointEdges = map (\(Some bid) -> reverseEdge 0 (getBlock bid m))
                              breakpointIds
        edges = cfgEdges ++ breakpointEdges

-- | Return subgraph of nodes reachable from given node.
reachableSubgraph :: G.Node -> G.UGr -> G.UGr
reachableSubgraph initNode g = G.mkGraph nl el
  where reachableNodes = Set.fromList $ G.bfs initNode g
        keepNode = (`Set.member` reachableNodes)
        nl = filter (\(n,_) -> keepNode n) (G.labNodes g)

        keepEdge (s,e,_) = keepNode s && keepNode e
        el = filter keepEdge (G.labEdges g)

nodeToBlockIDMap :: BlockMap ext blocks ret
                 -> Map G.Node (Some (BlockID blocks))
nodeToBlockIDMap =
  foldrFC (\b -> Map.insert (toNode (blockID b)) (Some (blockID b)))
          Map.empty

postdomMap :: forall ext blocks ret
            . BlockMap ext blocks ret
           -> [Some (BlockID blocks)]
           -> Map (Some (BlockID blocks)) [Some (BlockID blocks)]
postdomMap m breakpointIds = r
  where g0 = inEdgeGraph m breakpointIds
        g = reachableSubgraph 0 g0

        idMap = nodeToBlockIDMap m
        f :: Int -> Maybe (Some (BlockID blocks))
        f 0 = Nothing
        f i = Map.lookup i idMap
        -- Map each block to the postdominator for the block.
        r = Map.fromList
          [ (pd_id, mapMaybe f l)
          | (pd,_:l)  <- G.dom g 0
          , pd > 0
          , let Just pd_id = Map.lookup pd idMap
          ]

postdomAssignment :: forall ext blocks ret
                   . BlockMap ext blocks ret
                  -> [Some (BlockID blocks)]
                  -> CFGPostdom blocks
postdomAssignment m breakpointIds = fmapFC go m
  where pd = postdomMap m breakpointIds
        go :: Block ext blocks ret c -> Const [Some (BlockID blocks)] c
        go b = Const $ fromMaybe [] (Map.lookup (Some (blockID b)) pd)

-- | Compute posstdom information for CFG.
postdomInfo :: CFG ext b i r -> CFGPostdom b
postdomInfo g = postdomAssignment (cfgBlockMap g) []

breakpointPostdomInfo :: CFG ext b i r -> [BreakpointName] -> CFGPostdom b
breakpointPostdomInfo g breakpointNames = postdomAssignment (cfgBlockMap g) $
  mapMaybe (\nm -> Bimap.lookup nm (cfgBreakpoints g)) breakpointNames

blockEndsWithError :: Block ext blocks ret args -> Bool
blockEndsWithError b =
  withBlockTermStmt b $ \_ ts ->
    case ts of
      ErrorStmt{} -> True
      _ -> False

addErrorIf :: Bool -> String -> State [String] ()
addErrorIf True msg = modify $ (msg:)
addErrorIf False _ = return ()

validateTarget :: CFG ext blocks init ret
               -> CFGPostdom blocks
               -> String
               -- ^ Identifier for error.
               -> [Some (BlockID blocks)]
               -- ^ Postdoms for source block.
               -> Some (BlockID blocks)
               -- ^ Target
               -> State [String] ()
validateTarget _ pdInfo src (Some pd:src_postdoms) (Some tgt)
  | isJust (testEquality pd tgt) =
      addErrorIf (src_postdoms /= tgt_postdoms) $
        "Unexpected postdominators from " ++ src ++ " to " ++ show tgt ++ "."
  where Const tgt_postdoms = pdInfo Ctx.! blockIDIndex tgt
validateTarget g pdInfo src src_postdoms (Some tgt)
  | blockEndsWithError tgt_block =
    return ()
  | otherwise = do
      let tgt_len = length tgt_postdoms
      let src_len = length src_postdoms
      addErrorIf (tgt_len < src_len) $
        "Unexpected postdominators from " ++ src ++ " to " ++ show tgt ++ "."
      let tgt_prefix = drop (tgt_len - src_len) tgt_postdoms
      addErrorIf (src_postdoms /= tgt_prefix) $
        "Unexpected postdominators from " ++ src ++ " to " ++ show tgt ++ "."
  where tgt_block = getBlock tgt (cfgBlockMap g)
        Const tgt_postdoms = pdInfo Ctx.! blockIDIndex tgt

validatePostdom :: CFG ext blocks init ret
                -> CFGPostdom blocks
                -> [String]
validatePostdom g pdInfo = flip execState [] $ do
  forFC_ (cfgBlockMap g) $ \b -> do
    let Const b_pd = pdInfo Ctx.! blockIDIndex (blockID b)
    let loc = show (cfgHandle g) ++ show (blockID b)
    mapM_ (validateTarget g pdInfo loc b_pd) (nextBlocks b)

    withBlockTermStmt b $ \_ ts -> do
      case ts of
        Jump tgt -> do
          validateTarget g pdInfo loc b_pd (jumpTargetID tgt)
        Br _ tgt1 tgt2  -> do
          validateTarget g pdInfo loc b_pd (jumpTargetID tgt1)
          validateTarget g pdInfo loc b_pd (jumpTargetID tgt2)
        MaybeBranch _ _ x y -> do
          validateTarget g pdInfo loc b_pd (switchTargetID x)
          validateTarget g pdInfo loc b_pd (jumpTargetID   y)
        VariantElim _ _ s -> do
          traverseFC_ (validateTarget g pdInfo loc b_pd . switchTargetID) s
        Return{} -> do
          addErrorIf (not (null b_pd)) $
            "Expected empty postdom in " ++ loc ++ "."
        TailCall{} -> do
          addErrorIf (not (null b_pd)) $
            "Expected empty postdom in " ++ loc ++ "."
        ErrorStmt{} -> do
          addErrorIf (not (null b_pd)) $
            "Expected empty postdom in " ++ loc ++ "."
