{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module WTO (
  wtoTests
  ) where

import Control.Applicative
import Control.Monad ( replicateM, unless )
import qualified Control.Monad.State.Strict as St
import qualified Data.Foldable as F
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Prelude

import qualified Test.QuickCheck as QC
import qualified Test.Tasty as T
import qualified Test.Tasty.QuickCheck as T

import Lang.Crucible.Analysis.Fixpoint.Components

wtoTests :: T.TestTree
wtoTests = T.testGroup "WeakTopologicalOrdering" [
  T.testProperty "prop_reachableInWTO" prop_reachableInWTO,
  T.testProperty "prop_validWTO" prop_validWTO
  ]

-- | Test that all reachable nodes in the graph are present in the
-- weak topological ordering
prop_reachableInWTO :: RandomGraph -> Bool
prop_reachableInWTO gp = dfsReachedNodes dfs == S.fromList (concatMap F.toList wto)
  where
    dfs = reachable gp
    (root, sf) = toCFG gp
    wto = weakTopologicalOrdering sf root

-- | Test that the weak topological ordering property holds for the
-- WTO we compute.
--
-- That property is defined in terms of a relation w(c), which
-- evaluates to the set of heads of the nested components containing
-- the vertex c.
--
-- For every edge u->v:
--
--   (u < v AND v not in w(u)) OR (v <= u AND v in w(u))
--
-- where v <= u means that u->v is a backedge.
prop_validWTO :: RandomGraph -> Bool
prop_validWTO gp@(RG edges) =
  and [ (isBackEdge e && (v `vertexInWC` u)) || not (v `vertexInWC` u)
      | e@(u, v) <- edges
      , isReachableEdge e
      ]
  where
    dfs = reachable gp
    (root, sf) = toCFG gp
    wto = weakTopologicalOrdering sf root
    cchs = indexContainingComponentHeads wto
    isReachableEdge (src, _) = src `S.member` dfsReachedNodes dfs
    isBackEdge e = e `S.member` dfsBackEdges dfs
    vertexInWC v c = maybe False (S.member v) $ M.lookup c cchs

-- | This is the w(c) relation from the WTO criteria
--
-- The map keys are the cs
indexContainingComponentHeads :: (Ord n) => [WTOComponent n] -> M.Map n (S.Set n)
indexContainingComponentHeads cs = St.execState (mapM_ (go []) cs) M.empty
  where
    go heads c =
      case c of
        Vertex v -> St.modify' $ M.insert v (S.fromList heads)
        SCC (SCCData { wtoHead = h
                     , wtoComps = cs'
                     }) -> do
          let heads' = h : heads
          St.modify' $ M.insert h (S.fromList heads')
          mapM_ (go heads') cs'

newtype NodeId = NID Int
  deriving (Eq, Show)

instance QC.Arbitrary NodeId where
  arbitrary = QC.sized mkNodeId
    where
      mkNodeId n = NID <$> QC.choose (0, n)

newtype RandomGraph = RG [(Int, Int)]
  deriving (Show)

instance QC.Arbitrary RandomGraph where
  arbitrary = QC.sized mkRandomGraph

-- | Make an arbitrary graph by deciding on a number of edges and then
-- generating random edges.  Note that we always increment the size so
-- that we don't get empty graphs.
--
-- The graphs are not all connected.
mkRandomGraph :: Int -> QC.Gen RandomGraph
mkRandomGraph ((+ 1) -> sz) = do
  nEdges <- QC.choose (2, 2*sz)
  srcs <- replicateM nEdges (QC.choose (0, sz))
  dsts <- replicateM nEdges (QC.choose (0, sz))
  return $! RG (unique (zip srcs dsts))

-- | A DFS result; it additionally contains a list of back edges
-- discovered during its traversal
data DFS = DFS { dfsReachedNodes :: S.Set Int
               , dfsBackEdges :: S.Set (Int, Int)
               , dfsStart :: S.Set Int
               , dfsFinish :: S.Set Int
               }

-- | Compute the DFS of a random graph from its root.
reachable :: RandomGraph -> DFS
reachable gp =
  St.execState (go root) s0
  where
    s0 = DFS { dfsReachedNodes = S.empty
             , dfsBackEdges = S.empty
             , dfsStart = S.empty
             , dfsFinish = S.empty
             }
    (root, sf) = toCFG gp
    go n = do
      markDiscovered n
      F.forM_ (sf n) $ \successor -> do
        disc <- isDiscovered successor
        case disc of
          False -> go successor
          True -> do
            fin <- isFinished successor
            unless fin $ addBackedge (n, successor)
      markFinished n

type M a = St.State DFS a

markDiscovered :: Int -> M ()
markDiscovered v = St.modify' $ \s ->
  s { dfsReachedNodes = S.insert v (dfsReachedNodes s)
    , dfsStart = S.insert v (dfsStart s)
    }

markFinished :: Int -> M ()
markFinished v = St.modify' $ \s ->
  s { dfsFinish = S.insert v (dfsFinish s) }

addBackedge :: (Int, Int) -> M ()
addBackedge be = St.modify' $ \s -> s { dfsBackEdges = S.insert be (dfsBackEdges s) }

isDiscovered :: Int -> M Bool
isDiscovered n = S.member n <$> St.gets dfsReachedNodes

isFinished :: Int -> M Bool
isFinished n = S.member n <$> St.gets dfsFinish

unique :: (Ord a) => [a] -> [a]
unique = S.toList . S.fromList

-- | Return the root and the successor function for the graph.
--
-- Not defined for empty graphs
toCFG :: RandomGraph -> (Int, (Int -> [Int]))
toCFG (RG []) = error "Empty graph"
toCFG (RG edges@((s0, _) : _)) =
  (s0, \n -> [ dst | (src, dst) <- edges, n == src])


