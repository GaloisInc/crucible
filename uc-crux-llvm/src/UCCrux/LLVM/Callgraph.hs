{-
Module           : UCCrux.LLVM.Callgraph
Description      : Callgraph data type and utilities
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DeriveFunctor #-}

module UCCrux.LLVM.Callgraph
  ( PartEdge
  , peTag
  , peEndpoint
  , Callgraph
  , edges
  , check
  , empty
  , singleton
  , outgoing
  , incoming
  , callees
  , callers
  , cgBimap
  , Edge(..)
  , insertEdge
  , fromList
  )
where

import           Data.Bifunctor (Bifunctor(bimap))
import qualified Data.Bifunctor as Bi
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set

import           UCCrux.LLVM.Errors.Panic (panic)

-- | Two thirds of a labeled edge: a label and one endpoint
data PartEdge tag a
  = PartEdge
      { -- | Edge label
        peTag :: tag
        -- | Edge endpoint
      , peEndpoint :: a
      }
  deriving (Eq, Ord, Functor, Show)

instance Bifunctor PartEdge where
  bimap f g e =
    e { peTag = f (peTag e)
      , peEndpoint = g (peEndpoint e)
      }

-- | A program callgraph.
--
-- This type has three parameters:
--
-- * @tag@ is the type of edge labels (e.g., weights, control-flow contexts)
-- * @ee@ is the type of callees (e.g., functions)
-- * @er@ is the type of callers (e.g., functions, instructions, or expressions)
data Callgraph tag ee er
  = Callgraph
      { cgCallees :: Map er (Set (PartEdge tag ee))
      , cgCallers :: Map ee (Set (PartEdge tag er))
      }
  deriving (Eq, Ord, Show)

-- Utility, not exported
setFold :: Ord a => (k -> v -> Set a) -> Map k v -> Set a
setFold f = Map.foldrWithKey (\k v acc -> Set.union (f k v) acc) Set.empty

-- | Edges from the perspective of 'cgCallees'. Should be identical to
-- 'calleeEdges'.
callerEdges ::
  (Ord ee, Ord er, Ord tag) =>
  Callgraph tag ee er ->
  Set (Edge tag ee er)
callerEdges cg = setFold (\er es -> mkCallerEdges er es) (cgCallees cg)
  where
    mkCallerEdges ee partEdges =
      Set.map (\er -> Edge (peEndpoint er) ee (peTag er)) partEdges

-- | Edges from the perspective of 'cgCallers'. Should be identical to
-- 'callerEdges'.
calleeEdges ::
  (Ord ee, Ord er, Ord tag) =>
  Callgraph tag ee er ->
  Set (Edge tag ee er)
calleeEdges cg = setFold (\ee es -> mkCalleeEdges ee es) (cgCallers cg)
  where
    mkCalleeEdges er partEdges =
      Set.map (\ee -> Edge er (peEndpoint ee) (peTag ee)) partEdges

-- | All of the edges in the callgraph.
edges :: (Ord ee, Ord er, Ord tag) => Callgraph tag ee er -> Set (Edge tag ee er)
edges = callerEdges

-- | Panic if this 'Callgraph' violates its invariants
--
-- Invariant: For each edge from a caller to a callee, there is a corresponding
-- edge from a callee to its caller.
check :: (Ord ee, Ord er, Ord tag) => Callgraph tag ee er -> ()
check cg =
  if callerEdges cg == calleeEdges cg
  then ()
  else panic "UCCrux.LLVM.Callgraph.check" ["Invariant violation"]

-- | A 'Callgraph' with no edges.
empty :: Callgraph tag ee er
empty =
  Callgraph
    { cgCallees = Map.empty
    , cgCallers = Map.empty
    }

-- | /O(log n)/.
outgoing :: (Ord ee, Ord er) => Callgraph tag ee er -> er -> Set (PartEdge tag ee)
outgoing cg caller = fromMaybe Set.empty (Map.lookup caller (cgCallees cg))

-- | /O(log n)/.
incoming :: (Ord ee, Ord er) => Callgraph tag ee er -> ee -> Set (PartEdge tag er)
incoming cg callee = fromMaybe Set.empty (Map.lookup callee (cgCallers cg))

-- | /O(log n)/.
callees :: (Ord ee, Ord er) => Callgraph tag ee er -> er -> Set ee
callees cg callee = Set.map peEndpoint (outgoing cg callee)

-- | /O(log n)/.
callers :: (Ord ee, Ord er) => Callgraph tag ee er -> ee -> Set er
callers cg caller = Set.map peEndpoint (incoming cg caller)

cgBimap ::
  (Ord tag, Ord ee', Ord er') =>
  (er -> er') ->
  (ee -> ee') ->
  Callgraph tag ee er ->
  Callgraph tag ee' er'
cgBimap f g cg =
  Callgraph
    { cgCallees = fmap (Set.map (Bi.second g)) (Map.mapKeys f (cgCallees cg))
    , cgCallers = fmap (Set.map (Bi.second f)) (Map.mapKeys g (cgCallers cg))
    }

-- | A callgraph edge, with two endpoints and a label/tag.
data Edge tag ee er
  = Edge
      { edgeCallee :: ee
      , edgeCaller :: er
      , edgeTag :: tag
      }
  deriving (Eq, Ord, Show)

-- | /O(log n)/.
insertEdge ::
  (Ord tag, Ord ee, Ord er) =>
  Edge tag ee er ->
  Callgraph tag ee er ->
  Callgraph tag ee er
insertEdge (Edge eCallee eCaller eTag) cg =
  cg
    { cgCallees = setInsert eCaller (PartEdge eTag eCallee) (cgCallees cg)
    , cgCallers = setInsert eCallee (PartEdge eTag eCaller) (cgCallers cg)
    }
  where
    setInsert :: Ord k => Ord v => k -> v -> Map k (Set v) -> Map k (Set v)
    setInsert k v = Map.insertWith Set.union k (Set.singleton v)

singleton :: (Ord tag, Ord ee, Ord er) => Edge tag ee er -> Callgraph tag ee er
singleton e = insertEdge e empty

-- | /O(n log n)/.
fromList :: (Ord tag, Ord ee, Ord er) => [Edge tag ee er] -> Callgraph tag ee er
fromList = foldr insertEdge empty
