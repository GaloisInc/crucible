-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Analysis.Fixpoint.Components
-- Description      : Compute weak topological ordering of CFG
-- Copyright        : (c) Galois, Inc 2015
-- License          : BSD3
-- Maintainer       : Tristan Ravitch <tristan@galois.com>
-- Stability        : provisional
--
-- Compute a weak topological ordering over a control flow graph using
-- Bourdoncle's algorithm (See Note [Bourdoncle Components]).
------------------------------------------------------------------------

{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Lang.Crucible.Analysis.Fixpoint.Components (
  weakTopologicalOrdering,
  WTOComponent(..),
  SCC(..),
  parentWTOComponent,
  -- * Special cases
  cfgWeakTopologicalOrdering,
  cfgSuccessors,
  cfgStart
  ) where

import Control.Applicative
import Control.Monad ( when, void )
import qualified Control.Monad.State.Strict as St
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Traversable as T

import Prelude

import           Data.Parameterized.Some (Some(Some))
import           Lang.Crucible.CFG.Core (CFG, BlockID)
import qualified Lang.Crucible.CFG.Core as CFG

-- | Compute a weak topological ordering over a control flow graph.
--
-- Weak topological orderings provide an efficient iteration order for
-- chaotic iterations in abstract interpretation and dataflow analysis.
weakTopologicalOrdering :: (Ord n) => (n -> [n]) -> n -> [WTOComponent n]
weakTopologicalOrdering successors start =
  wtoPartition (St.execState (runM (visit start)) s0)
  where
    s0 = WTOState { wtoSuccessors = successors
                  , wtoPartition = []
                  , wtoStack = []
                  , wtoLabelSrc = unlabeled
                  , wtoLabels = M.empty
                  }

data WTOComponent n = SCC (SCC n)
                    | Vertex n
                    deriving (Functor, F.Foldable, T.Traversable, Show)

data SCC n = SCCData  { wtoHead :: n
                      , wtoComps :: [WTOComponent n]
                      }
             deriving (Functor, F.Foldable, T.Traversable, Show)

-- | Useful for creating a first argument to 'weakTopologicalOrdering'. See
-- also 'cfgWeakTopologicalOrdering'.
cfgSuccessors ::
  CFG ext blocks init ret ->
  Some (BlockID blocks) -> [Some (BlockID blocks)]
cfgSuccessors cfg = \(Some bid) -> CFG.nextBlocks (CFG.getBlock bid bm) where
  bm = CFG.cfgBlockMap cfg

-- | Useful for creating a second argument to 'weakTopologicalOrdering'. See
-- also 'cfgWeakTopologicalOrdering'.
cfgStart :: CFG ext blocks init ret -> Some (BlockID blocks)
cfgStart cfg = Some (CFG.cfgEntryBlockID cfg)

-- | Compute a weak topological order for the CFG.
cfgWeakTopologicalOrdering ::
  CFG ext blocks init ret ->
  [WTOComponent (Some (BlockID blocks))]
cfgWeakTopologicalOrdering cfg = weakTopologicalOrdering (cfgSuccessors cfg) (cfgStart cfg)

visit :: (Ord n) => n -> M n Label
visit v = do
  push v
  cn <- labelVertex v
  (leastLabel, isLoop) <- visitSuccessors v cn
  cn' <- lookupLabel v
  -- We only create a component if this vertex is the head of its
  -- strongly-connected component (i.e., its label is the same as the
  -- minimum label in its SCC, returned from visitSuccessors).  If so,
  -- we make a new component (which may be a singleton if the vertex
  -- is not in a loop).
  when (cn' == leastLabel) $ do
    markDone v
    -- Note that we always have to pop, but we might only use the
    -- result if there was a loop
    pop >>= \case
        Just elt ->
            case isLoop of
              False ->
                -- If there is no loop, add a singleton vertex to the partition
                addComponent (Vertex v)
              True -> do
                  -- Otherwise, unwind the stack and add a full component
                unwindStack elt v
                makeComponent v
        Nothing -> error "Pop attempted on empty stack (Components:visit)"
  -- We return the least label in the strongly-connected component
  -- containing this vertex, which is used if we have to unwind back
  -- to the SCC head vertex.
  return leastLabel

-- | Unwind the stack until we reach the target node @v@
unwindStack :: (Ord n)
            => n -- ^ Current top of the stack
            -> n -- ^ Target element
            -> M n ()
unwindStack elt v =
  case elt /= v of
    False -> return ()
    True -> do
      resetLabel elt
      pop >>= \case
          Just elt' -> unwindStack elt' v
          Nothing -> error $ "Emptied stack without finding target element (Components:unwindStack)"

-- | Make a component with the given head element by visiting
-- everything in the SCC and recursively creating a new partition.
makeComponent :: (Ord n) => n -> M n ()
makeComponent v = do
  ctx <- St.get
  -- Do a recursive traversal with an empty partition
  let ctx' = St.execState (runM (go (wtoSuccessors ctx))) (ctx { wtoPartition = [] })
  -- Restore the old partition but with the updated context
  St.put (ctx' { wtoPartition = wtoPartition ctx })
  let cmp = SCC $ SCCData { wtoHead = v
                          , wtoComps = wtoPartition ctx'
                          }
  addComponent cmp
  where
    go successors = F.forM_ (successors v) $ \s -> do
      sl <- lookupLabel s
      when (sl == unlabeled) $ do
        void (visit s)

-- | Visit successors of a node and find:
--
-- 1) The minimum label number of any reachable (indirect) successor
-- and 2) If the node is in a loop
visitSuccessors :: (Ord n) => n -> Label -> M n (Label, Bool)
visitSuccessors v leastLabel0 = do
  sucs <- St.gets wtoSuccessors
  F.foldlM go (leastLabel0, False) (sucs v)
  where
    go acc@(leastLabel, _) successor = do
      scn <- lookupLabel successor
      minScn <- case scn == unlabeled of
        True -> visit successor
        False -> return scn
      case minScn <= leastLabel of
        True -> return (minScn, True)
        False -> return acc

-- | Assign a label to a vertex.
--
-- This generates the next available label and assigns it to the
-- vertex.  Note that labels effectively start at 1, since 0 is used
-- to denote unassigned.  The actual labels are never exposed to
-- users, so that isn't a big deal.
labelVertex :: (Ord n) => n -> M n Label
labelVertex v = do
  cn <- nextLabel <$> St.gets wtoLabelSrc
  St.modify' $ \s -> s { wtoLabelSrc = cn
                       , wtoLabels = M.insert v cn (wtoLabels s)
                       }
  return cn

-- | Look up the label of a vertex
lookupLabel :: (Ord n) => n -> M n Label
lookupLabel v = do
  lbls <- St.gets wtoLabels
  case M.lookup v lbls of
    Nothing -> return unlabeled
    Just l -> return l

-- | Mark a vertex as processed by setting its Label to maxBound
markDone :: (Ord n) => n -> M n ()
markDone v =
  St.modify' $ \s -> s { wtoLabels = M.insert v maxLabel (wtoLabels s) }

-- | Reset a label on a vertex to the unlabeled state
resetLabel :: (Ord n) => n -> M n ()
resetLabel v =
  St.modify' $ \s -> s { wtoLabels = M.insert v unlabeled (wtoLabels s) }

-- | Add a component to the current partition
addComponent :: WTOComponent n -> M n ()
addComponent c =
  St.modify' $ \s -> s { wtoPartition = c : wtoPartition s }

push :: n -> M n ()
push n = St.modify' $ \s -> s { wtoStack = n : wtoStack s }

pop :: M n (Maybe n)
pop = do
  stk <- St.gets wtoStack
  case stk of
    [] -> return Nothing
    n : rest -> do
      St.modify' $ \s -> s { wtoStack = rest }
      return (Just n)

data WTOState n = WTOState { wtoSuccessors :: n -> [n]
                           -- ^ The successor relation for the control flow graph
                           , wtoPartition :: [WTOComponent n]
                           -- ^ The partition we are building up
                           , wtoStack :: [n]
                           -- ^ A stack of visited nodes
                           , wtoLabelSrc :: Label
                           , wtoLabels :: M.Map n Label
                           }

newtype M n a = M { runM :: St.State (WTOState n) a }
  deriving (Functor, Monad, St.MonadState (WTOState n), Applicative)

newtype Label = Label Int
  deriving (Eq, Ord, Show)

nextLabel :: Label -> Label
nextLabel (Label n) = Label (n + 1)

unlabeled :: Label
unlabeled = Label 0

maxLabel :: Label
maxLabel = Label maxBound

-- | Construct a map from each vertex to the head of its parent WTO component.
-- In particular, the head of a component is not in the map. The vertices that
-- are not in any component are not in the map.
parentWTOComponent :: (Ord n) => [WTOComponent n] -> M.Map n n
parentWTOComponent = F.foldMap' $ \case
  SCC scc' -> parentWTOComponent' scc'
  Vertex{} -> M.empty

parentWTOComponent' :: (Ord n) => SCC n -> M.Map n n
parentWTOComponent' scc =
  F.foldMap'
    (\case
      SCC scc' -> parentWTOComponent' scc'
      Vertex v -> M.singleton v $ wtoHead scc)
    (wtoComps scc)


{- Note [Bourdoncle Components]

Bourdoncle components are a weak topological ordering of graph
components that inform a good ordering for chaotic iteration.  The
components also provide a good set of locations to insert widening
operators for abstract interpretation.  The formulation was proposed
by Francois Bourdoncle in the paper "Efficient chaotic iteration
strategies with widenings" [1].

[1] http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.89.8183&rep=rep1&type=pdf

The basic idea of Bourdoncle's algorithm is to compute the recursive
strongly-connected components of the control flow graph, sorted into
topological order.  It is based on Tarjan's SCC algorithm, except that
it recursively looks for strongly-connected components in each SCC it
finds.

-}
