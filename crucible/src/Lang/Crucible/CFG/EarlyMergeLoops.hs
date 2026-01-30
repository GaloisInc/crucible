-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.CFG.EarlyMergeLoops
-- Description      : Provides transformations on pre-SSA CFGs
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : 
-- Stability        : experimental
--
-- This modules exposes a transformation that attempts to ensure that loop branches
-- are post-dominated by nodes in the loop.
--
-- The module is organized into 3 main components:
--   1. An analysis that computes the natural loops of a CFG;
--   2. An analysis that inserts postdominators into loops that have
--      "early exits" (and hence have postdominators outside the loop);
--   3. A "fixup" pass that ensures that, in the transformed CFG, all
--      values are well defined along all (new) paths.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Lang.Crucible.CFG.EarlyMergeLoops
  ( earlyMergeLoops
  ) where

import           Control.Monad (when, (>=>))
import           Control.Applicative ((<**>))
import qualified Data.Graph.Inductive as G
import qualified Data.Foldable as Fold
import           Data.Kind
import           Data.List (nub, minimumBy)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq ((<|), fromList)
import           Data.String (fromString)

import           What4.ProgramLoc (Position(..), Posd(..))

import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Reg
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Types

--------------------------
-- | Natural Loop Analysis
--------------------------

-- | This structure identifies natural loops. Natural loops are either
-- disjoint from each other, nested, or they share the same header.
data LoopInfo s = LoopInfo
  { liFooter     :: !(BlockID s)
    -- ^ This is the block with a backedge (to the header)
  , liHeader     :: !(BlockID s)
    -- ^ This is the destination of the backedge.
  , liMembers    :: !(Set (BlockID s))
  -- ^ The loop members, which is the set of nodes that can reach the footer
  -- without going through the header.
  , liEarlyExits :: ![CFGEdge s]
  -- ^ An exiting edge is an edge from a node in the loop to an edge
  -- not in the loop. An early exit is such an edge from a node that
  -- is not the footer node.
  , liFooterIn   :: ![CFGEdge s]
  -- ^ All the edges to the footer
  , liDominators :: ![BlockID s]
  -- ^ The dominators of the loop header.
  } deriving (Eq, Show)
type CFGEdge s = (BlockID s, BlockID s)

-- | Detect all loops in a cfg.
-- The assumption is that two backedges in a cfg will have distinct destination blocks.
-- If this assumption does not hold, then return the empty list.
cfgLoops :: CFG ext s init ret -> [LoopInfo s]
cfgLoops cfg
  | distinct  = lis
  | otherwise = []
  where
    (nm, gr) = blocksGraph (cfgBlocks cfg)
    root     = toNode (blockID (cfgEntryBlock cfg))
    ls       = loops root gr
    lis      = mkLoopInfo <$> ls
    distinct = length (nub (liHeader <$> lis)) == length lis

    mkLoopInfo ((footer, header, _), members) =
      LoopInfo
      { liFooter     = toBlockID footer
      , liHeader     = toBlockID header
      , liMembers    = Set.map toBlockID members
      , liEarlyExits = [ (toBlockID i, toBlockID j) | (i,j) <- exits members, i /= footer ]
      , liFooterIn   = [ (toBlockID j, toBlockID footer) | j <- G.pre gr footer ]
      , liDominators = maybe [] (fmap toBlockID) $ lookup header (G.dom gr root)
      }

    toBlockID n = nm Map.! n

    exits bs = [ (i, j) | i <- Set.toList bs, j <- G.suc gr i, j `Set.notMember` bs ]

-- | Is li1 nested in li2
isNested :: LoopInfo s -> LoopInfo s -> Ordering
isNested li1 li2
  | liHeader li2 `elem` liDominators li1 = LT
  | otherwise = EQ

-- | Return all loops in @g@, which are edges from a node in g to a
-- dominator of that node.
loops :: G.Node -- ^ entry node
      -> G.UGr -- ^ the graph
      -> [(G.LEdge (), Set G.Node)]
loops root g = [ (e, loopMembers g dominators header) | e@(_,header,_) <- edges ]
  where
    edges = loop dominators g =<< G.nodes g
    dominators = Map.fromList $ G.dom g root

-- | Return any edges from @n@ to a dominator of @n@, @n'@. The edge
-- @n@ to @n'@ is a loop.
loop :: Map.Map G.Node [G.Node] -- ^ Dominators
     -> G.UGr -- ^ The graph itself
     -> G.Node -- ^ The root node to inspect for backedges
     -> [G.LEdge ()] -- ^ A loop is an edge to a dominator
loop domMap g n =
  -- A back edge (loop) is an edge from n -> n' where n' dominates n
  [ (n, n', ()) | n' <- G.suc g n, n /= n', n' `elem` Map.findWithDefault [] n domMap ]

-- | The members of a loop are just those nodes dominated by the
-- header that can reach the header again
loopMembers :: G.UGr -> Map.Map G.Node [G.Node] -> G.Node -> Set G.Node
loopMembers g doms header =
  Set.fromList members
  where
    fromHeader = G.reachable header g
    members    = [ x | x <- fromHeader, header `elem` G.reachable x g, headerDominates x ]
    headerDominates n
      | Just ds <- Map.lookup n doms
      = header `elem` ds
      | otherwise
      = False

-- | View a blockID as a node
toNode :: BlockID s -> G.Node
toNode i =
  case i of
    LabelID l  -> fromIntegral $ indexValue $ labelId l
    LambdaID l -> fromIntegral $ indexValue $ lambdaId l

-- | Compute the successor nodes of this block
blockSuccessors :: Block ext s ret -> [G.Node]
blockSuccessors b =
  maybe [] (map toNode) $ termNextLabels (pos_val (blockTerm b))

-- | Returns the edges from this block to its successors
blockEdges :: Block ext s ret -> [G.LEdge ()]
blockEdges b =
  mkEdge (toNode (blockID b)) <$> blockSuccessors b
  where
    mkEdge x y = (x, y, ())

blocksGraph :: [Block ext s ret] -> (Map.Map G.Node (BlockID s), G.UGr)
blocksGraph blocks = (m, G.mkGraph ((,()) <$> nodes) edges)
  where
    nodes = toNode . blockID <$> blocks
    m     = Map.fromList (zip nodes (blockID <$> blocks))
    edges = blockEdges       =<< blocks

-----------------------------------------
-- | Undefined Value Fixup Transformation
-----------------------------------------

-- | A PartialValue of type @t@ closes over a register of type @Maybe t@
type ValueToPartialMap s  = MapF.MapF (Value s) (PartialValue s)
newtype PartialValue s tp = PartialValue { getPartial :: Reg s (MaybeType tp) }

type AtomSubst s = MapF.MapF (Atom s :: CrucibleType -> Type)
                              (Atom s :: CrucibleType -> Type)
type AtomPair s  = MapF.Pair (Atom s :: CrucibleType -> Type)
                              (Atom s :: CrucibleType -> Type)

-- | Undefined Value Fixup pass
-- The merge-block insertion process introduces infeasible paths along which
-- some registers may be undefined: this will later be interpreted as a block
-- input in the SSA transformation. To avoid this, we introduce a pass to
-- replace registers/atoms that may be undefined along some path with a partial
-- register (i.e. of type Maybe t).
--
-- Assuming that the input CFG has no paths along which a value is
-- read before being written, the paths along which the reference is
-- read but never written are a subset of the infeasible paths.
lowerUndefPass :: (Monad m, TraverseExt ext)
               => NonceGenerator m s
               -> Label s
               -> CFG ext s init ret
               -> m (CFG ext s init ret)
lowerUndefPass ng rootLabel cfg =
  do (pvals, refInits) <- mkPartialRegMap ng cfg

     let root' = mkBlock (blockID root) (blockExtraInputs root) (blockStmts root <> refInits) (blockTerm root)
     let lower blk
           | blockID blk == LabelID rootLabel
           = return root'
           | otherwise
           = lowerBlock ng pvals blk

     blks' <- mapM lower (cfgBlocks cfg)
     let cfg' = cfg { cfgBlocks = blks' }
     return cfg'
  where
    root = fromMaybe err $ findBlock cfg rootLabel
    err  = panic "EarlyMergeLoops.lowerUndefPass"
                 [ "Root block not found in cfg" ]

-- | Fixup the reads and writes in a block. This means, for each value in the domain
-- of the @ValueToPartialMap@ argument,
-- 1. If the value is read, then find the associated partial value register and read that instead
-- 2. Dually, if the value is written, then write that value to the associated partial value register.
lowerBlock :: forall s m ext ret
            . (Monad m, TraverseExt ext)
           => NonceGenerator m s
           -> ValueToPartialMap s
           -> Block ext s ret
           -> m (Block ext s ret)
lowerBlock ng pvals blk =
  do -- If this is a lambda block, treat the associated atom as a write to that atom.
     initInputs               <- lowerBlockIDValues ng pvals blk
     -- Dually, any values passed to a successor should be treated as reads
     (preOutput, loweredTerm) <- lowerTermStmtValues ng pvals blk
     -- Fix the reads and writes in the body of this block
     lowered <- concatMapSeqM (lowerReads >=> concatMapSeqM lowerWrites) (blockStmts blk)
     return $ mkBlock (blockID blk) (blockExtraInputs blk) (initInputs <> lowered <> preOutput) loweredTerm
  where
    lowerWrites = lowerValueWrites ng pvals
    lowerReads  = lowerValueReads ng pvals

    concatMapSeqM :: Monad m => (a -> m (Seq b)) -> Seq a -> m (Seq b)
    concatMapSeqM f seq0 =
      Fold.foldrM (\s ss -> f s <**> pure (<> ss)) mempty seq0

-- | The atom in a lambda ID is essentially an 'atom definition', so
-- we need to check if this lambda's atom needs to be 'lowered'.
lowerBlockIDValues :: forall s m ext ret
                     . (Monad m, TraverseExt ext)
                    => NonceGenerator m s
                    -> ValueToPartialMap s
                    -> Block ext s ret
                    -> m (Seq (Posd (Stmt ext s)))
lowerBlockIDValues ng pvals blk = 
  case blockID blk of
    LambdaID (lambdaAtom -> a)
      | Just (getPartial -> pr) <- MapF.lookup (AtomValue a) pvals ->
        do pa <- freshAtom ng (atomPosition a) (MaybeRepr (typeOfAtom a))
           let setPa = Posd (atomPosition a) (DefineAtom pa (EvalApp (JustValue (typeOfAtom a) a)))
               setPr = Posd (atomPosition a) (SetReg pr pa)
           return $ Seq.fromList [ setPa, setPr ]
      | otherwise ->
        -- Not in our list of values to lower
        return mempty
    LabelID {} ->
      -- No atoms defined
      return mempty

-- | Jumping to a block with a value a la Output is akin to
-- 'reading' the atom, so if we already lifted the original value
-- of type T to a (Maybe T), we need to convert it back to a T
-- here.
lowerTermStmtValues :: forall s m ext ret
                     . (Monad m, TraverseExt ext)
                    => NonceGenerator m s
                    -> ValueToPartialMap s
                    -> Block ext s ret
                    -> m (Seq (Posd (Stmt ext s)), Posd (TermStmt s ret))
lowerTermStmtValues ng pvals blk =
  case pos_val (blockTerm blk) of
    Output ll a          -> withLowered a $ Output ll
    MaybeBranch t a ll l -> withLowered a $ \a' -> MaybeBranch t a' ll l
    Return a             -> withLowered a $ Return
    TailCall f c a       -> withLowered f $ \f' -> TailCall f' c a
    ErrorStmt msg        -> withLowered msg $ ErrorStmt
    VariantElim c a ls   -> withLowered a $ \a' -> VariantElim c a' ls
    -- No atoms are output/read
    Jump {}              -> return (mempty, blockTerm blk)
    Br {}                -> return (mempty, blockTerm blk)

  where
    termPos = pos (blockTerm blk)
    withLowered :: forall (tp :: CrucibleType) ty.
                   Atom s tp
                -> (Atom s tp -> TermStmt s ty) -> m (Seq (Posd (Stmt ext s)), Posd (TermStmt s ty))
    withLowered a k =
      do (setAtom, a') <- lowerAtomRead termPos a
         return (setAtom, Posd termPos (k a'))

    lowerAtomRead :: forall (tp :: CrucibleType). Position -> Atom s tp -> m (Seq (Posd (Stmt ext s)), Atom s tp)
    lowerAtomRead p a =
        do (sub, setValue) <- lowerAtom ng pvals (Some a)
           let a' = apSubst (atomSubst sub) a
           return $ (Posd p <$> Seq.fromList setValue, a')
      

-- | Replace each write of a possibly-undef atom/register to a write of the
-- associated partial register by injecting it into a value of Maybe type.
lowerValueWrites :: forall m ext s. (Monad m, TraverseExt ext)
                 => NonceGenerator m s
                 -> ValueToPartialMap s
                 -> Posd (Stmt ext s)
                 -> m (Seq (Posd (Stmt ext s)))
lowerValueWrites ng pvals st =
  case pos_val st of
   -- Replace r := a (morally) with pr := Just a,
   -- where pr is the partial register associated with r
   SetReg r a
     | Just (getPartial -> pr) <- MapF.lookup (RegValue r) pvals ->
         setMaybeAtom pr a (typeOfAtom a)
     | otherwise -> orig

   -- Given a := v, append pr := Just(a) where pr is the
   -- partial register associated with a
   DefineAtom a _
     | Just (getPartial -> pr) <- MapF.lookup (AtomValue a) pvals ->
       do setA' <- setMaybeAtom pr a (typeOfAtom a)
          return (st Seq.<| setA')
     | otherwise -> orig

   -- No registers set or atoms defined:
   WriteGlobal {} -> orig
   WriteRef {}    -> orig
   DropRef {}     -> orig
   Print {}       -> orig
   Assert {}      -> orig
   Assume {}      -> orig
   Breakpoint {}  -> orig

  where
    orig = pure (Seq.fromList [st])

    -- Construct (pa := Just a; pr := pa) where pa is fresh
    setMaybeAtom :: forall (tp :: CrucibleType).
                    Reg s (MaybeType tp) -> Atom s tp -> TypeRepr tp -> m (Seq (Posd (Stmt ext s)))
    setMaybeAtom pr a ty =
       do pa <- freshAtom ng (atomPosition a) (MaybeRepr ty)
          let setPa = Posd (pos st) (DefineAtom pa (EvalApp (JustValue ty a)))
              setPr = Posd (pos st) (SetReg pr pa)
          return $ Seq.fromList [ setPa, setPr ]

-- | Replace each read of a lowered atom/register to a read of the
-- associated register + projection from Maybe
lowerValueReads :: forall m ext s
                . (Monad m, TraverseExt ext)
                => NonceGenerator m s
                -> ValueToPartialMap s
                -> Posd (Stmt ext s)
                -> m (Seq (Posd (Stmt ext s)))
lowerValueReads ng pvals st =
  case pos_val st of
    -- RegReads have only one form
    DefineAtom a (ReadReg r)
     | Just (getPartial -> pr) <- MapF.lookup (RegValue r) pvals ->
       lowerRegRead ng (pos st) a pr
    -- For everything else, we need to check if any of the
    -- referenced atoms need to be lowered
    DefineAtom {}  -> lowerAtomReads ng pvals atomsToLower st
    SetReg {}      -> lowerAtomReads ng pvals atomsToLower st
    WriteGlobal {} -> lowerAtomReads ng pvals atomsToLower st
    WriteRef {}    -> lowerAtomReads ng pvals atomsToLower st
    DropRef {}     -> lowerAtomReads ng pvals atomsToLower st
    Print {}       -> lowerAtomReads ng pvals atomsToLower st
    Assert {}      -> lowerAtomReads ng pvals atomsToLower st
    Assume {}      -> lowerAtomReads ng pvals atomsToLower st
    Breakpoint {}  -> lowerAtomReads ng pvals atomsToLower st
  where
    atomsToLower :: [Some (Atom s)]
    atomsToLower = Set.toList (foldStmtInputs addIfLowered (pos_val st) mempty)

    addIfLowered :: forall tp. Value s tp -> Set.Set (Some (Atom s)) -> Set.Set (Some (Atom s))
    addIfLowered v@(AtomValue a) s
      | MapF.member v pvals = Set.insert (Some a) s
    addIfLowered _ s = s

-- | Replace each read of a lowered atom to a read of the
-- associated register + projection from Maybe
lowerAtomReads :: forall m ext s.
                  (Monad m, TraverseExt ext)
               => NonceGenerator m s
               -> ValueToPartialMap s
               -> [Some (Atom s)]
               -> Posd (Stmt ext s)
               -> m (Seq (Posd (Stmt ext s)))
lowerAtomReads ng pvals atomsToLower st =
  do (substs, readRegs) <- unzip <$> mapM (lowerAtom ng pvals) atomsToLower
     let substMap        = atomSubst (concat substs)
     st'                <- mapStmtAtom (return . apSubst substMap) (pos_val st)
     let stmts           = Seq.fromList (Posd (pos st) <$> (concat readRegs ++ [st']))
     return stmts

apSubst :: AtomSubst s -> (forall (tp :: CrucibleType). Atom s tp -> Atom s tp)
apSubst sub n = fromMaybe n $ MapF.lookup n sub

atomSubst :: [MapF.Pair (Atom s :: CrucibleType -> Type) (Atom s)] -> AtomSubst s
atomSubst substs = MapF.fromList substs

-- | Given an atom @a@ of type @t@ whose definition we've already
-- replaced with a register @r@ of type @Maybe t@, produce the
-- statements to
-- 1. read @r@ into a fresh @a'@
-- 2. set fresh @a''@ to @fromJust a'@
-- returns a mapping from @a@ to @a'@ and the above
lowerAtom :: forall m s ext.
             Monad m
          => NonceGenerator m s
          -> ValueToPartialMap s
          -> Some (Atom s)
          -> m ([AtomPair s], [Stmt ext s])
lowerAtom ng pvals (Some a)
  | Just (getPartial -> r) <- MapF.lookup (AtomValue a) pvals =
      do a'  <- substAtom (const (freshNonce ng)) a
         str <- freshAtom ng (atomPosition a) knownRepr
         a'' <- freshAtom ng (atomPosition a) (MaybeRepr (typeOfAtom a))
         let defs = [ DefineAtom a'' (ReadReg r)
                    , DefineAtom str (EvalApp (StringLit ("Lower Atom Pass: " <> fromString (show (atomId a)))))
                    , DefineAtom a'  (EvalApp (FromJustValue (typeOfAtom a) a'' str))
                    ]
         return ([MapF.Pair a a'], defs)
  | otherwise =
      return ([], [])

-- | @lowerRegRead ng pos a pr@ constructs @a' := pr; a := fromJust a'@.
lowerRegRead :: Monad m
             => NonceGenerator m s
             -> Position
             -- ^ The position we should use for the new statements
             -> Atom s tp
             -- ^ The atom we're defininig
             -> Reg s (MaybeType tp)
             -- ^ The partial register to read from
             -> m (Seq (Posd (Stmt ext s)))
lowerRegRead ng p a pr =
  do a' <- freshAtom ng (atomPosition a) (MaybeRepr (typeOfAtom a))
     str <- freshAtom ng (atomPosition a) knownRepr
     -- insert a new atom to read the reg, then replace with FromJustVal
     let stmts = [ DefineAtom str (EvalApp (StringLit "Lower Register Pass"))
                 , DefineAtom a'  (ReadReg pr)
                 , DefineAtom a   (EvalApp (FromJustValue (typeOfAtom a) a' str))
                 ]
     return $ Seq.fromList (Posd p <$> stmts)
  
-- | Traverse all dfs paths, avoiding backedges, to find values that may be read but not written.
-- Returns:
--  1. a mapping from values of type @t@ to corresponding registers of type @Maybe t@ 
--  2. statements to initialize the registers mentioned in said mapping.
mkPartialRegMap :: (Monad m, TraverseExt ext)
                => NonceGenerator m s
                -> CFG ext s init ret
                -> m ((ValueToPartialMap s, Seq (Posd (Stmt ext s))))
mkPartialRegMap ng cfg =
  traverseCFG gatherPvals (MapF.empty, mempty) (blockExtraInputs entry) entry cfg
  where
    entry = cfgEntryBlock cfg

    gatherPvals pvals env blk =
      do refs'   <- Fold.foldlM addPval pvals (blockUndefVals env blk)
         return (refs', env <> blockAssignedValues blk)
  
    addPval (pvals, inits) val@(Some v)  
      | Just _ <- MapF.lookup v pvals
      = return (pvals, inits)
      | otherwise
      = do (MapF.Pair vundef pval, is) <- makePartialReg ng val
           return (MapF.insert vundef pval pvals, inits <> is)

-- | Given a value @v@ of type @t@, create a new register @r@ of type
--   @Maybe t@.  This function returns 1. the mapping from @v@ to such
--   an @r@, as well as the @stmts@ that will initialize @r@ to
--   @Nothing : Maybe t@.
makePartialReg :: Monad m
               => NonceGenerator m s
               -> Some (Value s)
               -> m (MapF.Pair (Value s) (PartialValue s), Seq (Posd (Stmt ext s)))
makePartialReg ng (Some val) =
  do a <- freshAtom ng p (MaybeRepr ty)
     r <- freshReg ng p (MaybeRepr ty)
     let v = EvalApp (NothingValue ty)
         s = DefineAtom a v
         sr = SetReg r a
         inits = Posd p <$> [s, sr]
     return (MapF.Pair val (PartialValue r), Seq.fromList inits)
  where
    (ty, p) = case val of
                RegValue reg   -> (typeOfReg reg, regPosition reg)
                AtomValue atom -> (typeOfAtom atom, atomPosition atom)

-------------------
-- | Merging Paths
-------------------

-- | This is a record used to construct/manage the variant type that the router block
-- will use to switch on. The important piece is the map that relates blockIDs to an index
-- into the variant type's ctx -- with this map we can associate a _value_ of the variant type
-- with a given blockID
data BlockSwitchInfo s ctx = BlockSwitchInfo
                             { switchRepr :: CtxRepr ctx
                             , switchSize :: Ctx.Size ctx
                             , switchMap  :: Map.Map (BlockID s) (Ctx.Index ctx UnitType)
                             }
                           deriving Show

-- | Used as a substitution between labels.
-- Closes over the type of LambdaLabels
data BlockIDPair s where
   Labels       :: Label s -> Label s -> BlockIDPair s
   LambdaLabels :: LambdaLabel s tp -> LambdaLabel s tp -> BlockIDPair s

instance Show (BlockIDPair s) where
  show (Labels l1 l2)       = show l1 ++ " => " ++ show l2
  show (LambdaLabels l1 l2) = show l1 ++ " =>{lambda} " ++ show l2

-- | This is the main pass that attempts to optimize early exits in
-- the loops in a CFG.  In particular, this transformation ensures that the
-- postdominator of the loop header is a member of the loop.
--
-- Given a natural loop, its members are a set of blocks @bs@. Let the exit edges be 
-- the edges from some block @b@ in @bs@ to either the loop header or a block not in @bs@.
--
-- Let (i, j) be such an exit edge.This transofrmation inserts a new
-- block @r@ such that in the transformed cfg there is an edge (i, r)
-- and an edge (r, j). Moreover, the transformation ensures that [i,
-- r, j'] is not feasible for j' != j. This works by setting a
-- "destination" register @d := j@ in each block i for each exit edge
-- (i, j), and switching on the value of @d@ in the block @r@.
earlyMergeLoops :: ( TraverseExt ext, Monad m, Show (CFG ext s init ret) )
                => NonceGenerator m s
                -> CFG ext s init ret
                -> m (CFG ext s init ret)
earlyMergeLoops ng cfg0 =
  do cfg' <- earlyMergeLoops' ng mempty (cfgLoops cfg0) cfg0
     lowerUndefPass ng (cfgEntryLabel cfg') cfg'
      
-- Merge a loop from loops in cfg.  The loops parameter is passed
-- to earlyMergeLoops (rather than calculated directly from cfg)
-- so that we can use see how the set of loops changes from
-- iteration to iteration: in particular, we want to make sure
-- that the number of loops does not increases
earlyMergeLoops' :: ( TraverseExt ext, Monad m, Show (CFG ext s init ret) )
                 => NonceGenerator m s
                 -> Set (BlockID s)
                 -> [LoopInfo s]
                 -> CFG ext s init ret
                 -> m (CFG ext s init ret)
earlyMergeLoops' ng seen ls cfg
  | Just l <- nextLoop
  = do cfg' <- earlyMergeLoop ng cfg l

       -- Check if we should proceed: in particular, if the new CFG
       -- renamed or produced new loops, then we need to bail as we
       -- might not terminate in that case.
       let ls'      = cfgLoops cfg'
       let seen'    = (Set.insert (liHeader l) seen)
       let nextStep = candidates seen' ls'
       -- The termination transition invariant is that 
       when (length thisStep <= length nextStep) $
         panic "EarlyMergeLoops.earlyMergeLoops'"
               ["Non-decreasing number of loops in earlyMegeLoops'"]
       
       earlyMergeLoops' ng seen' ls' cfg'
  | otherwise
  = return cfg
  where
    thisStep =
      candidates seen ls

    nextLoop 
      | null thisStep  = Nothing
      | otherwise = Just (minimumBy isNested thisStep)

    candidates seenBlocks lis =
      filter (unseen seenBlocks) lis


    unseen s li = liHeader li `Set.notMember` s

-- | Apply the transformation described in @earlyMergeLoops@ to a single loop.
earlyMergeLoop :: ( TraverseExt ext, Monad m )
               => NonceGenerator m s
               -> CFG ext s init ret
               -> LoopInfo s
               -> m (CFG ext s init ret)
earlyMergeLoop ng cfg li
  | not (null exits) =
      do bmap' <- funnelPaths ng bmap exits
         return cfg { cfgBlocks = Map.elems bmap' }
  | otherwise =
      return cfg
  where
    exits         = filterErrors (liEarlyExits li ++ liFooterIn li)
    filterErrors  = filter (not . errorPath bmap)
    bmap          = blockMap cfg

-- | Given a set of edges (i, j) in E,
-- Create a single block that merges all paths before
-- continuing on to the respective j's
--
-- Create a unique block F and multiple blocks  i' j' such
-- that i -> i' -> F -> j' -> j.
-- This function defines a register 'r : () + () + ... + ()'
-- Each 'j' corresponds to one of these tags, so each
-- i' sets r to indicate which 'j' to jump to, and F
-- switches on r. Each j' is a lambda block that jumps to the
-- original j.
--
-- E.g. given i0 -> j0, i1 -> j0, i2 -> j1,
-- then i0' =  r := inj(0, ()); jump F
--      i1' =  r := inj(0, ()); jump F
--      i2' =  r := inj(1, ()); jump F
--      F   =  switch r { 0: j0', 1: j1' }
--      j0' = jump j0
--      j1' = jump j1
funnelPaths :: (TraverseExt ext, Monad m)
             => NonceGenerator m s
             -> Map.Map (BlockID s) (Block ext s ret)
             -> [(BlockID s, BlockID s)]
             -> m (Map.Map (BlockID s) (Block ext s ret))
funnelPaths ng bmap paths =
  case mkBlockSwitchInfo outBlocks of
    Some p ->
      do (rename, newBlocks) <- routePaths ng p outBlocks
         let renamedMap       = Fold.foldl' (updateBlock rename) bmap (fst <$> paths)
             newMap           = Fold.foldl' addNewBlock renamedMap newBlocks

         return newMap
  where
    outBlocks = nub (snd <$> paths)

    sub renaming stmt = Fold.foldl' runRename stmt renaming
    addNewBlock m b        = Map.insert (blockID b) b m
    updateBlock ren m bid  = Map.update (doUpdate ren) bid m
    doUpdate renaming blk  = Just $ mkBlock (blockID blk) (blockExtraInputs blk)
                                      (blockStmts blk) (sub renaming <$> blockTerm blk)

    -- Apply the label substitution in 'renaming'
    -- to the term stmt in tgt (no-op on stmts without labels)
    runRename tgt renaming =
      case (tgt, renaming) of
        (Jump t, Labels from to)
          | t == from -> Jump to
          | otherwise -> tgt
        (Jump _, LambdaLabels {}) -> tgt

        (Br p t1 t2, Labels from to)
          | t1 == from -> Br p to t2
          | t2 == from -> Br p t1 to
          | otherwise  -> tgt
        (Br {}, LambdaLabels {}) -> tgt

        (Output ll a, LambdaLabels from to)
          | Just Refl <- testEquality ll from -> Output to a
          | otherwise -> tgt
        (Output {}, Labels {}) -> tgt

        (VariantElim ctx a assgn, r@(LambdaLabels {})) ->
          VariantElim ctx a (fmapFC (renameLabel r) assgn)
        (VariantElim {}, Labels {}) -> tgt

        (MaybeBranch t a l1 l2, Labels from to)
          | l2 == from -> MaybeBranch t a l1 to
          | otherwise  -> tgt
        (MaybeBranch t a l1 l2, LambdaLabels from to)
          | Just Refl <- testEquality l1 from ->
            MaybeBranch t a to l2
          | otherwise  -> tgt

        {- No labels to rename -}
        (Return _, _)     -> tgt
        (TailCall {}, _)  -> tgt
        (ErrorStmt {}, _) -> tgt

    renameLabel (LambdaLabels from to) ll
      | Just Refl <- testEquality from ll = to
    renameLabel _ l = l


-- | Given a list of blocks, build a record of a variant type such that each injection
-- is associated with a single block.
mkBlockSwitchInfo :: [BlockID s] -> Some (BlockSwitchInfo s)
mkBlockSwitchInfo bs =
  case bs of
    []      ->
      Some (BlockSwitchInfo Ctx.empty Ctx.zeroSize mempty)
    (b:bs') ->
      case mkBlockSwitchInfo bs' of
        Some (BlockSwitchInfo ctxRepr sz indices) ->
          Some $ BlockSwitchInfo { switchRepr = ctxRepr Ctx.:> UnitRepr
                                 , switchSize = Ctx.incSize sz
                                 , switchMap  = Map.insert b (Ctx.nextIndex sz) (Map.map Ctx.skipIndex indices)
                                 }

-- | This function does most of the work for @funnelPaths@.
-- In particular, given a list of blocks @b0...bn@,
-- it constructs a single @r@, a list @b_in0...b_inn@, and a list
-- @b_out0...@b_outn@ such that @b_in_i@ jump to @r@, and @r@
-- jumps to the corresponding @b_out_i@.
--
-- The return value is a pair of
-- (1) A list of BlockIDPairs, which should be understood as a substitution
-- on labels. This is necessary since we are introducing *new* blocks to replace
-- *old* jump targets. This substitution is used to update the old jump targets
-- (2) A list of newly created blocks
routePaths :: forall m ext ctx s ret
            . (TraverseExt ext, Monad m)
           => NonceGenerator m s
           -> BlockSwitchInfo s ctx
           -- ^ the variant info should map each element of @outs@ to an index into `ctx`
           -> [BlockID s]
           -- ^ the blocks that we want to join & then fan out from
           -> m ([BlockIDPair s], [Block ext s ret])
routePaths ng (BlockSwitchInfo ctx sz idxMap) outs =
  do -- 'bsi' has the information we need to associate each input block
     -- with an a particular *index* into a list of outputs. This means
     -- for each destination that we're routing to,
     -- we can set a register `r` to some value `v`
     -- and case split on `r` in a 'router block' to recover the intended destination

     -- this associates each such index with the new 'destination'
     mapping <- mkMapping

     -- This is the block that switches on the destination block.
     -- l is its label, r is the register that we'll case split on,
     -- and 'router' is the actual block definition containing the switch
     (l, r, router) <- routerBlock ng ctx mapping
    
     -- construct the blocks feeding into the router. for each output block,
     -- set 'r' appropriately, by fetching the value from the index map in 'vi'
     (rename, injBlocks) <- unzip <$> traverse (mkInjBlock r l) outs

     -- Finally make the destination blocks that continue to the original
     -- targets
     let outputBlocks = Map.foldrWithKey (mkLambdaBlock rename mapping) [] idxMap

     return (rename, router : outputBlocks ++ injBlocks)
  where
    bidToTerm :: BlockID s -> [BlockIDPair s] -> TermStmt s ret
    bidToTerm origOut rename =
      case (origOut, rename) of
        (LabelID ll, _ ) -> Jump ll
        (LambdaID ll, LambdaLabels l1 l2:_)
          | Just Refl <- testEquality (lambdaId ll) (lambdaId l1) -> Output l1 (lambdaAtom l2)
        (_, _:rest) -> bidToTerm origOut rest
        _ ->
          panic "routePaths" ["Output blocks mismatched"]
  
    mkMapping = Ctx.generateM sz $ \idx ->
      do n <- freshNonce ng
         a <- freshAtom ng internal (ctx Ctx.! idx)
         return (LambdaLabel n a)

    mkInjBlock reg rlabel j =
      do let idx = idxMap Map.! j
         (rename, injBlock) <- routerEntryBlock ng ctx reg j idx rlabel
         return (rename, injBlock)

    mkLambdaBlock rename mapping blkId blkIdx blks =
      mkBlock (LambdaID (mapping Ctx.! blkIdx))
              mempty
              mempty
              (Posd internal (bidToTerm blkId rename)) : blks

-- | Create a block that switches on a register. This does the work of
-- allocating the new label and discriminant register
routerBlock :: ( TraverseExt ext, Monad m )
            => NonceGenerator m s
            -> CtxRepr routing
            -> Ctx.Assignment (LambdaLabel s) routing
            -> m (Label s, Reg s (VariantType routing), Block ext s ret)
routerBlock ng ctx mapping =
  do l        <- Label <$> freshNonce ng
     destReg  <- freshReg ng internal (VariantRepr ctx)
     readDest <- freshAtom ng internal (VariantRepr ctx)
     let elim    = VariantElim ctx readDest mapping
         readVar = Posd internal (DefineAtom readDest (ReadReg destReg))
         funnel  = mkBlock (LabelID l) mempty (pure readVar) (Posd internal elim)
     return (l, destReg, funnel)

-- | This creates a block that to be substituted for @origID@.
-- This block will set the given register to the injection
-- given by @destIdx@, and then jump to a router block (described in @routePaths@)
-- that will `switch` on this register. 
routerEntryBlock :: ( TraverseExt ext, Monad m )
                 => NonceGenerator m s
                 -> CtxRepr routing
                 -> Reg s (VariantType routing)
                 -- ^ The register we will switch on
                 -> BlockID s
                 -- ^ The ID of the block we're substituting for
                 -> Ctx.Index routing UnitType
                 -- ^ Which injection in the variant type to use
                 -> Label s
                 -- ^ The label of the router block
                 -> m (BlockIDPair s, Block ext s ret)
routerEntryBlock ng ctx r origID destIdx routerLabel =
  do aUnit <- freshAtom ng internal UnitRepr
     aInj  <- freshAtom ng internal (VariantRepr ctx)
   
     (l, rename) <-
       case origID of
         LabelID l1 ->
           do l2 <- substLabel (\_ -> freshNonce ng) l1
              return (LabelID l2, Labels l1 l2)
         LambdaID l1@(LambdaLabel _ a) ->
           do l' <- freshNonce ng
              a' <- freshNonce ng
              -- knot-tying in the LambdaLabel type results in an infinite loop
              let l2 = LambdaLabel l' a { atomId = a' }
              return (LambdaID l2, LambdaLabels l1 l2)

     let defUnit = Posd internal (DefineAtom aUnit (EvalApp EmptyApp))
         defVar  = Posd internal (DefineAtom aInj (EvalApp (InjectVariant ctx destIdx aUnit)))
         setReg  = Posd internal (SetReg r aInj)
         stmts   = Seq.fromList [defUnit, defVar, setReg]
         blk     = mkBlock l mempty stmts (Posd internal (Jump routerLabel))

     return (rename, blk)

errorPath :: Map.Map (BlockID s) (Block ext s ret) -> CFGEdge s -> Bool
errorPath bmap (_, bid) =
  case Map.lookup bid bmap of
    Just (blockTerm -> Posd _ (ErrorStmt _)) -> True
    _ -> False

-- | Generally useful helpers

freshAtom :: Monad m => NonceGenerator m s -> Position -> TypeRepr tp -> m (Atom s tp)
freshAtom ng p tp =
  do i <- freshNonce ng
     return $ Atom { atomPosition = p
                   , atomId = i
                   , atomSource = Assigned
                   , typeOfAtom = tp
                   }

freshReg :: Monad m => NonceGenerator m s -> Position -> TypeRepr tp -> m (Reg s tp)
freshReg ng p tp =
  do i <- freshNonce ng
     return $ Reg { regPosition = p
                  , regId = i
                  , typeOfReg = tp
                  }
      
findBlock :: CFG ext s init ret -> Label s -> Maybe (Block ext s ret)
findBlock g l =
  Fold.find (\b -> blockID b == LabelID l) (cfgBlocks g)
  
blockUndefVals :: ValueSet s -> Block ext s ret -> ValueSet s
blockUndefVals def blk = blockKnownInputs blk Set.\\ def

blockMap :: CFG ext s init ret -> Map.Map (BlockID s) (Block ext s ret)
blockMap cfg = Map.fromList [ (blockID b, b) | b <- cfgBlocks cfg ]

internal :: Position
internal = InternalPos
