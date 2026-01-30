-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.BlockInfo
-- Description      : Pre-translation analysis results
-- Copyright        : (c) Galois, Inc 2018-2021
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-----------------------------------------------------------------------
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

module Lang.Crucible.LLVM.Translation.BlockInfo
  ( LLVMBlockInfoMap
  , LLVMBlockInfo(..)
  , buildBlockInfoMap
  , useTypedVal
  ) where

import Data.Foldable (toList)
import qualified Data.Foldable as Foldable
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Text.LLVM.AST as L

import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.Panic ( panic )

type LLVMBlockInfoMap s = Map L.BlockLabel (LLVMBlockInfo s)

-- | Information about an LLVM basic block computed before we begin the
--   translation proper.
data LLVMBlockInfo s
  = LLVMBlockInfo
    {
      -- | The crucible block label corresponding to this LLVM block
      block_label :: Label s

      -- | The computed \"use\" set for this block.  This is the set
      -- of identifiers that must be assigned prior to jumping to this
      -- block. They are either used directly in this block or used
      -- by a successor of this block.
      --
      -- Note! \"metadata\" nodes do not contribute to the use set.
      -- This is because LLVM itself relaxes the usual use/def rules
      -- for metadata to prevent debugging information from inhibiting
      -- optimizations.  CF https://bugs.llvm.org/show_bug.cgi?id=51155
      --
      -- Note! values referenced in phi nodes are also not included in
      -- this set, they are instead handled when examining the
      -- terminal statements of predecessor blocks.
    , block_use_set :: !(Set L.Ident)

      -- | The predecessor blocks to this block (i.e., all those blocks
      -- that can jump to this one).
    , block_pred_set :: !(Set L.BlockLabel)

      -- | The successor blocks to this block (i.e., all those blocks
      -- that this block can jump to).
    , block_succ_set :: !(Set L.BlockLabel)

      -- | The statements defining this block
    , block_body :: ![L.Stmt]

      -- | Map from labels to assignments that must be made before
      -- jumping.  If this is the block info for label l',
      -- and the map has [(i1,v1),(i2,v2)] in the phi_map for block l,
      -- then basic block l is required to assign i1 = v1 and i2 = v2
      -- before jumping to block l'.
    , block_phi_map :: !(Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value)))
    }

-- | Construct the block info map for the given function definition.  This collects
--   information about phi-nodes, assigns crucible labels to each basic block, and
--   computes use sets for each block.
buildBlockInfoMap :: Monad m => L.Define -> Generator l s st ret m (LLVMBlockInfoMap s)
buildBlockInfoMap d =
  do bim0 <- Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)
     let bim1 = updatePredSets bim0
     return (computeUseSets bim1)

-- | Build the initial pass of block information. This does not yet compute predecessor
--   sets or use sets.
buildBlockInfo :: Monad m => L.BasicBlock -> Generator l s st ret m (L.BlockLabel, LLVMBlockInfo s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let succ_set = buildSuccSet (L.bbStmts bb)
  let blk_lbl = case L.bbLabel bb of
                  Just l -> l
                  Nothing -> panic "crucible-llvm:Translation.buildBlockInfo"
                             [ "unable to obtain label from BasicBlock" ]
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_use_set = mempty
                                , block_pred_set = mempty
                                , block_succ_set = succ_set
                                , block_body = L.bbStmts bb
                                , block_label = lab
                                })

-- | Given the statements in a basic block, find all the successor blocks,
-- i.e. the blocks this one may jump to.
buildSuccSet :: [L.Stmt] -> Set L.BlockLabel
buildSuccSet [] = mempty
buildSuccSet (s:ss) =
  case L.stmtInstr s of
    L.Ret{} -> mempty
    L.RetVoid -> mempty
    L.Unreachable -> mempty
    L.Jump l -> Set.singleton l
    L.Br _ l1 l2 -> Set.fromList [l1,l2]
    L.CallBr _ _ _ norm other -> Set.fromList (norm:other)
    L.Invoke _ _ _ l1 l2 -> Set.fromList [l1,l2]
    L.IndirectBr _ ls -> Set.fromList ls
    L.Switch _ ldef ls -> Set.fromList (ldef:map snd ls)
    _ -> buildSuccSet ss


-- | Compute predecessor sets from the successor sets already computed in @buildBlockInfo@
updatePredSets :: LLVMBlockInfoMap s -> LLVMBlockInfoMap s
updatePredSets bim0 = Foldable.foldl' upd bim0 predEdges
  where
   upd bim (to,from) = Map.adjust (\bi -> bi{ block_pred_set = Set.insert from (block_pred_set bi) }) to bim

   predEdges =
     [ (to,from) | (from, bi) <- Map.assocs bim0
                 , to <- Set.elems (block_succ_set bi)
     ]

-- | Compute use sets for each basic block. These sets list all the
-- virtual registers that must be assigned before jumping to a
-- block.
--
-- This is essentially a backward fixpoint computation based on the
-- identifiers used in the block statements.  We iterate the use/def
-- transfer function until no more changes are made.  Because it is a
-- backward analysis, we (heuristically) examine the blocks in
-- descending order, and re-add blocks to the workset based on
-- predecessor maps.
--
-- This fixpoint computation terminates for the usual reasons: the transfer
-- function is monotonic (use sets only increase) and has no infinite
-- chains (in the worst case, all the finitely-many identifiers in the
-- function end up in every use set).
computeUseSets :: LLVMBlockInfoMap s -> LLVMBlockInfoMap s
computeUseSets bim0 = loop bim0 (Map.keysSet bim0) -- start with all blocks in the workset
  where
  loop bim ws =
    -- choose the largest remaining block label in the workset
    case Set.maxView ws of
      -- if the workset is empty, we are done
      Nothing -> bim
      Just (l, ws') ->
        -- look up the current block information relating to block l
        case Map.lookup l bim of
          Nothing -> panic "computeUseSets" ["Could not find label", show l]
          Just bi ->
            -- run the transfer function and compute an updated use set
            case updateUseSet l bi bim of
              -- if there is no update, continue down the work set
              Nothing -> loop bim ws'
              -- if we updated the use set, record it in the block map and
              -- add all the predecessors of this block back to the work set
              Just bi' ->
                loop (Map.insert l bi' bim) (Set.union ws' (block_pred_set bi'))

-- | Run the use/def transfer function on the block body and update the block info if
-- any changes are detected
updateUseSet :: L.BlockLabel -> LLVMBlockInfo s -> Map L.BlockLabel (LLVMBlockInfo s) -> Maybe (LLVMBlockInfo s)
updateUseSet lab bi bim = if newuse == block_use_set bi then Nothing else Just bi{ block_use_set = newuse }
  where
  newuse = loop (block_body bi)

  loop [] = mempty

  -- invoke and callbr are a special case when their return values are assigned
  -- to registers: the return values can only be used in the "normal" successor
  -- block.

  loop (L.Result nm i _dr _md:ss) =
    case i of
      L.Invoke _tp f args l_normal l_unwind ->
            -- the use sets from the function value, arguments, and unwind label
        let uss = [useVal f, useLabel lab l_unwind bim] ++ map useTypedVal args
            -- the use set from the normal return label, note that nm is in scope here
            u_normal = Set.delete nm (useLabel lab l_normal bim)
            -- invoke is a block terminator, we can ignore the tail of the list
         in Set.unions (u_normal : uss)

      L.CallBr _tp f args l_normal ls ->
            -- the use sets from the function value, arguments, and non-normal
            -- labels
        let uss = useVal f:(map (\l -> useLabel lab l bim) ls ++ map useTypedVal args)
            -- the use set from the normal return label, note that nm is in scope here
            u_normal = Set.delete nm (useLabel lab l_normal bim)
            -- callbr is a block terminator, we can ignore the tail of the list
         in Set.unions (u_normal : uss)

      -- In other cases, combine the use set of the instruction with
      -- the use set of following instructions, after deleting the register
      -- defined here
      _ -> Set.union (instrUse lab i bim) (Set.delete nm (loop ss))

  loop (L.Effect i _dr _md:ss) = Set.union (instrUse lab i bim) (loop ss)

instrUse :: L.BlockLabel -> L.Instr -> Map L.BlockLabel (LLVMBlockInfo s) -> Set L.Ident
instrUse from i bim = Set.unions $ case i of
  L.Phi{} -> [] -- NB, phi node use is handled in `useLabel`
  L.RetVoid -> []
  L.Ret tv -> [useTypedVal tv]
  L.Arith _op x y -> [useTypedVal x, useVal y]
  L.Bit _op x y -> [useTypedVal x, useVal y ]
  L.Conv _op x _tp -> [useTypedVal x]
  L.Call _tailCall _tp f args -> useVal f : map useTypedVal args
  -- NB, this is only correct for "callbr" instructions that don't assign the return value
  L.CallBr _tp f args norm ls ->
    [useVal f, useLabel from norm bim] ++
      map (\l -> useLabel from l bim) ls ++
      map useTypedVal args
  L.Alloca _tp Nothing  _align -> []
  L.Alloca _tp (Just x) _align -> [useTypedVal x]
  L.Load _tp p _ord _align -> [useTypedVal p]
  L.Store p v _ord _align -> [useTypedVal p, useTypedVal v]
  L.Fence{} -> []
  L.CmpXchg _weak _vol p v1 v2 _s _o1 _o2 -> map useTypedVal [p,v1,v2]
  L.AtomicRW _vol _op p v _s _o -> [useTypedVal p, useTypedVal v]
  L.ICmp _samesign _op x y -> [useTypedVal x, useVal y]
  L.FCmp _op x y -> [useTypedVal x, useVal y]
  L.GEP _ib _tp base args -> useTypedVal base : map useTypedVal args
  L.Select c x y -> [ useTypedVal c, useTypedVal x, useVal y ]
  L.ExtractValue x _ixs -> [useTypedVal x]
  L.InsertValue x y _ixs -> [useTypedVal x, useTypedVal y]
  L.ExtractElt x y -> [useTypedVal x, useVal y]
  L.InsertElt x y z -> [useTypedVal x, useTypedVal y, useVal z]
  L.ShuffleVector x y z -> [useTypedVal x, useVal y, useTypedVal z]
  L.Jump l -> [useLabel from l bim]
  L.Br c l1 l2 -> [useTypedVal c, useLabel from l1 bim, useLabel from l2 bim]
  -- NB, this is only correct for "invoke" instructions that don't assign the return value
  L.Invoke _tp f args l1 l2 -> [useVal f, useLabel from l1 bim, useLabel from l2 bim] ++ map useTypedVal args
  L.Comment{} -> []
  L.Unreachable -> []
  L.Unwind -> [] -- ??
  L.VaArg x _tp -> [useTypedVal x]
  L.IndirectBr x ls -> useTypedVal x : [ useLabel from l bim | l <- ls ]
  L.Switch c def bs -> useTypedVal c : useLabel from def bim : [ useLabel from l bim | (_,l) <- bs ]
  L.Resume x -> [useTypedVal x]
  L.LandingPad _tp Nothing _ cls -> map useClause cls
  L.LandingPad _tp (Just cleanup) _ cls -> useTypedVal cleanup : map useClause cls
  L.UnaryArith _op x -> [useTypedVal x]
  L.Freeze x -> [useTypedVal x]

useClause :: L.Clause -> Set L.Ident
useClause (L.Catch v) = useTypedVal v
useClause (L.Filter v) = useTypedVal v

useLabel :: L.BlockLabel -> L.BlockLabel -> Map L.BlockLabel (LLVMBlockInfo s) -> Set L.Ident
useLabel from to bim =
  case Map.lookup to bim of
    Nothing -> panic "useLabel" ["Could not find label", show to]
    Just bi ->
      let phiList =
            case Map.lookup from (block_phi_map bi) of
              Nothing -> []
              Just ps -> toList ps
      in Set.unions (block_use_set bi : [ useVal v | (_,_,v) <- phiList ])

-- | Compute the set of identifiers referenced by the given typed value
useTypedVal :: L.Typed (L.Value) -> Set L.Ident
useTypedVal tv = useVal (L.typedValue tv)

-- | Compute the set of identifiers referenced by the given value
useVal :: L.Value -> Set L.Ident
useVal v = Set.unions $ case v of
  L.ValInteger{} ->  []
  L.ValBool{} -> []
  L.ValHalf{} -> []
  L.ValBFloat{} -> []
  L.ValFloat{} -> []
  L.ValDouble{} -> []
  L.ValFP80{} -> []
  L.ValFP128{} -> []
  L.ValFP128_PPC{} -> []
  L.ValIdent i -> [Set.singleton i]
  L.ValSymbol _s -> []
  L.ValNull -> []
  L.ValArray _tp vs -> map useVal vs
  L.ValVector _tp vs -> map useVal vs
  L.ValStruct vs -> map useTypedVal vs
  L.ValPackedStruct vs -> map useTypedVal vs
  L.ValString _ -> []
  L.ValConstExpr{} -> [] -- TODO? should we look through constant exprs?
  L.ValUndef -> []
  L.ValLabel _ -> []
  L.ValZeroInit -> []
  L.ValAsm{} -> [] -- TODO! inline asm ...
  L.ValPoison{} -> []

  -- NB! metadata values are not considered as part of our use analysis
  L.ValMd _md -> []


-- | Given the statements in a basic block, find all the phi instructions and
-- compute the list of assignments that must be made for each predecessor block.
buildPhiMap :: [L.Stmt] -> Map L.BlockLabel (Seq (L.Ident, L.Type, L.Value))
buildPhiMap ss = go ss Map.empty
 where go (L.Result ident (L.Phi tp xs) _ _ : stmts) m = go stmts (go' ident tp xs m)
       go _ m = m

       f x mseq = Just (fromMaybe Seq.empty mseq Seq.|> x)

       go' ident tp ((v, lbl) : xs) m = go' ident tp xs (Map.alter (f (ident,tp,v)) lbl m)
       go' _ _ [] m = m
