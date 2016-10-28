-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Analysis.Reachable
-- Description      : Trims a CFG to the reachable subset
-- Copyright        : (c) Galois, Inc 2016
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
-- License          : BSD3
------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
module Lang.Crucible.Analysis.Reachable
  ( reachableCFG
  ) where

import           Control.Monad.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.UnsafeContext as Ctx
import           Lang.Crucible.Core

remapBlockID :: MapF (BlockID b) (BlockID b') -> BlockID b a -> BlockID b' a
remapBlockID m b =
  case MapF.lookup b m of
    Nothing -> error $ "Could not remap block " ++ show b
    Just r -> r

remapJumpTarget :: MapF (BlockID b) (BlockID b')
                -> JumpTarget b c -> JumpTarget b' c
remapJumpTarget m (JumpTarget x r a) = JumpTarget (remapBlockID m x) r a

remapSwitchTarget :: MapF (BlockID b) (BlockID b')
                  -> SwitchTarget b c r -> SwitchTarget b' c r
remapSwitchTarget m (SwitchTarget x r a) = SwitchTarget (remapBlockID m x) r a


remapTermStmt :: MapF (BlockID b) (BlockID b') -> TermStmt b ret c -> TermStmt b' ret c
remapTermStmt m ts =
  case ts of
    Jump jmp -> Jump (remapJumpTarget m jmp)
    Br c x y -> Br c (remapJumpTarget m x) (remapJumpTarget m y)
    MaybeBranch tp r x y -> MaybeBranch tp r (remapSwitchTarget m x) (remapJumpTarget m y)
    MSwitchStmt r x   -> MSwitchStmt r (fmapF (remapSwitchTarget m) x)
    VariantElim c r a -> VariantElim c r (fmapFC (remapSwitchTarget m) a)
    Return r          -> Return r
    TailCall f c a    -> TailCall f c a
    ErrorStmt r       -> ErrorStmt r

remapBlock :: MapF (BlockID b) (BlockID b')
           -> BlockID b' ctx
           -> Block b r ctx
           -> Block b' r ctx
remapBlock m nm b =
  Block { blockID = nm
        , blockInputs = blockInputs b
        , _blockStmts =
          runIdentity $
            stmtSeqTermStmt
              (\(l,s) -> Identity (TermStmt l (remapTermStmt m s)))
              (_blockStmts b)
        }

mkOldMap :: forall b b' r
         .  Ctx.Assignment (Block b r) b'
         -> MapF (BlockID b) (BlockID b')
mkOldMap a = Ctx.forIndex (Ctx.size a) f MapF.empty
  where f :: MapF (BlockID b) (BlockID b')
          -> Ctx.Index b' c
          -> MapF (BlockID b) (BlockID b')
        f m new_index = MapF.insert (blockID b) (BlockID new_index) m
          where b = a Ctx.! new_index

remapBlockMap :: forall b b' ret
               . MapF (BlockID b) (BlockID b')
              -> Ctx.Assignment (Block b ret) b'
                 -- ^ Map new blocks to old block IDs.
              -> BlockMap b' ret
remapBlockMap oldToNew newToOld = Ctx.generate (Ctx.size newToOld) $ f
  where f :: Ctx.Index b' ctx -> Block b' ret ctx
        f i = remapBlock oldToNew (BlockID i) (newToOld Ctx.! i)

exploreReachable :: BlockMap blocks ret
                 -> BlockID blocks init
                 -> Map (Some (BlockID blocks)) Int
exploreReachable m d = exploreReachable' m [Some d] Map.empty

exploreReachable' :: BlockMap blocks ret
                  -> [Some (BlockID blocks)]
                  -> Map (Some (BlockID blocks)) Int
                  -> Map (Some (BlockID blocks)) Int
exploreReachable' _ [] r = r
exploreReachable' m (Some h:l) r =
  case Map.lookup (Some h) r of
    Just c -> exploreReachable' m l (Map.insert (Some h) (c+1) r)
    Nothing -> do
      let b = getBlock h m
      exploreReachable' m (nextBlocks b ++ l) (Map.insert (Some h) 1 r)

insReachable :: BlockMap b r
             -> Some (Ctx.Assignment (Block b r))
             -> Some (BlockID b)
             -> Some (Ctx.Assignment (Block b r))
insReachable m (Some a) (Some (BlockID block_id)) = Some $ a Ctx.%> (m Ctx.! block_id)



reachableCFG :: CFG blocks init ret -> SomeCFG init ret
reachableCFG g =
    case foldl (insReachable old_map) (Some Ctx.empty) (Map.keys reachables) of
      Some newToOld ->
--          trace ("Size change: " ++ show (Ctx.sizeInt (Ctx.size old_map) - Ctx.sizeInt (Ctx.size new_map))) $
                 SomeCFG g'
        where oldToNew = mkOldMap newToOld
              new_map = remapBlockMap oldToNew newToOld
              g' = CFG { cfgHandle = cfgHandle g
                       , cfgBlockMap = new_map
                       , cfgEntryBlockID = remapBlockID oldToNew entry_id
                       }
  where old_map = cfgBlockMap g
        entry_id = cfgEntryBlockID g
        reachables = exploreReachable old_map entry_id
