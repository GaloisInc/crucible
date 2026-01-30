-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Analysis.Reachable
-- Description      : Compute the reachable subgraph of a CFG
-- Copyright        : (c) Galois, Inc 2015
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Compute reachability on CFG blocks, reduce the CFG to include just
-- the reachable blocks, and remap block labels in the program to point
-- to the new, relabeled blocks.
------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
module Lang.Crucible.Analysis.Reachable
  ( reachableCFG
  ) where

import           Control.Monad.Identity
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import qualified Data.Bimap as Bimap
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC
import qualified Data.Parameterized.Context as Ctx
import           Lang.Crucible.CFG.Core

remapBlockID :: MapF (BlockID b) (BlockID b') -> BlockID b a -> BlockID b' a
remapBlockID m b =
  fromMaybe (error $ "Could not remap block " ++ show b)
            (MapF.lookup b m)

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
    VariantElim c r a -> VariantElim c r (fmapFC (remapSwitchTarget m) a)
    Return r          -> Return r
    TailCall f c a    -> TailCall f c a
    ErrorStmt r       -> ErrorStmt r

remapBlock :: MapF (BlockID b) (BlockID b')
           -> BlockID b' ctx
           -> Block ext b r ctx
           -> Block ext b' r ctx
remapBlock m nm b =
  Block { blockID = nm
        , blockInputs = blockInputs b
        , _blockStmts =
          runIdentity $
            stmtSeqTermStmt
              (\(l,s) -> Identity (TermStmt l (remapTermStmt m s)))
              (_blockStmts b)
        }

mkOldMap :: forall ext b b' r
         .  Ctx.Assignment (Block ext b r) b'
         -> MapF (BlockID b) (BlockID b')
mkOldMap a = Ctx.forIndex (Ctx.size a) f MapF.empty
  where f :: MapF (BlockID b) (BlockID b')
          -> Ctx.Index b' c
          -> MapF (BlockID b) (BlockID b')
        f m new_index = MapF.insert (blockID b) (BlockID new_index) m
          where b = a Ctx.! new_index

remapBlockMap :: forall ext b b' ret
               . MapF (BlockID b) (BlockID b')
              -> Ctx.Assignment (Block ext b ret) b'
                 -- ^ Map new blocks to old block IDs.
              -> BlockMap ext b' ret
remapBlockMap oldToNew newToOld = Ctx.generate (Ctx.size newToOld) $ f
  where f :: Ctx.Index b' ctx -> Block ext b' ret ctx
        f i = remapBlock oldToNew (BlockID i) (newToOld Ctx.! i)

exploreReachable :: BlockMap ext blocks ret
                 -> BlockID blocks init
                 -> Map (Some (BlockID blocks)) Int
exploreReachable m d = exploreReachable' m [Some d] Map.empty

exploreReachable' :: BlockMap ext blocks ret
                  -> [Some (BlockID blocks)]
                  -> Map (Some (BlockID blocks)) Int
                  -> Map (Some (BlockID blocks)) Int
exploreReachable' _ [] r = r
exploreReachable' m (Some h:l) r =
  case Map.lookup (Some h) r of
    Just c -> exploreReachable' m l (Map.insert (Some h) (c + 1) r)
    Nothing -> do
      let b = getBlock h m
      exploreReachable' m (nextBlocks b ++ l) (Map.insert (Some h) 1 r)

insReachable :: BlockMap ext b r
             -> Some (Ctx.Assignment (Block ext b r))
             -> Some (BlockID b)
             -> Some (Ctx.Assignment (Block ext b r))
insReachable m (Some a) (Some (BlockID block_id)) = Some $ a Ctx.:> (m Ctx.! block_id)



reachableCFG :: CFG ext blocks init ret -> SomeCFG ext init ret
reachableCFG g =
    case foldl (insReachable old_map) (Some Ctx.empty) (Map.keys reachables) of
      Some newToOld ->
--          trace ("Size change: " ++ show (Ctx.sizeInt (Ctx.size old_map) - Ctx.sizeInt (Ctx.size new_map))) $
                 SomeCFG g'
        where oldToNew = mkOldMap newToOld
              new_map = remapBlockMap oldToNew newToOld
              new_breakpoints = Bimap.mapR (mapSome $ remapBlockID oldToNew) (cfgBreakpoints g)
              g' = CFG { cfgHandle = cfgHandle g
                       , cfgBlockMap = new_map
                       , cfgEntryBlockID = remapBlockID oldToNew entry_id
                       , cfgBreakpoints = new_breakpoints
                       }
  where old_map = cfgBlockMap g
        entry_id = cfgEntryBlockID g
        reachables = exploreReachable old_map entry_id
