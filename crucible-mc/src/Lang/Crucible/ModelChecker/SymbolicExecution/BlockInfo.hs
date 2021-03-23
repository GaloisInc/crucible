{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
-- Description      : Information about blocks gathered during their symbolic execution
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
  ( BlockEnd (..),
    BlockInfo (..),
  )
where

import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Types
import qualified What4.Interface as What4

-- | @BlockEnd@ is a short descriptor of how a given block ends, capturing some
-- possible continuation arguments that we need to produce a model.
data BlockEnd sym
  = BlockEndAborts
  | BlockEndBranches
      (What4.Pred sym) -- condition under which true branch is taken
      (Core.Some (ResolvedJump sym)) -- true branch target
      (Core.Some (ResolvedJump sym)) -- false branch target
  | BlockEndJumps (Core.Some (ResolvedJump sym))
  | BlockEndReturns (Core.Some (RegEntry sym))

data BlockInfo sym (globCtx :: Ctx CrucibleType) (block :: Ctx CrucibleType) = BlockInfo
  { -- | how this block ends
    blockInfoEnd :: BlockEnd sym,
    -- | symbolic value for global variables at the end of the block
    blockInfoGlobals :: Ctx.Assignment (RegEntry sym) globCtx,
    blockInfoID :: Integer,
    -- | assumptions that hold at the **end** of the block
    blockInfoAssumptions :: [What4.Pred sym],
    -- | obligations pending at the **end** of the block
    blockInfoObligations :: [What4.Pred sym],
    -- | retains the size of the original block
    blockInfoSize :: Ctx.Size block
  }
