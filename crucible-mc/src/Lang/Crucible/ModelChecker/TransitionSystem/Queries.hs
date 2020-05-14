{-# LANGUAGE RecordWildCards #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.TransitionSystem.Queries
-- Description      : Builder for the queries of the transition system
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.TransitionSystem.Queries
  ( makeQueries,
  )
where

import qualified Control.Lens as L
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
import qualified What4.Interface as What4

makeBlockQuery ::
  Backend.IsSymInterface sym =>
  sym ->
  What4.SymNat sym ->
  What4.Pred sym ->
  BlockInfo sym globCtx block ->
  IO (What4.Pred sym)
makeBlockQuery sym currentBlock hasReturned (BlockInfo {..}) =
  do
    thisBlock <- What4.natLit sym blockInfoID
    isCurrentBlock <- What4.natEq sym currentBlock thisBlock
    -- we need to state that the program has not returned, because the
    -- transition to the state where the program has returned allows arbitrary
    -- changes to variables of the last block
    notHasReturned <- What4.notPred sym hasReturned
    condition <- What4.andPred sym isCurrentBlock notHasReturned
    obligations <- What4.andAllOf sym L.folded blockInfoObligations
    What4.impliesPred sym condition obligations

makeQueries ::
  Backend.IsSymInterface sym =>
  sym ->
  What4.SymNat sym ->
  What4.Pred sym ->
  Ctx.Assignment (BlockInfo sym globCtx) blocks ->
  IO [What4.Pred sym]
makeQueries sym currentBlock hasReturned blockInfos =
  do
    blockQueries <- sequenceA $ toListFC (makeBlockQuery sym currentBlock hasReturned) blockInfos
    -- finalQuery <-
    --   do
    --     finalObligation <- What4.andAllOf sym L.folded finalObligations
    --     What4.impliesPred sym hasReturned finalObligation
    return blockQueries
