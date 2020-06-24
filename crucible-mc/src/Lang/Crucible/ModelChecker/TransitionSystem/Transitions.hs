{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.TransitionSystem.Transitions
-- Description      : Builder for the transitions of the transition system
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.TransitionSystem.Transitions
  ( Namespacer (..),
    makeStateTransitions,
  )
where

import qualified Control.Lens as L
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader, asks, runReaderT)
import Data.Functor.Const (Const (..), getConst)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)
import Lang.Crucible.ModelChecker.AsBaseType
import Lang.Crucible.ModelChecker.GlobalInfo
import Lang.Crucible.ModelChecker.NamingConventions
import Lang.Crucible.ModelChecker.SallyWhat4
import Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
import Lang.Crucible.ModelChecker.TransitionSystem.Namespacer
import Lang.Crucible.ModelChecker.TransitionSystem.StateCtx
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Types
import qualified What4.Interface as What4
import Prelude hiding (init)

data TransitionSystemReader sym blocks globCtx init = TransitionSystemReader
  { -- | @tsBlockSizes@ retains the size of every block, so that we can
    -- adjust indices scoping over just the global context into indices
    -- scoping over the aggregate @StateCtx@
    tsBlockSizes :: Ctx.Assignment Ctx.Size blocks,
    -- | @tsInitSize@ retains the size of the initial data, as we don't
    -- retain any other assignment we could retrieve it from
    tsInitSize :: Ctx.Size init,
    tsCurrentBlock :: What4.SymNat sym,
    tsCurrentHasReturned :: What4.Pred sym,
    tsCurrentState :: What4.SymStruct sym (StateCtx blocks globCtx init),
    tsGlobalInfos :: Ctx.Assignment (GlobalInfo sym) globCtx,
    -- | @tsNamespacer@ is a function that can manipulate any expression to
    -- add a given namespace to all variables, turning variables @v@ into
    -- either @state.v@ or @next.v@ depending on which namespace is passed.
    -- It will always be equal to @addNamespaceToVariables@ in practice, but
    -- abstracting it like this allows us to make all type signatures be in
    -- terms of an abstracted @sym@ rather than the verbose concrete
    -- expression type.
    tsNamespacer :: Namespacer sym (StateCtx blocks globCtx init),
    tsNextBlock :: What4.SymNat sym,
    tsNextHasReturned :: What4.Pred sym,
    tsNextState :: What4.SymStruct sym (StateCtx blocks globCtx init),
    tsStateRepr :: Ctx.Assignment BaseTypeRepr (StateCtx blocks globCtx init),
    tsSym :: sym
  }

regEntryExpr ::
  Backend.IsSymInterface sym =>
  RegEntry sym block ->
  IO (What4.SymExpr sym (AsBaseType' block))
regEntryExpr (RegEntry {..}) =
  do
    case regType of
      LLVMPointerRepr _ ->
        do
          let (_, bv) = llvmPointerView regValue
          return bv
      rt -> error $ show rt

nextArgPred ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  Core.BlockID blocks' tp ->
  Ctx.Index block arg ->
  RegEntry sym arg ->
  m (Const (What4.Pred sym) arg)
nextArgPred blockID idx regEntry@(RegEntry {..}) =
  do
    namespacer <- asks tsNamespacer
    next <- asks tsNextState
    state <- asks tsCurrentState
    sym <- asks tsSym
    liftIO $ do
      let varName = blockArgumentName blockID idx
      argVar <- What4.freshConstant sym varName (asBaseTypeRepr regType)
      arg <- runNamespacer namespacer next argVar
      argValue <- runNamespacer namespacer state =<< regEntryExpr regEntry
      Const <$> What4.isEq sym arg argValue

nextArgsPred ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  Core.BlockID blocks' tp ->
  RegMap sym block ->
  m (What4.Pred sym)
nextArgsPred blockID rm =
  do
    sym <- asks tsSym
    nextArgsPreds <-
      toListFC getConst
        <$> Ctx.traverseWithIndex
          (nextArgPred blockID)
          (regMap rm)
    liftIO $ What4.andAllOf sym L.folded nextArgsPreds

makeBlockEndPred ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  BlockEnd sym ->
  m (What4.Pred sym)
makeBlockEndPred BlockEndAborts =
  asks tsNextHasReturned -- FIXME: add nextHasAborted
makeBlockEndPred
  ( BlockEndBranches
      rawTruePred
      (Core.Some (ResolvedJump trueTarget trueArgs))
      (Core.Some (ResolvedJump falseTarget falseArgs))
    ) =
    do
      namespacer <- asks tsNamespacer
      nextBlock <- asks tsNextBlock
      nextHasReturned <- asks tsNextHasReturned
      state <- asks tsCurrentState
      sym <- asks tsSym
      let nextBlockIs b = What4.natEq sym nextBlock =<< What4.natLit sym b
      trueBlockArgs <- nextArgsPred trueTarget trueArgs
      falseBlockArgs <- nextArgsPred falseTarget falseArgs
      liftIO $ do
        doesNotReturn <- What4.notPred sym nextHasReturned
        truePred <- runNamespacer namespacer state rawTruePred
        falsePred <- runNamespacer namespacer state =<< What4.notPred sym truePred
        nextBlockIsTrueBlock <- nextBlockIs (natOfBlockID trueTarget)
        trueBlockConclusion <- What4.andPred sym nextBlockIsTrueBlock trueBlockArgs
        trueBlock <- What4.impliesPred sym truePred trueBlockConclusion
        nextBlockIsFalseBlock <- nextBlockIs (natOfBlockID falseTarget)
        falseBlockConclusion <- What4.andPred sym nextBlockIsFalseBlock falseBlockArgs
        falseBlock <- What4.impliesPred sym falsePred falseBlockConclusion
        What4.andAllOf sym L.folded [doesNotReturn, trueBlock, falseBlock]
makeBlockEndPred (BlockEndJumps (Core.Some (ResolvedJump targetBlock args))) =
  do
    nextBlock <- asks tsNextBlock
    nextHasReturned <- asks tsNextHasReturned
    sym <- asks tsSym
    let nextBlockIs b = What4.natEq sym nextBlock =<< What4.natLit sym b
    nextBlockArgs <- nextArgsPred targetBlock args
    liftIO $ do
      doesNotReturn <- What4.notPred sym nextHasReturned
      nextBlockEq <- nextBlockIs (natOfBlockID targetBlock)
      What4.andAllOf sym L.folded [doesNotReturn, nextBlockEq, nextBlockArgs]
makeBlockEndPred (BlockEndReturns (Core.Some _regEntry)) =
  asks tsNextHasReturned -- FIXME: set return value?

makeGlobalPred ::
  forall sym m blocks globCtx init tp.
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  Ctx.Index globCtx tp ->
  RegEntry sym tp ->
  m (Const (What4.Pred sym) tp)
makeGlobalPred ndx regEntry =
  do
    namespacer <- asks tsNamespacer
    next <- asks tsNextState
    state <- asks tsCurrentState
    -- stateFieldsRepr <- asks tsStateCtxRepr
    sym <- asks tsSym
    ndx' <-
      globalIndexToStateIndex
        <$> asks tsBlockSizes
        <*> (Ctx.size <$> asks tsGlobalInfos)
        <*> asks tsInitSize
        <*> pure ndx
    liftIO $ do
      globalNext <- What4.structField sym next ndx'
      -- the expression we have is not namespaced, it scopes over the current state
      nextValue <- runNamespacer namespacer state =<< regEntryExpr regEntry
      globalPred <- What4.isEq sym globalNext nextValue
      return (Const globalPred)

makeGlobalsPred ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  Ctx.Assignment (RegEntry sym) globCtx ->
  m (What4.Pred sym)
makeGlobalsPred globalValues =
  do
    globalPreds <- toListFC getConst <$> Ctx.traverseWithIndex makeGlobalPred globalValues
    sym <- asks tsSym
    liftIO $ What4.andAllOf sym L.folded globalPreds

stateTransitionForBlock ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  BlockInfo sym globCtx block ->
  m (What4.SolverSymbol, What4.Pred sym)
stateTransitionForBlock (BlockInfo {..}) =
  do
    currentBlock <- asks tsCurrentBlock
    currentHasReturned <- asks tsCurrentHasReturned
    namespacer <- asks tsNamespacer
    next <- asks tsNextState
    sym <- asks tsSym
    blockEndPred <- makeBlockEndPred blockInfoEnd
    -- We can give the assumptions that arose during this block as given for the
    -- next block.
    blockAssumptionsPred <-
      liftIO $
        runNamespacer namespacer next
          =<< What4.andAllOf sym L.folded blockInfoAssumptions
    blockGlobalsPred <- makeGlobalsPred blockInfoGlobals
    liftIO $ do
      thisBlock <- What4.natLit sym blockInfoID
      isCurrentBlock <- What4.natEq sym thisBlock currentBlock
      hasNotReturned <- What4.notPred sym currentHasReturned
      transition <-
        What4.andAllOf
          sym
          L.folded
          $ [
              -- only consider this transition if the program has *not* terminated
              hasNotReturned,
              -- only consider this transition if this block is the current block
              isCurrentBlock,
              -- this predicate describes how this block ends
              blockEndPred,
              -- this predicate describes the assumptions that may be made from
              -- this block on
              blockAssumptionsPred,
              -- this predicate describes how global variables change
              blockGlobalsPred
            ]
      return (userSymbol' ("Transition_for_block_" ++ show blockInfoID), transition)

makeStateTransition ::
  stateFields ~ StateCtx blocks globCtx init =>
  Backend.IsSymInterface sym =>
  sym ->
  Namespacer sym stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Size init ->
  What4.SymStruct sym stateFields ->
  What4.SymStruct sym stateFields ->
  BlockInfo sym globCtx block ->
  IO (What4.SolverSymbol, What4.Pred sym)
makeStateTransition sym namespacer stateFieldsRepr blockSizes globInfos initSize state next blockInfo = do
  let currentBlockIndex = makeCurrentBlockIndex blockSizes (Ctx.size globInfos) initSize
  let hasReturnedIndex = makeHasReturnedIndex blockSizes (Ctx.size globInfos) initSize
  stateBlock <- What4.structField sym state currentBlockIndex
  nextBlock <- What4.structField sym next currentBlockIndex
  stateHasReturned <- What4.structField sym state hasReturnedIndex
  nextHasReturned <- What4.structField sym next hasReturnedIndex
  let reader =
        TransitionSystemReader
          { tsBlockSizes = blockSizes,
            tsInitSize = initSize,
            tsCurrentBlock = stateBlock,
            tsCurrentHasReturned = stateHasReturned,
            tsCurrentState = state,
            tsGlobalInfos = globInfos,
            tsNextBlock = nextBlock,
            tsNextHasReturned = nextHasReturned,
            tsNextState = next,
            tsStateRepr = stateFieldsRepr,
            tsNamespacer = namespacer,
            tsSym = sym
          }
  flip runReaderT reader $ stateTransitionForBlock blockInfo

-- | @makeStateTransitions@ builds the actual transitions of the transition
-- system based on information about the basic blocks and transitions across them.
makeStateTransitions ::
  stateFields ~ StateCtx blocks globCtx init =>
  Backend.IsSymInterface sym =>
  sym ->
  Namespacer sym stateFields ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  Ctx.Assignment Ctx.Size blocks ->
  Ctx.Assignment (BlockInfo sym globCtx) blocks ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Size init ->
  What4.SymStruct sym stateFields ->
  What4.SymStruct sym stateFields ->
  IO [(What4.SolverSymbol, What4.Pred sym)]
makeStateTransitions sym namespacer stateFieldsRepr blockSizes blockInfos globInfos initSize state next =
  sequence $ toListFC (makeStateTransition sym namespacer stateFieldsRepr blockSizes globInfos initSize state next) blockInfos
