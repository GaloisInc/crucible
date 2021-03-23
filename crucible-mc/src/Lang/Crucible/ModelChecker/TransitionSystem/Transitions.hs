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

import Control.Arrow ((&&&))
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
  { -- | @tsBlocks@ is used in two ways:
    -- 1. to make outgoing transitions into a given block, we want to use the
    -- target block's assumptions as predicates, therefore, we need information
    -- about other blocks than the current one,
    -- 2. we need the size of this assignment to adjust indices in the compound
    -- context we build.
    tsBlocks :: Ctx.Assignment (BlockInfo sym globCtx) blocks,
    -- | @tsInitSize@ retains the size of the initial data, as we don't
    -- retain any other assignment we could retrieve it from
    tsInitSize :: Ctx.Size init,
    tsCurrentBlock :: What4.SymInteger sym,
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
    tsNextBlock :: What4.SymInteger sym,
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

-- | @findBlockAssumptions@ retrieves the assumptions of the target block.
findBlockAssumptions ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  sym ->
  -- because we retrieve this block from an existential package, we have lost
  -- the equality @blocks ~ blocks'@
  Core.BlockID blocks' args ->
  m (What4.Pred sym)
findBlockAssumptions sym blockID = do
  allBlockAssumptions <- toListFC (blockInfoID &&& blockInfoAssumptions) <$> asks tsBlocks
  case lookup (integerOfBlockID blockID) allBlockAssumptions of
    Nothing -> error $ "findBlockAssumptions: could not find block " ++ show blockID ++ ". Please report."
    Just assumptions -> liftIO $ What4.andAllOf sym L.folded assumptions

-- | @makeBlockEndPred@ creates the predicated that dictates what happens at the
-- end of the block, based on the @BlockEnd@ information.  This can be one of
-- ending the program, jumping to a block, branching between two blocks, or
-- aborting.
--
-- Note that there is a complication here: blocks have been so far analyzed in
-- isolation, but in order to allow transition into some block, we must satisfy
-- its assumptions.  So @makeBlockEndPred@ must find what are the assumptions
-- for the block it claims it can transition to.
makeBlockEndPred ::
  forall sym m blocks globCtx init.
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
      state <- asks tsCurrentState
      sym <- asks tsSym
      truePred <- liftIO $ runNamespacer namespacer state rawTruePred
      falsePred <- liftIO $ What4.notPred sym truePred
      trueBlock <- makeTargetPred trueTarget trueArgs truePred
      falseBlock <- makeTargetPred falseTarget falseArgs falsePred
      liftIO $ What4.andAllOf sym L.folded [trueBlock, falseBlock]
makeBlockEndPred (BlockEndJumps (Core.Some (ResolvedJump targetBlock args))) =
  do
    sym <- asks tsSym
    makeTargetPred targetBlock args (What4.truePred sym)
makeBlockEndPred (BlockEndReturns (Core.Some _regEntry)) =
  asks tsNextHasReturned -- FIXME: set return value?

makeTargetPred ::
  Backend.IsSymInterface sym =>
  MonadIO m =>
  MonadReader (TransitionSystemReader sym blocks globCtx init) m =>
  Core.BlockID blocks' tp ->
  RegMap sym block ->
  What4.Pred sym ->
  m (What4.Pred sym)
makeTargetPred targetBlock args blockCondition = do
  namespacer <- asks tsNamespacer
  next <- asks tsNextState
  nextBlock <- asks tsNextBlock
  nextHasReturned <- asks tsNextHasReturned
  sym <- asks tsSym
  let nextBlockIs b = What4.intEq sym nextBlock =<< What4.intLit sym b
  nextBlockArgs <- nextArgsPred targetBlock args
  rawBlockAssumptions <- findBlockAssumptions sym targetBlock
  -- NOTE: because we wish for the predicate to hold for entering the next
  -- state, we require that it holds of the "next" state
  nextBlockAssumptions <- liftIO $ runNamespacer namespacer next rawBlockAssumptions
  liftIO $ do
    doesNotReturn <- What4.notPred sym nextHasReturned
    nextBlockEq <- nextBlockIs (integerOfBlockID targetBlock)
    blockConclusion <- What4.andAllOf sym L.folded [doesNotReturn, nextBlockEq, nextBlockArgs, nextBlockAssumptions]
    What4.impliesPred sym blockCondition blockConclusion

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
        <$> (fmapFC blockInfoSize <$> asks tsBlocks)
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

-- | @stateTransitionForBlock@ computes the state transition predicate for a
-- given block.  It returns a supposedly fresh name for it, and the predicate,
-- which is made of:
--
-- * a predicate asserting the program has not terminated
--
-- * a predicate asserting the current block is this one
--
-- * predicates about the possible next block(s)
--
-- * predicates freezing the global variables across the block transition
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
      thisBlock <- What4.intLit sym blockInfoID
      isCurrentBlock <- What4.intEq sym thisBlock currentBlock
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
  Ctx.Assignment (BlockInfo sym globCtx) blocks ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Size init ->
  What4.SymStruct sym stateFields ->
  What4.SymStruct sym stateFields ->
  BlockInfo sym globCtx block ->
  IO (What4.SolverSymbol, What4.Pred sym)
makeStateTransition sym namespacer stateFieldsRepr blocks globInfos initSize state next blockInfo = do
  let blockSizes = fmapFC blockInfoSize blocks
  let currentBlockIndex = makeCurrentBlockIndex blockSizes (Ctx.size globInfos) initSize
  let hasReturnedIndex = makeHasReturnedIndex blockSizes (Ctx.size globInfos) initSize
  stateBlock <- What4.structField sym state currentBlockIndex
  nextBlock <- What4.structField sym next currentBlockIndex
  stateHasReturned <- What4.structField sym state hasReturnedIndex
  nextHasReturned <- What4.structField sym next hasReturnedIndex
  let reader =
        TransitionSystemReader
          { tsBlocks = blocks,
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
  Ctx.Assignment (BlockInfo sym globCtx) blocks ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Size init ->
  What4.SymStruct sym stateFields ->
  What4.SymStruct sym stateFields ->
  IO [(What4.SolverSymbol, What4.Pred sym)]
makeStateTransitions sym namespacer stateFieldsRepr blockInfos globInfos initSize state next =
  sequence $ toListFC (makeStateTransition sym namespacer stateFieldsRepr blockInfos globInfos initSize state next) blockInfos
