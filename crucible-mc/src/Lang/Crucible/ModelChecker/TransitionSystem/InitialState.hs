{-# LANGUAGE RecordWildCards #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.TransitionSystem.Builder
-- Description      : Entry point into facilities for building a transition system
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.TransitionSystem.InitialState
  ( makeInitialState,
  )
where

import qualified Control.Lens as L
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)
import Lang.Crucible.ModelChecker.GlobalInfo
import Lang.Crucible.ModelChecker.NamingConventions
import Lang.Crucible.ModelChecker.SallyWhat4
import qualified Text.LLVM as TL
import qualified What4.Interface as What4

-- | @initialStateGlobal@ turns a @GlobInfo@ gathered information about a global
-- variable into a @Pred sym@ that can be used as a conjunct in the initial
-- state predicate.  The predicate simply asserts that the global variable is
-- equal to its initial value.
initialStateGlobal ::
  Backend.IsSymInterface sym =>
  sym ->
  GlobalInfo sym tp ->
  IO (What4.Pred sym)
initialStateGlobal sym (GlobalInfo {..}) =
  case globalTypeRepr of
    LLVMPointerRepr w ->
      do
        let (_, bv) = llvmPointerView globalRegValue
        let TL.Symbol globalName = globalSymbol
        v <- What4.freshBoundedBV sym (userSymbol' globalName) w Nothing Nothing
        What4.bvEq sym v bv
    _ -> error "initialStateGlobal: encountered a global variable that was not an LLVM pointer, please report to the maintainers."

makeInitialState ::
  Backend.IsSymInterface sym =>
  Core.CFG ext blocks init ret ->
  sym ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  What4.SymNat sym ->
  What4.Pred sym ->
  IO (What4.Pred sym)
makeInitialState cfg sym globInfos currentBlock hasReturned =
  do
    let initialBlock = natOfBlockID (Core.cfgEntryBlockID cfg)
    initialStateGlobalsPredicates <- sequenceA $ toListFC (initialStateGlobal sym) globInfos
    initialBlockPredicate <-
      do
        initialBlockLit <- What4.natLit sym initialBlock
        What4.natEq sym currentBlock initialBlockLit
    initialStateHasNotReturned <- What4.notPred sym hasReturned
    What4.andAllOf
      sym
      L.folded
      ( initialBlockPredicate
          : initialStateHasNotReturned
          : initialStateGlobalsPredicates
      )
