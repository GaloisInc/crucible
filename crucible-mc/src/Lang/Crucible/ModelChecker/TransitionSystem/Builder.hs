{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- UndecidableInstances is for CtxFlatten

-- |
-- Module           : Lang.Crucible.ModelChecker.TransitionSystem.Builder
-- Description      : Entry point into facilities for building a transition system
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.TransitionSystem.Builder
  ( makeTransitionSystem,
  )
where

import Data.Functor.Const (Const (..))
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.ModelChecker.AsBaseType
import Lang.Crucible.ModelChecker.GlobalInfo
import Lang.Crucible.ModelChecker.NamingConventions
import Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
import Lang.Crucible.ModelChecker.TransitionSystem.InitialState
import Lang.Crucible.ModelChecker.TransitionSystem.Queries
import Lang.Crucible.ModelChecker.TransitionSystem.StateCtx
import Lang.Crucible.ModelChecker.TransitionSystem.Transitions
import Lang.Crucible.Types
import qualified What4.Interface as What4
import qualified What4.TransitionSystem as TS

-- | @makeTransitionSystem@ uses all of the gathered program information to
-- build the final transition system.
makeTransitionSystem ::
  forall ext blocks init ret globCtx sym.
  Backend.IsSymInterface sym =>
  sym ->
  Core.CFG ext blocks init ret ->
  ( forall stateFields.
    Ctx.Assignment (Const What4.SolverSymbol) stateFields ->
    Ctx.Assignment BaseTypeRepr stateFields ->
    Namespacer sym stateFields
  ) ->
  -- | Info about the global context
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Assignment (BlockInfo sym globCtx) blocks ->
  IO (TS.TransitionSystem sym (StateCtx blocks globCtx init))
makeTransitionSystem sym cfg namespacer globInfos blockInfos =
  do
    let initArgs :: CtxRepr init = Core.cfgArgTypes cfg
    let initArgsNames = namesForContext functionArgumentName initArgs
    -- let retTp = regType retVal
    let blocksInputs = fmapFC Core.blockInputs (Core.cfgBlockMap cfg)
    let blocksIDs = fmapFC Core.blockID (Core.cfgBlockMap cfg)
    let blocksInputsNames =
            Ctx.zipWith
              (\blockID blockInputs -> namesForContext (blockArgumentName blockID) blockInputs)
              blocksIDs
              blocksInputs
    -- NOTE: the structure of @stateReprs@ and @stateSymbols@ must match exactly
    -- the structure of @StateCtx@
    let stateReprs =
          ( (asBaseTypeReprs (flattenCtx blocksInputs))
              Ctx.<++> ( asBaseTypeReprs (globalTypeReprs globInfos)
                           Ctx.<++> asBaseTypeReprs initArgs
                       )
          )
            -- `Ctx.extend` asBaseTypeRepr retTp
            `Ctx.extend` BaseBoolRepr
            `Ctx.extend` BaseNatRepr
    let stateSymbols =
          ( asBaseTypeNames (flattenCtx blocksInputsNames)
              Ctx.<++> ( asBaseTypeNames (globalSymbolsAsSolverSymbols globInfos)
                           Ctx.<++> asBaseTypeNames initArgsNames
                       )
          )
            -- `Ctx.extend` Const returnValueVariable
            `Ctx.extend` Const hasReturnedVariable
            `Ctx.extend` Const currentBlockVariable
    currentBlock <- What4.freshConstant sym currentBlockVariable BaseNatRepr
    hasReturned <- What4.freshConstant sym hasReturnedVariable BaseBoolRepr
    let actualNamespacer = namespacer stateSymbols stateReprs
    return $
      TS.TransitionSystem
        { stateReprs,
          stateNames = stateSymbols,
          initialStatePredicate = \_ -> makeInitialState cfg sym globInfos currentBlock hasReturned,
          stateTransitions =
            makeStateTransitions
              sym
              actualNamespacer
              stateReprs
              blockInfos
              globInfos
              (Ctx.size initArgs),
          queries = makeQueries sym actualNamespacer currentBlock hasReturned blockInfos
        }
