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
import Lang.Crucible.ModelChecker.SallyWhat4
import Lang.Crucible.ModelChecker.SymbolicExecution.BlockInfo
import Lang.Crucible.ModelChecker.TransitionSystem.InitialState
import Lang.Crucible.ModelChecker.TransitionSystem.Queries
import Lang.Crucible.ModelChecker.TransitionSystem.Transitions
import Lang.Crucible.Types
import qualified What4.Interface as What4
import qualified What4.TransitionSystem as TS

type family CtxFlatten (ctx :: Ctx (Ctx a)) :: Ctx a where
  CtxFlatten Ctx.EmptyCtx = Ctx.EmptyCtx
-- using prefix form to avoid hlint bug
  CtxFlatten (ctxs Ctx.::> ctx) = (Ctx.<+>) (CtxFlatten ctxs) ctx

flattenCtx ::
  Ctx.Assignment (Ctx.Assignment f) blocks ->
  Ctx.Assignment f (CtxFlatten blocks)
flattenCtx ctxs =
  case Ctx.viewAssign ctxs of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctxs' ctx -> flattenCtx ctxs' Ctx.<++> ctx

-- | @makeTransitionSystem@ uses all of the gathered program information to
-- build the final transition system.
makeTransitionSystem ::
  forall ext blocks init ret globCtx sym.
  Backend.IsSymInterface sym =>
  sym ->
  Core.CFG ext blocks init ret ->
  ( forall stateFields.
    Ctx.Assignment BaseTypeRepr stateFields ->
    Namespacer sym stateFields
  ) ->
  -- | Info about the global context
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Assignment (BlockInfo sym globCtx) blocks ->
  IO
    ( TS.TransitionSystem sym
        -- using prefix here only because of a hlint bug
        ( ( (Ctx.<+>)
              (AsBaseTypes (CtxFlatten blocks))
              ( (Ctx.<+>)
                  (AsBaseTypes globCtx)
                  (AsBaseTypes init)
              )
          )
            -- Ctx.::> AsBaseType' retTp -- return value
            Ctx.::> BaseBoolType -- whether the program has returned
            Ctx.::> BaseNatType -- current block
        )
    )
makeTransitionSystem sym cfg namespacer globInfos blockInfos =
  do
    let initArgs = Core.cfgArgTypes cfg
    let initArgsNames = namesForContext functionArgumentName initArgs
    -- let retTp = regType retVal
    -- NOTE: the structure of the next two variables must match exactly the
    -- structure of the return type of this function
    let blocksInputs ::
          Ctx.Assignment (Ctx.Assignment TypeRepr) blocks =
            fmapFC Core.blockInputs (Core.cfgBlockMap cfg)
    let blocksIDs = fmapFC Core.blockID (Core.cfgBlockMap cfg)
    let blocksInputsNames ::
          Ctx.Assignment (Ctx.Assignment (Const String)) blocks =
            Ctx.zipWith
              (\blockID blockInputs -> namesForContext (blockArgumentName blockID) blockInputs)
              blocksIDs
              blocksInputs
    let stateFieldsRepr =
          ( (asBaseTypeReprs (flattenCtx blocksInputs))
              Ctx.<++> ( asBaseTypeReprs (globalTypeReprs globInfos)
                           Ctx.<++> asBaseTypeReprs initArgs
                       )
          )
            -- `Ctx.extend` asBaseTypeRepr retTp
            `Ctx.extend` BaseBoolRepr
            `Ctx.extend` BaseNatRepr
    let stateFieldsNames =
          ( asBaseTypeNames (flattenCtx blocksInputsNames)
              Ctx.<++> ( asBaseTypeNames (globalSymbolsAsStrings globInfos)
                           Ctx.<++> asBaseTypeNames initArgsNames
                       )
          )
            -- `Ctx.extend` Const returnValueVariable
            `Ctx.extend` Const hasReturnedVariable
            `Ctx.extend` Const currentBlockVariable
    currentBlock <- What4.freshConstant sym (userSymbol' currentBlockVariable) BaseNatRepr
    hasReturned <- What4.freshConstant sym (userSymbol' hasReturnedVariable) BaseBoolRepr
    return $
      TS.TransitionSystem
        { stateFieldsRepr,
          stateFieldsNames,
          initialStatePred = \_ -> makeInitialState cfg sym globInfos currentBlock hasReturned,
          stateTransitions = makeStateTransitions sym (namespacer stateFieldsRepr) stateFieldsRepr blockInfos globInfos,
          -- NOTE: putting the final query last because it's nicer in the output
          queries = makeQueries sym currentBlock hasReturned blockInfos
        }
