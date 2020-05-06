{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module Lang.Crucible.ModelChecker.MCState
  ( BlockInformation (..),
    GlobalInfo (..),
    InitInfo (..),
    MCState (..),
    MCTransition (..),
    SomeBlock (..),
    checkAndRegisterInitialBlock,
    globalSymbols,
    globalTypeReprs,
    initTypeReprs,
    initSymbols,
    mcBlockEndAssumptions,
    mcBlockEndObligations,
    mcBlockStartAssumptions,
    mcBlockStartObligations,
    mcGlobals,
    mcInitialBlock,
    mcTransitions,
    registerConditionalTransition,
    registerUnconditionalTransition,
    setCurrentBlock,
    unsetCurrentBlock,
    mcBlocksInformation,
    withCurrentBlock,
    withInitialBlock,
  )
where

import qualified Control.Lens as L
import Control.Monad.State (MonadState, modify)
import Data.Functor.Const
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC
import GHC.Natural
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.Simulator
import Lang.Crucible.Types
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified What4.Interface as What4

-- | @GlobalInfo sym tp@ captures the information we collect about global
-- variables.  Currently we retain their name @Symbol@, their type @TypeRepr@,
-- and their initial value @RegValue@.
data GlobalInfo sym tp
  = GlobalInfo
      { globalSymbol :: String,
        globalTypeRepr :: TypeRepr tp,
        globalRegValue :: RegValue sym tp
      }

instance PP.Pretty (GlobalInfo sym tp) where
  pretty GlobalInfo {..} = PP.text (show globalSymbol) PP.<+> ":" PP.<+> PP.pretty globalTypeRepr PP.<+> ":=" PP.<+> "TODO"

globalSymbols :: Ctx.Assignment (GlobalInfo sym) ctx -> Ctx.Assignment (Const String) ctx
globalSymbols = fmapFC (Const . globalSymbol)

globalTypeReprs :: Ctx.Assignment (GlobalInfo sym) ctx -> Ctx.Assignment TypeRepr ctx
globalTypeReprs = fmapFC globalTypeRepr

-- globalRegValues :: Ctx.Assignment (GlobalInfo sym) ctx -> Ctx.Assignment (RegValue' sym) ctx
-- globalRegValues = fmapFC (RV . globalRegValue)

-- | @InitInfo@ is a convenience to carry information about the name and type of
-- variables in the initial context using only one assignment.
data InitInfo tp
  = InitInfo
      { initSymbol :: String,
        initTypeRepr :: TypeRepr tp
      }

initSymbols :: Ctx.Assignment InitInfo ctx -> Ctx.Assignment (Const String) ctx
initSymbols = fmapFC (Const . initSymbol)

initTypeReprs :: Ctx.Assignment InitInfo ctx -> Ctx.Assignment TypeRepr ctx
initTypeReprs = fmapFC initTypeRepr

data BlockInformation sym
  = BlockInformation
      { _mcBlockStartAssumptions :: [What4.Pred sym],
        _mcBlockStartObligations :: [What4.Pred sym],
        _mcBlockEndAssumptions :: [What4.Pred sym],
        _mcBlockEndObligations :: [What4.Pred sym]
      }

mcBlockStartAssumptions :: L.Lens' (BlockInformation sym) [What4.Pred sym]
mcBlockStartAssumptions = L.lens _mcBlockStartAssumptions (\c s -> c {_mcBlockStartAssumptions = s})

mcBlockEndAssumptions :: L.Lens' (BlockInformation sym) [What4.Pred sym]
mcBlockEndAssumptions = L.lens _mcBlockEndAssumptions (\c s -> c {_mcBlockEndAssumptions = s})

mcBlockStartObligations :: L.Lens' (BlockInformation sym) [What4.Pred sym]
mcBlockStartObligations = L.lens _mcBlockStartObligations (\c s -> c {_mcBlockStartObligations = s})

mcBlockEndObligations :: L.Lens' (BlockInformation sym) [What4.Pred sym]
mcBlockEndObligations = L.lens _mcBlockEndObligations (\c s -> c {_mcBlockEndObligations = s})

data MCTransition sym
  = MCTransition
      { _fromBlock :: Natural,
        _condition :: What4.Pred sym,
        _toBlock :: Natural
      }

data SomeBlock = forall blocks args. SomeBlock (Core.BlockID blocks args)

withSomeBlock ::
  SomeBlock ->
  (forall blocks args. Core.BlockID blocks args -> a) ->
  a
withSomeBlock (SomeBlock block) k = k block

data MCState sym
  = MCState
      { _mcBlocksInformation :: Map.Map Natural (BlockInformation sym),
        _mcCurrentBlock :: Maybe SomeBlock,
        _mcGlobals :: Maybe (Some (Ctx.Assignment (GlobalInfo sym))),
        _mcInitialBlock :: Maybe SomeBlock,
        -- | Lists all the instances of a transition from a given block to
        -- another block as part of the symbolic execution.
        _mcTransitions :: [MCTransition sym]
      }

mcBlocksInformation :: L.Lens' (MCState sym) (Map.Map Natural (BlockInformation sym))
mcBlocksInformation = L.lens _mcBlocksInformation (\c s -> c {_mcBlocksInformation = s})

mcGlobals :: L.Lens' (MCState sym) (Maybe (Some (Ctx.Assignment (GlobalInfo sym))))
mcGlobals = L.lens _mcGlobals (\c s -> c {_mcGlobals = s})

mcInitialBlock :: L.Lens' (MCState sym) (Maybe SomeBlock)
mcInitialBlock = L.lens _mcInitialBlock (\c s -> c {_mcInitialBlock = s})

mcTransitions :: L.Lens' (MCState sym) [MCTransition sym]
mcTransitions = L.lens _mcTransitions (\c s -> c {_mcTransitions = s})

registerConditionalTransition ::
  MonadState (MCState sym) m =>
  Natural ->
  What4.Pred sym ->
  Natural ->
  m ()
registerConditionalTransition _fromBlock _condition _toBlock =
  do
    let transition = MCTransition {_fromBlock, _condition, _toBlock}
    modify $ L.over mcTransitions (transition :)
    return ()

registerUnconditionalTransition ::
  What4.IsSymExprBuilder sym =>
  MonadState (MCState sym) m =>
  sym ->
  Natural ->
  Natural ->
  m ()
registerUnconditionalTransition sym fromBlock toBlock =
  registerConditionalTransition fromBlock (What4.truePred sym) toBlock

changeCurrentBlock :: Maybe (Core.BlockID blocks args) -> MCState sym -> MCState sym
changeCurrentBlock b s =
  s {_mcCurrentBlock = SomeBlock <$> b}

setCurrentBlock :: Core.BlockID blocks args -> MCState sym -> MCState sym
setCurrentBlock b = changeCurrentBlock (Just b)

unsetCurrentBlock :: MCState sym -> MCState sym
unsetCurrentBlock = changeCurrentBlock Nothing

withCurrentBlock ::
  MCState sym ->
  (forall blocks args. Core.BlockID blocks args -> a) ->
  Maybe a
withCurrentBlock (MCState {..}) k =
  case _mcCurrentBlock of
    Nothing -> Nothing
    Just b -> Just (withSomeBlock b k)

checkAndRegisterInitialBlock ::
  Core.BlockID blocks args ->
  MCState sym ->
  MCState sym
checkAndRegisterInitialBlock block s@(MCState {..}) =
  case _mcInitialBlock of
    Nothing -> s {_mcInitialBlock = Just (SomeBlock block)}
    Just _ -> s

withInitialBlock ::
  MCState sym ->
  (forall blocks args. Core.BlockID blocks args -> a) ->
  Maybe a
withInitialBlock (MCState {..}) k =
  case _mcInitialBlock of
    Nothing -> Nothing
    Just b -> Just (withSomeBlock b k)
