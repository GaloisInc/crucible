{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Debug.Override
  ( debuggerPrepend
  , debuggerQuit
  , debuggerStop
  , debugOverride
  , debugRunOverride
  ) where

import Control.Lens qualified as Lens
import Control.Monad.IO.Class (liftIO)
import Data.Text qualified as Text
import Data.Parameterized.Context qualified as Ctx
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Personality qualified as Pers
import Lang.Crucible.Debug.Personality (HasContext)
import Lang.Crucible.Debug.Statement (Statement)
import Lang.Crucible.Debug.Statement qualified as Stmt
import Lang.Crucible.Backend qualified as CB
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator.OverrideSim qualified as C
import Lang.Crucible.Simulator.RegValue qualified as C
import Lang.Crucible.Types qualified as CT
import What4.Interface qualified as WI

debuggerPrepend ::
  HasContext p cExt sym ext t =>
  [Statement cExt] ->
  C.OverrideSim p sym ext rtp args ret ()
debuggerPrepend stmts = do
  simCtx <- Lens.use C.stateContext
  simCtx' <- liftIO (Pers.prepend stmts simCtx)
  C.stateContext Lens..= simCtx'

debuggerQuit ::
  HasContext p cExt sym ext t =>
  C.OverrideSim p sym ext rtp args ret ()
debuggerQuit = C.stateContext Lens.%= Pers.quit
{-# INLINEABLE debuggerQuit #-}

debuggerStop ::
  HasContext p cExt sym ext t =>
  C.OverrideSim p sym ext rtp args ret ()
debuggerStop = C.stateContext Lens.%= Pers.stop
{-# INLINEABLE debuggerStop #-}

-- | An override that stops the debugger at this location
debugOverride ::
  HasContext p cExt sym ext t =>
  C.TypedOverride p sym ext Ctx.EmptyCtx CT.UnitType
debugOverride =
  C.TypedOverride
  { C.typedOverrideArgs = CT.knownRepr
  , C.typedOverrideRet = CT.knownRepr
  , C.typedOverrideHandler = \_args -> debuggerStop
  }

-- | An override that adds a command to the debugger
debugRunOverride ::
  WI.IsExpr (WI.SymExpr sym) =>
  WI.IsExprBuilder sym =>
  HasContext p cExt sym ext t =>
  Cmd.CommandExt cExt ->
  C.TypedOverride p sym ext (Ctx.EmptyCtx Ctx.::> CT.StringType CT.Unicode) CT.UnitType
debugRunOverride extImpl =
  C.TypedOverride
  { C.typedOverrideArgs = CT.knownRepr
  , C.typedOverrideRet = CT.knownRepr
  , C.typedOverrideHandler =
      \(Ctx.viewAssign -> Ctx.AssignExtend _ (C.RV s)) -> do
        sym <- C.getSymInterface
        case WI.asString s of
          Nothing ->
            CB.throwUnsupported sym "Must pass concrete string to @debug-run"
          Just (WI.UnicodeLiteral txt) -> do
            case Stmt.parse extImpl txt of
              Left err ->
                CB.throwUnsupported sym (Text.unpack (Stmt.renderParseError err))
              Right stmt -> debuggerPrepend [stmt]
  }
