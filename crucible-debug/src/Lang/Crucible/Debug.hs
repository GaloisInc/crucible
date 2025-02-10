{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Debug
  ( debugger
  , bareDebuggerExt
  , bareDebugger
  , Inps.defaultDebuggerInputs
  , Outps.defaultDebuggerOutputs
  , Arg.Arg(..)
  , AType.ArgTypeRepr(..)
  , type AType.Breakpoint
  , type AType.Exactly
  , type AType.Function
  , type AType.Int
  , type AType.Path
  , type AType.Text
  , Cmd.Command(Base, Ext)
  , Cmd.CommandExt(..)
  , Cmd.voidExts
  , Cmds.execStateSimState
  , Ctxt.EvalResult(..)
  , Ctxt.Context(..)
  , Ctxt.CommandImpl(..)
  , Ctxt.ExtImpl(..)
  , Ctxt.voidImpl
  , Resp.Response(Ok, UserError, XResponse)
  , Resp.UserError(NotApplicable)
  , Resp.NotApplicable(DoneSimulating, NotYetSimulating)
  , Resp.ResponseExt
  , type Rgx.Regex
  , type Rgx.Empty
  , type Rgx.Lit
  , type (Rgx.:|)
  , type Rgx.Then
  , type Rgx.Star
  , Rgx.Match(..)
  , Rgx.RegexRepr(..)
  , Trace.Trace
  , Trace.TraceEntry(..)
  , Trace.latest
  , IntrinsicPrinters(..)
  ) where

import Control.Applicative qualified as Applicative
import Control.Lens qualified as Lens
import Control.Monad qualified as Monad
import Data.IORef qualified as IORef
import Data.Maybe qualified as Maybe
import Data.Parameterized.Map qualified as MapF
import Data.Parameterized.Nonce qualified as Nonce
import Data.Parameterized.Some (Some(Some))
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Void (Void)
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.Backend.Simple qualified as C
import Lang.Crucible.CFG.Extension qualified as C
import Lang.Crucible.Debug.Arg qualified as Arg
import Lang.Crucible.Debug.Arg.Type qualified as AType
import Lang.Crucible.Debug.Breakpoint qualified as Break
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Commands qualified as Cmds
import Lang.Crucible.Debug.Complete qualified as Complete
import Lang.Crucible.Debug.Complete (CompletionT)
import Lang.Crucible.Debug.Context (Context, DebuggerState)
import Lang.Crucible.Debug.Context qualified as Ctxt
import Lang.Crucible.Debug.Eval (EvalResult)
import Lang.Crucible.Debug.Eval qualified as Eval
import Lang.Crucible.Debug.Inputs (Inputs)
import Lang.Crucible.Debug.Inputs qualified as Inps
import Lang.Crucible.Debug.Outputs (Outputs)
import Lang.Crucible.Debug.Outputs qualified as Outps
import Lang.Crucible.Debug.Regex qualified as Rgx
import Lang.Crucible.Debug.Response qualified as Resp
import Lang.Crucible.Debug.Response (Response)
import Lang.Crucible.Debug.Statement (Statement)
import Lang.Crucible.Debug.Style qualified as Style
import Lang.Crucible.Debug.Style (StyleT)
import Lang.Crucible.Debug.Trace qualified as Trace
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Pretty (IntrinsicPrinters(..))
import Lang.Crucible.Simulator.CallFrame qualified as C
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Syntax.Concrete qualified as C
import Lang.Crucible.Types qualified as C
import Prettyprinter qualified as PP
import System.Exit qualified as Exit
import System.IO (stdout)
import What4.Expr qualified as W4
import What4.Interface qualified as W4

-- Useful for debugging
_printState :: C.ExecState p sym ext rtp -> Text
_printState =
  \case
    C.AbortState {} -> "AbortState"
    C.CallState {} -> "CallState"
    C.TailCallState {} -> "TailCallState"
    C.ReturnState {} -> "ReturnState"
    C.ResultState {} -> "ResultState"
    C.InitialState {} -> "InitialState"
    C.OverrideState {} -> "OverrideState"
    C.RunningState {} -> "RunningState"
    C.SymbolicBranchState {} -> "SymbolicBranchState"
    C.BranchMergeState {} -> "BranchMergeState"
    C.ControlTransferState {} -> "ControlTransferState"
    C.UnwindCallState {} -> "UnwindCallState"

stepState ::
  Context cExt p sym ext t ->
  C.ExecState p sym ext rtp ->
  IO DebuggerState
stepState ctx =
  \case
    C.AbortState {} ->
      if Ctxt.dbgStopOnAbort ctx
      then pure Ctxt.Stopped
      else pure initState
    C.CallState _retHandler frm _st -> do
      C.SomeHandle hdl <- pure (C.resolvedCallHandle frm)
      stepCall hdl
    C.TailCallState _vfv frm _st -> do
      C.SomeHandle hdl <- pure (C.resolvedCallHandle frm)
      stepCall hdl
    C.ReturnState _fnm _vfv _ret _st ->
      case initState of
        Ctxt.Running Ctxt.Finish -> pure Ctxt.Stopped
        _ -> pure initState
    C.RunningState (C.RunBlockEnd _) simState -> do
      let fr = simState Lens.^. C.stateCrucibleFrame
      C.CallFrame { C._frameCFG = cfg, C._frameBlockID = blkId } <- pure fr
      let ent = Trace.TraceEntry cfg blkId
      Trace.append (Ctxt.dbgTrace ctx) ent
      pure initState

    -- Nothing to do for these...
    C.InitialState {} -> pure initState
    C.OverrideState {} -> pure initState
    C.ResultState {} -> pure initState
    C.RunningState {} -> pure initState
    C.SymbolicBranchState {} -> pure initState

    -- These are mostly implementation details...
    C.BranchMergeState {} -> pure initState
    C.ControlTransferState {} -> pure initState
    C.UnwindCallState {} -> pure initState
  where
    initState = Ctxt.dbgState ctx

    stepCall :: C.FnHandle args ret ->  IO DebuggerState
    stepCall hdl = do
      let b = Break.BreakFunction (C.handleName hdl)
      if Set.member b (Ctxt.dbgBreakpoints ctx)
      then pure Ctxt.Stopped
      else pure initState

mergeResults ::
  C.ExecutionFeatureResult p sym ext ret ->
  C.ExecutionFeatureResult p sym ext ret ->
  C.ExecutionFeatureResult p sym ext ret
mergeResults old new =
  case old of
    C.ExecutionFeatureNoChange -> new
    _ ->
      case new of
        C.ExecutionFeatureNoChange -> old
        _ -> new

resultState ::
  C.ExecutionFeatureResult p sym ext ret ->
  Maybe (C.ExecState p sym ext ret)
resultState =
  \case
    C.ExecutionFeatureNoChange -> Nothing
    C.ExecutionFeatureModifiedState s -> Just s
    C.ExecutionFeatureNewState s -> Just s

stopped ::
  (sym ~ W4.ExprBuilder s st fs) =>
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  W4.IsExpr (W4.SymExpr sym) =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext (C.RegEntry sym t) ->
  IO (EvalResult cExt p sym ext t)
stopped ctx0 execState0 = go ctx0 execState0 C.ExecutionFeatureNoChange
  where
    go c0 s0 r = do
      let cEnv = Ctxt.toCompletionEnv c0 s0
      let sEnv = Ctxt.toStyleEnv c0 s0
      stmt <- Style.runStyleM sEnv (Complete.runCompletionM cEnv (Inps.recv (Ctxt.dbgInputs c0)))
      result0 <- Eval.eval c0 s0 stmt
      let featResult = mergeResults r (Eval.evalFeatureResult result0)
      let result = result0 { Eval.evalFeatureResult = featResult }
      let s = Maybe.fromMaybe s0 (resultState featResult)
      let c = Eval.evalCtx result
      Outps.send (Ctxt.dbgOutputs c) (Eval.evalResp result)
      case Ctxt.dbgState c of
        Ctxt.Quit -> pure result
        Ctxt.Running {} -> pure result
        Ctxt.Stopped -> go c s featResult

dispatch ::
  (sym ~ W4.ExprBuilder s st fs) =>
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  W4.IsExpr (W4.SymExpr sym) =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext (C.RegEntry sym t) ->
  IO (Context cExt p sym ext t, C.ExecutionFeatureResult p sym ext (C.RegEntry sym t))
dispatch ctx0 execState =
  case Ctxt.dbgState ctx0 of
    Ctxt.Quit ->
      pure (ctx0, C.ExecutionFeatureNoChange)
    Ctxt.Running {} | C.ResultState {} <- execState -> do
      let ctx = ctx0 { Ctxt.dbgState = Ctxt.Stopped }
      dispatch ctx execState
    Ctxt.Running (Ctxt.Step i) | i <= 1 -> do
      let ctx = ctx0 { Ctxt.dbgState = Ctxt.Stopped }
      dispatch ctx execState
    Ctxt.Running (Ctxt.Step i) -> do
      let ctx = ctx0 { Ctxt.dbgState = Ctxt.Running (Ctxt.Step (i - 1)) }
      state <- stepState ctx execState
      let ctx' = ctx0 { Ctxt.dbgState = state }
      pure (ctx', C.ExecutionFeatureNoChange)
    Ctxt.Running {} -> do
      state <- stepState ctx0 execState
      let ctx = ctx0 { Ctxt.dbgState = state }
      pure (ctx, C.ExecutionFeatureNoChange)
    Ctxt.Stopped -> do
      result <- stopped ctx0 execState
      pure (Eval.evalCtx result, Eval.evalFeatureResult result)

debugger ::
  (sym ~ W4.ExprBuilder s st fs) =>
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  W4.IsExpr (W4.SymExpr sym) =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  Cmd.CommandExt cExt ->
  Ctxt.ExtImpl cExt p sym ext t ->
  IntrinsicPrinters sym ->
  Inputs (CompletionT cExt (StyleT cExt IO)) (Statement cExt) ->
  Outputs IO (Response cExt) ->
  C.TypeRepr t ->
  IO (C.ExecutionFeature p sym ext (C.RegEntry sym t))
debugger cExt impl iFns ins outs rTy = do
  ctxRef <- IORef.newIORef =<< Ctxt.initCtx cExt impl iFns ins outs rTy
  pure $
    C.ExecutionFeature $ \execState -> do
      ctx0 <- IORef.readIORef ctxRef
      (ctx, featResult) <- dispatch ctx0 execState
      IORef.writeIORef ctxRef ctx
      pure featResult

-- | Like 'bareDebugger', but with a syntax extension
bareDebuggerExt ::
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  Cmd.CommandExt cExt ->
  (forall p sym t. C.IsSymInterface sym => Ctxt.ExtImpl cExt p sym ext t) ->
  (forall p sym. C.IsSymInterface sym => C.ExtensionImpl p sym ext) ->
  Inputs (CompletionT cExt (StyleT cExt IO)) (Statement cExt) ->
  Outputs IO (Response cExt) ->
  (Text -> IO ()) ->
  IO ()
bareDebuggerExt cExts cEval extImpl inps outps logger = do
  Some nonceGen <- Nonce.newIONonceGenerator
  ha <- C.newHandleAllocator
  sym <- W4.newExprBuilder W4.FloatIEEERepr W4.EmptyExprBuilderState nonceGen
  bak <- C.newSimpleBackend sym
  let retType = C.UnitRepr
  let fns = C.FnBindings C.emptyHandleMap
  let simCtx = C.initSimContext bak C.emptyIntrinsicTypes ha stdout fns extImpl ()
  let ov = C.runOverrideSim retType $ return ()
  let simSt  = C.InitialState simCtx C.emptyGlobals C.defaultAbortHandler retType ov
  dbgr <- do
    let iFns = IntrinsicPrinters MapF.empty
    debugger cExts cEval iFns inps outps retType
  Monad.void $ C.executeCrucible [dbgr] simSt
  C.getProofObligations bak >>= \case
    Nothing -> pure ()
    Just {} -> do
      logger "There were unhandled proof obligations! Try `prove` and `clear`."
      Exit.exitFailure

-- | Start a debugger instance in an empty Crucible program.
--
-- The Crucible program simply returns the unit value. The idea is to use the
-- @Load@ and @Call@ commands to actually run some Crucible CFG(s).
--
-- Proves obligations using Z3.
bareDebugger ::
  Inputs (CompletionT Void (StyleT Void IO)) (Statement Void) ->
  Outputs IO (Response Void) ->
  (Text -> IO ()) ->
  IO ()
bareDebugger inps outps logger =
  let ?parserHooks = C.ParserHooks Applicative.empty Applicative.empty in
  bareDebuggerExt
    Cmd.voidExts
    Ctxt.voidImpl
    C.emptyExtensionImpl
    inps
    outps
    logger
