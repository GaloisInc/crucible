{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Debug.Eval
  ( Ctxt.EvalResult(..)
  , eval
  ) where

import Control.Lens qualified as Lens
import Data.Maybe qualified as Maybe
import Data.Set qualified as Set
import Data.Text qualified as Text
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.CFG.Extension qualified as C
import Lang.Crucible.Debug.Arg qualified as Arg
import Lang.Crucible.Debug.Breakpoint (Breakpoint(BreakFunction))
import Lang.Crucible.Debug.Command.Base qualified as BCmd
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Commands qualified as Cmds
import Lang.Crucible.Debug.Context (Context)
import Lang.Crucible.Debug.Context qualified as Ctxt
import Lang.Crucible.Debug.Regex qualified as Rgx
import Lang.Crucible.Debug.Response qualified as Resp
import Lang.Crucible.Debug.Statement qualified as Stmt
import Lang.Crucible.Debug.Statement (Statement)
import Lang.Crucible.Debug.Trace qualified as Trace
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Syntax.Concrete qualified as C
import Prettyprinter qualified as PP
import What4.Expr.Builder qualified as W4
import What4.Interface qualified as W4

runCmd ::
  Context cExt p sym ext t ->
  C.ExecState p sym ext (C.RegEntry sym t) ->
  Ctxt.RunningState ->
  IO (Ctxt.EvalResult cExt p sym ext t)
runCmd ctx execState runState =
  case execState of
    C.ResultState {} ->
      let resp = Resp.UserError (Resp.NotApplicable Resp.DoneSimulating) in
      pure (def ctx) { Ctxt.evalResp = resp }
    _ -> pure (def ctx) { Ctxt.evalCtx = ctx { Ctxt.dbgState = Ctxt.Running runState  } }

-- | Helper, not exported
def :: Context cExt p sym ext t -> Ctxt.EvalResult cExt p sym ext t
def ctx = Ctxt.EvalResult ctx C.ExecutionFeatureNoChange Resp.Ok

baseImpl ::
  (sym ~ W4.ExprBuilder s st fs) =>
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  W4.IsExpr (W4.SymExpr sym) =>
  BCmd.BaseCommand ->
  Ctxt.CommandImpl cExt p sym ext t
baseImpl =
  \case
    BCmd.Backtrace ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rBacktrace
      , Ctxt.implBody = \ctx execState Rgx.MEmpty -> do
          resp <- Cmds.backtrace execState
          pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Block ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rBlock
      , Ctxt.implBody = \ctx execState Rgx.MEmpty -> do
          resp <- Cmds.block ctx execState
          pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Break ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rBreak
      , Ctxt.implBody = \ctx _execState (Rgx.MLit (Arg.AFunction fNm)) -> do
          let bs = Set.insert (BreakFunction fNm) (Ctxt.dbgBreakpoints ctx)
          pure (def ctx) { Ctxt.evalCtx = ctx { Ctxt.dbgBreakpoints = bs } }
      }

    BCmd.Call ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rCall
      , Ctxt.implBody = \ctx execState (Rgx.MLit (Arg.AFunction fNm)) -> do
          (featRes, resp) <- Cmds.call execState (Ctxt.dbgRetTy ctx) fNm
          pure (def ctx) { Ctxt.evalFeatureResult = featRes, Ctxt.evalResp = resp }
      }

    BCmd.Cfg ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rCfg
      , Ctxt.implBody = \ctx execState m ->
          case m of
            Rgx.MLeft Rgx.MEmpty -> do
              resp <- Cmds.cfg execState Nothing
              pure (def ctx) { Ctxt.evalResp = resp }
            Rgx.MRight (Rgx.MLit (Arg.AFunction fNm)) -> do
              (featRes, resp) <- Cmds.call execState (Ctxt.dbgRetTy ctx) fNm
              pure (def ctx) { Ctxt.evalFeatureResult = featRes, Ctxt.evalResp = resp }
      }

    BCmd.Clear ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rClear
      , Ctxt.implBody = \ctx execState Rgx.MEmpty ->
          C.withBackend (C.execStateContext execState) $ \bak -> do
            n <- length <$> C.getProofObligations bak
            C.clearProofObligations bak
            pure (def ctx) { Ctxt.evalResp = Resp.Clear n }
      }

    BCmd.Comment ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rComment
      , Ctxt.implBody = \ctx _execState (Rgx.MStar _) -> pure (def ctx)
      }

    BCmd.Delete ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rDelete
      , Ctxt.implBody = \ctx _execState (Rgx.MLit (Arg.ABreakpoint bp@(BreakFunction fNm))) -> do
          let bs0 = Ctxt.dbgBreakpoints ctx
          let wasElem = Set.member bp bs0
          let bs = Set.delete bp bs0
          pure (def ctx)
            { Ctxt.evalCtx = ctx { Ctxt.dbgBreakpoints = bs }
            , Ctxt.evalResp = Resp.Delete fNm wasElem
            }
      }

    BCmd.Done ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rDone
      , Ctxt.implBody = \ctx execState Rgx.MEmpty -> do
          case execState of
            C.ResultState {} ->
              pure (def ctx) { Ctxt.evalCtx = ctx { Ctxt.dbgState = Ctxt.Quit } }
            _ ->
              let resp = Resp.UserError (Resp.NotApplicable Resp.NotDone) in
              pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Frame ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rFrame
      , Ctxt.implBody = \ctx execState Rgx.MEmpty -> do
          resp <- Cmds.frame ctx execState
          pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Finish ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rFinish
      , Ctxt.implBody = \ctx execState Rgx.MEmpty ->
          runCmd ctx execState Ctxt.Finish
      }

    BCmd.Help ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rHelp
      , Ctxt.implBody = \ctx _execState m ->
        case m of
          Rgx.MLeft Rgx.MEmpty ->
            pure (def ctx) { Ctxt.evalResp = Cmds.help (Ctxt.dbgCommandExt ctx) Nothing }
          Rgx.MRight (Rgx.MLit (Arg.ACommand cmd)) ->
            pure (def ctx) { Ctxt.evalResp = Cmds.help (Ctxt.dbgCommandExt ctx) (Just cmd) }

      }

    BCmd.Load ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rLoad
      , Ctxt.implBody = \ctx execState (Rgx.MLit (Arg.APath path)) -> do
          (featRes, resp) <- Cmds.load execState (Text.unpack path)
          pure (def ctx) { Ctxt.evalFeatureResult = featRes, Ctxt.evalResp = resp }
      }

    BCmd.Location ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rLocation
      , Ctxt.implBody = \ctx execState Rgx.MEmpty -> do
          let stateCtx = C.execStateContext execState
          let sym = stateCtx Lens.^. C.ctxSymInterface
          loc <- W4.getCurrentProgramLoc sym
          pure (def ctx) { Ctxt.evalResp = Resp.Location loc }
      }

    BCmd.Obligation ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rObligation
      , Ctxt.implBody = \ctx execState Rgx.MEmpty ->
          C.withBackend (C.execStateContext execState) $ \bak -> do
          obls <- C.getProofObligations bak
          let goals = Maybe.fromMaybe [] (C.goalsToList <$> obls)
          let sym = C.backendGetSym bak
          prettyGoals <- mapM (C.ppProofObligation sym) goals
          pure (def ctx) { Ctxt.evalResp = Resp.Obligation prettyGoals }
      }

    BCmd.PathCondition ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rPathCondition
      , Ctxt.implBody = \ctx execState Rgx.MEmpty ->
          C.withBackend (C.execStateContext execState) $ \bak -> do
            pathCond <- W4.printSymExpr <$> C.getPathCondition bak
            pure (def ctx) { Ctxt.evalResp = Resp.PathCondition pathCond }
      }

    BCmd.Prove ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rProve
      , Ctxt.implBody = \ctx execState Rgx.MEmpty -> do
          resp <- C.withBackend (C.execStateContext execState) Cmds.prove
          pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Quit ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rQuit
      , Ctxt.implBody = \ctx _execState Rgx.MEmpty ->
          pure (def ctx) { Ctxt.evalCtx = ctx { Ctxt.dbgState = Ctxt.Quit } }
      }

    BCmd.Register ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rRegister
      , Ctxt.implBody = \ctx execState (Rgx.MStar ints) -> do
          let ints' = map (\(Rgx.MLit (Arg.AInt i)) -> i) ints
          resp <- Cmds.reg ctx execState ints'
          pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Run ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rRun
      , Ctxt.implBody = \ctx execState Rgx.MEmpty ->
          runCmd ctx execState Ctxt.Run
      }

    BCmd.Secret ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rSecret
      , Ctxt.implBody = \ctx execState m -> do
          resp <- Cmds.secret ctx execState m
          pure (def ctx) { Ctxt.evalResp = resp }
      }

    BCmd.Step ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rStep
      , Ctxt.implBody = \ctx execState Rgx.MEmpty ->
          runCmd ctx execState Ctxt.Step
      }

    BCmd.Source ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rSource
      , Ctxt.implBody = \ctx _execState (Rgx.MLit (Arg.APath path)) -> do
          r <- Cmds.source ctx (Text.unpack path)
          case r of
            Left ioErr -> pure (def ctx) { Ctxt.evalResp = Resp.IOError ioErr }
            Right inputs -> pure (def ctx) { Ctxt.evalCtx = ctx { Ctxt.dbgInputs = inputs } }
      }

    BCmd.Trace ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rTrace
      , Ctxt.implBody = \ctx _execState m -> do
          let n =
                case m of
                  Rgx.MLeft Rgx.MEmpty -> 2
                  Rgx.MRight (Rgx.MLit (Arg.AInt i)) -> i
          ents <- reverse <$> Trace.latest (Ctxt.dbgTrace ctx) n
          pure (def ctx) { Ctxt.evalResp = Resp.Trace (map PP.pretty ents) }
      }

    BCmd.Usage ->
      Ctxt.CommandImpl
      { Ctxt.implRegex = BCmd.rUsage
      , Ctxt.implBody = \ctx _execState (Rgx.MLit (Arg.ACommand cmd)) ->
          pure (def ctx) { Ctxt.evalResp = Resp.Usage (Cmds.usage (Ctxt.dbgCommandExt ctx) cmd) }
      }

cmdImpl ::
  (sym ~ W4.ExprBuilder s st fs) =>
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  W4.IsExpr (W4.SymExpr sym) =>
  Context cExt p sym ext t ->
  Cmd.Command cExt ->
  Ctxt.CommandImpl cExt p sym ext t
cmdImpl ctx cmd =
  case cmd of
    Cmd.Base bCmd -> baseImpl bCmd
    Cmd.Ext xCmd -> Ctxt.getExtImpl (Ctxt.dbgExtImpl ctx) xCmd

eval ::
  (sym ~ W4.ExprBuilder s st fs) =>
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  W4.IsExpr (W4.SymExpr sym) =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext (C.RegEntry sym t) ->
  Statement cExt ->
  IO (Ctxt.EvalResult cExt p sym ext t)
eval ctx execState stmt =
  let args = Stmt.stmtArgs stmt in
  let argError err = (def ctx) { Ctxt.evalResp = Resp.UserError (Resp.ArgError (Stmt.stmtCmd stmt) err) } in
  case cmdImpl ctx (Stmt.stmtCmd stmt) of
    Ctxt.CommandImpl { Ctxt.implRegex = r, Ctxt.implBody = f } ->
      case Arg.match (Arg.convert (Ctxt.dbgCommandExt ctx) r) args of
        Left e -> pure (argError e)
        Right m -> f ctx execState m
