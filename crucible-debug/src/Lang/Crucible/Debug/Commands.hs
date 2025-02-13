{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Debug.Commands
  ( execStateSimState
  , backtrace
  , block
  , call
  , cfg
  , frame
  , help
  , load
  , prove
  , reg
  , secret
  , source
  , usage
  ) where

import Control.Exception qualified as X
import Control.Lens qualified as Lens
import Control.Monad.Except (runExceptT)
import Control.Monad.IO.Class (liftIO)
import Data.Kind (Type)
import Data.List qualified as List
import Data.Maybe qualified as Maybe
import Data.Parameterized.Classes (ixF')
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Nonce qualified as Nonce
import Data.Parameterized.Some (Some(Some), viewSome)
import Data.Parameterized.TraversableFC (toListFC)
import Data.Sequence qualified as Seq
import Data.Text.IO qualified as IO
import Data.Text qualified as Text
import Lang.Crucible.Analysis.Postdom qualified as C
import Lang.Crucible.Backend.Prove qualified as Prove
import Lang.Crucible.Backend qualified as C
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.CFG.Extension qualified as C
import Lang.Crucible.CFG.Reg qualified as C.Reg
import Lang.Crucible.CFG.SSAConversion qualified as C
import Lang.Crucible.Debug.Arg qualified as Arg
import Lang.Crucible.Debug.Command.Base qualified as BCmd
import Lang.Crucible.Debug.Command qualified as Cmd
import Lang.Crucible.Debug.Complete (CompletionT)
import Lang.Crucible.Debug.Complete qualified as Complete
import Lang.Crucible.Debug.Context (Context)
import Lang.Crucible.Debug.Context qualified as Ctxt
import Lang.Crucible.Debug.Inputs (Inputs)
import Lang.Crucible.Debug.Inputs qualified as Inps
import Lang.Crucible.Debug.Outputs qualified as Outps
import Lang.Crucible.Debug.Regex qualified as Rgx
import Lang.Crucible.Debug.Response qualified as Resp
import Lang.Crucible.Debug.Response (Response)
import Lang.Crucible.Debug.Statement qualified as Stmt
import Lang.Crucible.Debug.Statement (Statement)
import Lang.Crucible.Debug.Style qualified as Style
import Lang.Crucible.Debug.Style (StyleT)
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Pretty (ppRegVal)
import Lang.Crucible.Simulator.CallFrame qualified as C
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Syntax.Atoms qualified as C
import Lang.Crucible.Syntax.Concrete qualified as C
import Lang.Crucible.Syntax.SExpr qualified as C
import Lang.Crucible.Utils.Seconds qualified as Sec
import Lang.Crucible.Utils.Timeout qualified as CTO
import Prettyprinter qualified as PP
import System.Exit qualified as Exit
import Text.Megaparsec qualified as MP
import What4.Config qualified as W4
import What4.Expr.Builder qualified as W4
import What4.FunctionName qualified as W4
import What4.Interface qualified as W4
import What4.ProgramLoc qualified as W4
import What4.Solver qualified as W4

---------------------------------------------------------------------
-- Helpers, exported

execStateSimState ::
  C.ExecState p sym ext r ->
  Either Resp.NotApplicable (C.SomeSimState p sym ext r)
execStateSimState =
  \case
    C.ResultState _                  -> Left Resp.DoneSimulating
    C.AbortState _ st                -> Right (C.SomeSimState st)
    C.UnwindCallState _ _ st         -> Right (C.SomeSimState st)
    C.CallState _ _ st               -> Right (C.SomeSimState st)
    C.TailCallState _ _ st           -> Right (C.SomeSimState st)
    C.ReturnState _ _ _ st           -> Right (C.SomeSimState st)
    C.ControlTransferState _ st      -> Right (C.SomeSimState st)
    C.RunningState _ st              -> Right (C.SomeSimState st)
    C.SymbolicBranchState _ _ _ _ st -> Right (C.SomeSimState st)
    C.OverrideState _ st             -> Right (C.SomeSimState st)
    C.BranchMergeState _ st          -> Right (C.SomeSimState st)
    C.InitialState _ _ _ _ _         -> Left Resp.NotYetSimulating

---------------------------------------------------------------------
-- Helpers, not exported

insertCfg ::
  C.IsSyntaxExtension ext =>
  C.Reg.CFG ext blocks init ret ->
  C.FnHandleMap (C.FnState p sym ext) ->
  C.FnHandleMap (C.FnState p sym ext)
insertCfg regCFG hdlMap =
  case C.toSSA regCFG of
    C.SomeCFG ssaCFG ->
      C.insertHandleMap
        (C.cfgHandle ssaCFG)
        (C.UseCFG ssaCFG (C.postdomInfo ssaCFG))
        hdlMap

type SomeFn :: (Ctx.Ctx C.CrucibleType -> C.CrucibleType -> Type) -> Type
data SomeFn f = forall args ret. SomeFn (f args ret)

lookupHandleMapByName ::
  W4.FunctionName ->
  C.FnHandleMap f ->
  Maybe (SomeFn f)
lookupHandleMapByName fNm hdls = do
  let sHdls = C.handleMapToHandles hdls
  C.SomeHandle h <- List.find (\(C.SomeHandle hdl) -> C.handleName hdl == fNm) sHdls
  SomeFn <$> C.lookupHandleMap h hdls

-- TODO: Upstream to Crucible as a Lens
modifySimContext ::
  (C.SimContext p sym ext -> C.SimContext p sym ext) ->
  C.ExecState p sym ext r ->
  C.ExecState p sym ext r
modifySimContext f =
  \case
    C.ResultState r ->
      case r of
        C.FinishedResult ctx x -> C.ResultState (C.FinishedResult (f ctx) x)
        C.AbortedResult ctx x -> C.ResultState (C.AbortedResult (f ctx) x)
        C.TimeoutResult es -> modifySimContext f es
    C.AbortState x s -> C.AbortState x (s Lens.& C.stateContext Lens.%~ f)
    C.UnwindCallState x y s -> C.UnwindCallState x y (s Lens.& C.stateContext Lens.%~ f)
    C.CallState x y s -> C.CallState x y (s Lens.& C.stateContext Lens.%~ f)
    C.TailCallState x y s -> C.TailCallState x y (s Lens.& C.stateContext Lens.%~ f)
    C.ReturnState x y z s -> C.ReturnState x y z (s Lens.& C.stateContext Lens.%~ f)
    C.ControlTransferState x s -> C.ControlTransferState x (s Lens.& C.stateContext Lens.%~ f)
    C.RunningState x s -> C.RunningState x (s Lens.& C.stateContext Lens.%~ f)
    C.SymbolicBranchState x y z w s -> C.SymbolicBranchState x y z w (s Lens.& C.stateContext Lens.%~ f)
    C.OverrideState x s -> C.OverrideState x (s Lens.& C.stateContext Lens.%~ f)
    C.BranchMergeState x s -> C.BranchMergeState x (s Lens.& C.stateContext Lens.%~ f)
    C.InitialState ctx x y z w -> C.InitialState (f ctx) x y z w

---------------------------------------------------------------------
-- Commands, exported

backtrace ::
  C.ExecState p sym ext r ->
  IO (Response cExt)
backtrace execState =
  case execStateSimState execState of
    Left notApplicable -> pure (Resp.UserError (Resp.NotApplicable notApplicable))
    Right (C.SomeSimState simState) -> do
      let frames = C.activeFrames (C._stateTree simState)
      pure (Resp.Backtrace (C.ppExceptionContext frames))

block ::
  C.IsSyntaxExtension ext =>
  W4.IsExpr (W4.SymExpr sym) =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext r ->
  IO (Response cExt)
block _ctx execState =
  case execStateSimState execState of
    Left notApplicable -> pure (Resp.UserError (Resp.NotApplicable notApplicable))
    Right (C.SomeSimState simState) ->
      let fr = simState Lens.^. C.stateTree . C.actFrame . C.gpValue in
      case fr of
        C.MF callFrame ->
          let regs = C.regMap (callFrame Lens.^. C.frameRegs) in
          pure (Resp.Block (ppStmtSeq False (Ctx.size regs) (C._frameStmts callFrame)))
        C.OF {} -> pure (Resp.UserError (Resp.NotApplicable Resp.NoCfg))
        C.RF {} -> pure (Resp.UserError (Resp.NotApplicable Resp.NoCfg))
  where
    -- TODO: The below is taken from Crucible. Export?

    prefixLineNum :: Bool -> W4.ProgramLoc -> PP.Doc ann -> PP.Doc ann
    prefixLineNum True pl d = PP.vcat ["%" PP.<+> W4.ppNoFileName (W4.plSourceLoc pl), d]
    prefixLineNum False _ d = d

    ppStmtSeq :: C.PrettyExt ext => Bool -> Ctx.Size ctx -> C.StmtSeq ext blocks ret ctx -> PP.Doc ann
    ppStmtSeq ppLineNum h (C.ConsStmt pl s r) =
      PP.vcat
      [ prefixLineNum ppLineNum pl (C.ppStmt h s)
      , ppStmtSeq ppLineNum (C.nextStmtHeight h s) r
      ]
    ppStmtSeq ppLineNum _ (C.TermStmt pl s) =
      prefixLineNum ppLineNum pl (PP.pretty s)

call ::
  C.IsSymInterface sym =>
  C.IsSyntaxExtension ext =>
  C.ExecState p sym ext (C.RegEntry sym t) ->
  C.TypeRepr t ->
  W4.FunctionName ->
  IO (C.ExecutionFeatureResult p sym ext (C.RegEntry sym t), Response cExt)
call execState rTy fNm = do
  let fTy = C.FunctionHandleRepr Ctx.empty C.UnitRepr
  let binds = execState Lens.^. Lens.to C.execStateContext . C.functionBindings
  case C.searchHandleMap fNm fTy (C.fnBindings binds) of
    Nothing -> do
      let hdls = C.handleMapToHandles (C.fnBindings binds)
      let names = map (\(C.SomeHandle hdl) -> C.handleName hdl) hdls
      pure (C.ExecutionFeatureNoChange, Resp.UserError (Resp.FnNotFound fNm names))
    Just (hdl, bind) -> do
      case execStateSimState execState of
        Left notApplicable -> pure (C.ExecutionFeatureNoChange, Resp.UserError (Resp.NotApplicable notApplicable))
        Right (C.SomeSimState simState) -> do
          let initCtx = simState Lens.^. C.stateContext
          let globs = simState Lens.^. C.stateGlobals
          let abortHdl = simState Lens.^. C.abortHandler
          let initState =
                C.InitialState initCtx globs abortHdl rTy $
                  C.runOverrideSim rTy $
                    let args = C.RegMap Ctx.empty in
                    case bind of
                      C.UseOverride o -> do
                        _ <- C.callOverride hdl o args
                        C.exitExecution Exit.ExitSuccess
                      C.UseCFG c _ -> do
                        _ <- C.callCFG c args
                        C.exitExecution Exit.ExitSuccess
          let featRes = C.ExecutionFeatureNewState initState
          pure (featRes, Resp.Ok)

cfg ::
  C.IsSyntaxExtension ext =>
  C.ExecState p sym ext r ->
  Maybe W4.FunctionName ->
  IO (Response cExt)
cfg execState =
  \case
    Just fNm -> do
      let binds = execState Lens.^. Lens.to C.execStateContext . C.functionBindings
      let hdls = C.handleMapToHandles (C.fnBindings binds)
      let names = map (\(C.SomeHandle hdl) -> C.handleName hdl) hdls
      case lookupHandleMapByName fNm (C.fnBindings binds) of
        Nothing -> pure (Resp.UserError (Resp.FnNotFound fNm names))
        Just (SomeFn (C.UseOverride {})) -> pure (Resp.UserError (Resp.NotACfg fNm))
        Just (SomeFn (C.UseCFG c _)) -> pure (Resp.Cfg (C.ppCFG True c))
    Nothing ->
      case execStateSimState execState of
        Left notApplicable -> pure (Resp.UserError (Resp.NotApplicable notApplicable))
        Right (C.SomeSimState simState) -> do
          case simState Lens.^. C.stateTree . C.actFrame . C.gpValue of
            C.MF (C.CallFrame { C._frameCFG = c }) ->
              pure (Resp.Cfg (C.ppCFG True c))
            C.OF {} -> pure (Resp.UserError (Resp.NotApplicable Resp.NoCfg))
            C.RF {} -> pure (Resp.UserError (Resp.NotApplicable Resp.NoCfg))

frame ::
  C.IsSyntaxExtension ext =>
  W4.IsExpr (W4.SymExpr sym) =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext r ->
  IO (Response cExt)
frame _ctx execState =
  case execStateSimState execState of
    Left notApplicable -> pure (Resp.UserError (Resp.NotApplicable notApplicable))
    Right (C.SomeSimState simState) ->
      pure $ Resp.Frame $
        let fr = simState Lens.^. C.stateTree . C.actFrame . C.gpValue in
        let name = fr Lens.^. C.frameFunctionName in
        case fr of
          C.OF ovFrame ->
            let regs = C.regMap (ovFrame Lens.^. C.overrideRegMap) in
            PP.vcat
            [ "Override:" PP.<+> PP.pretty name
            , ""
            , "Argument types:"
            , PP.vcat $ toListFC (bullet . PP.pretty . C.regType) regs
            ]
          C.MF callFrame ->
            let regs = C.regMap (callFrame Lens.^. C.frameRegs) in
            PP.vcat
              [ "CFG:" PP.<+> PP.pretty name
              , "Block:" PP.<+> viewSome PP.pretty (C._frameBlockID callFrame)
              , ""
              , "Argument types:"
              , PP.vcat $ toListFC (bullet . PP.pretty . C.regType) regs
              ]
          C.RF {} -> "Return:" PP.<+> PP.pretty name
  where bullet = ("-" PP.<+>) . PP.align

help ::
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  PP.Pretty cExt =>
  Cmd.CommandExt cExt ->
  Maybe (Cmd.Command cExt) ->
  Response cExt
help cExts =
  \case
    Nothing ->
      let mkHelp c = Cmd.name cExts c <> " (" <> Cmd.abbrev cExts c <> ")" <> ": " <> Cmd.help cExts c in
      Resp.Help (PP.pretty (Text.unlines (List.sort (map mkHelp (Cmd.allCmds cExts)))))
    Just cmd -> 
      Resp.Help $
        -- See 'Lang.Crucible.Debug.Command.ext{Detail,Help}' for expectations
        -- on these strings, which are why it makes sense to format them this
        -- way (e.g., adding a period, printing "details" after "help"), etc.
        let basic = [usage cExts cmd, "", PP.pretty (Cmd.help cExts cmd) <> "."]
            detail =
              case Cmd.detail cExts cmd of
                Just more -> ["", PP.pretty more]
                Nothing -> []
        in PP.vcat (basic ++ detail)

load ::
  C.IsSyntaxExtension ext =>
  (?parserHooks :: C.ParserHooks ext) =>
  C.ExecState p sym ext r ->
  FilePath ->
  IO (C.ExecutionFeatureResult p sym ext r, Response cExt)
load execState0 path = do
  eTxt <- X.try (IO.readFile path)
  case eTxt of
    Left ioErr -> pure (C.ExecutionFeatureNoChange, Resp.IOError ioErr)
    Right txt -> do
      case MP.parse (C.skipWhitespace *> MP.many (C.sexp C.atom) <* MP.eof) path txt of
        Left err -> pure (C.ExecutionFeatureNoChange, Resp.UserError (Resp.LoadParseError err))
        Right v ->
          Nonce.withIONonceGenerator $ \ng -> do
            let execCtx = C.execStateContext execState0
            let ha = C.simHandleAllocator execCtx
            parseResult <- C.top ng ha [] $ C.prog v
            case parseResult of
              Left err ->
                pure (C.ExecutionFeatureNoChange, Resp.UserError (Resp.LoadSyntaxError (PP.pretty err)))
              Right (C.ParsedProgram{ C.parsedProgCFGs = cfgs }) -> do
                let binds = execState0 Lens.^. Lens.to C.execStateContext . C.functionBindings . Lens.to C.fnBindings
                let binds' = foldl (\bs (C.Reg.AnyCFG c) -> insertCfg c bs) binds cfgs
                let execState = modifySimContext (\c -> c Lens.& C.functionBindings Lens..~ C.FnBindings binds') execState0
                let featRes = C.ExecutionFeatureModifiedState execState
                pure (featRes, Resp.Load path (length cfgs))

prove ::
  (sym ~ W4.ExprBuilder t st fs) =>
  C.IsSymBackend sym bak =>
  bak ->
  IO (Response cExt)
prove bak = do
  let sym = C.backendGetSym bak
  -- TODO(#270?): Configurable timeout
  let timeout = CTO.Timeout (Sec.secondsFromInt 5)
  -- TODO(#266): Configurable prover
  W4.extendConfig W4.z3Options (W4.getConfiguration sym)
  let prover = Prove.offlineProver timeout sym W4.defaultLogData W4.z3Adapter
  let strat = Prove.ProofStrategy prover Prove.keepGoing
  let convertResult =
        \case
          Prove.Proved {} -> Resp.Proved
          Prove.Disproved {} -> Resp.Disproved
          Prove.Unknown {} -> Resp.Unknown
  let printer = Prove.ProofConsumer $ \goal res -> do
        doc <- C.ppProofObligation sym goal
        pure (Seq.fromList [(doc, convertResult res)])
  runExceptT (Prove.proveCurrentObligations bak strat printer) >>=
    \case
      Left CTO.TimedOut -> pure Resp.ProveTimeout
      Right results -> pure (Resp.Prove results)

-- TODO: Support taking a function or block name
reg ::
  forall p sym ext r t cExt.
  W4.IsExpr (W4.SymExpr sym) =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext r ->
  [Int] ->
  IO (Response cExt)
reg ctx execState idxs =
  case execStateSimState execState of
    Left notApplicable -> pure (Resp.UserError (Resp.NotApplicable notApplicable))
    Right (C.SomeSimState simState) -> do
      let fr = simState Lens.^. C.stateTree . C.actFrame . C.gpValue
      let regs :: Maybe (C.Some (C.RegMap sym))
          regs =
            case fr of
              C.OF ovFrame ->
                Just (C.Some (ovFrame Lens.^. C.overrideRegMap))
              C.MF callFrame ->
                Just (C.Some (callFrame Lens.^. C.frameRegs))
              C.RF {} ->
                Nothing
      case regs of
        Nothing -> pure (Resp.UserError (Resp.NotApplicable Resp.NoFrame))
        Just (C.Some (C.RegMap rs)) -> do
          let sz = Ctx.size rs
          let mIdxs =
                if List.null idxs
                then Right (toListFC Some (Ctx.generate sz id))  -- all indices
                else traverse (\i -> maybeToEither i (Ctx.intIndex i sz)) idxs
          let ppArg (C.Some idx) =
                let C.RegEntry ty val = rs Lens.^. ixF' idx in
                ppRegVal (Ctxt.dbgPpIntrinsic ctx) ty (C.RV val)
          case mIdxs of
            Left i -> pure (Resp.UserError (Resp.NoSuchArgument i))
            Right idxs' -> pure (Resp.Arg (PP.vcat (List.map ppArg idxs')))
  where
    maybeToEither :: e -> Maybe a -> Either e a
    maybeToEither e =
      \case
        Nothing -> Left e
        Just a -> Right a

secret ::
  PP.Pretty cExt =>
  Context cExt p sym ext t ->
  C.ExecState p sym ext r ->
  Rgx.Match (Arg.Arg cExt) BCmd.SecretRegex ->
  IO (Resp.Response cExt)
secret ctx execState m =
  let cExt = Ctxt.dbgCommandExt ctx in
  case m of
    -- Show what sort of tab-completion should be provided by the UI
    Rgx.MLeft (Rgx.MThen _complete (Rgx.MThen (Rgx.MLit (Arg.ACommand cmd)) (Rgx.MStar args0))) -> do
      let args = map (\(Rgx.MLit (Arg.AText t)) -> Text.unpack t) args0
      let cEnv = Ctxt.toCompletionEnv ctx execState
      let line = unwords (show (PP.pretty cmd) : map (filter (/= '_')) args)
      -- Act like we are completing as if the user pressed TAB at the "_"
      let cursor = Maybe.fromMaybe "_" (List.find ("_" `List.isSuffixOf`) args)
      completions <- Complete.complete cEnv line (List.init cursor)
      pure $
        Resp.Complete $
          case completions of
            [] -> "No completions"
            _ -> PP.vcat (List.map PP.pretty completions)
    -- Show what sort of syntax-highlighting should be provided by the UI
    Rgx.MRight (Rgx.MThen _secret (Rgx.MThen (Rgx.MLit (Arg.ACommand cmd)) (Rgx.MStar args0))) ->
      let args = map (\(Rgx.MLit (Arg.AText t)) -> t) args0 in
      case Cmd.regex cExt cmd of
        Some rx ->
          let sEnv = Ctxt.toStyleEnv ctx execState in
          pure (Resp.Style (Style.runStyle sEnv (Style.style rx args)))

source ::
  Context cExt p sym ext t ->
  FilePath ->
  IO (Either X.IOException (Inputs (CompletionT cExt (StyleT cExt IO)) (Statement cExt)))
source ctx path = do
  let cExt = Ctxt.dbgCommandExt ctx
  eTxt <- liftIO (X.try (IO.readFile path))
  case eTxt of
    Left ioErr -> pure (Left ioErr)
    Right txt -> do
      let lns = Text.lines txt
      let cmds = traverse (Stmt.parse cExt) lns
      case cmds of
        Left err -> do
          Outps.send (Ctxt.dbgOutputs ctx) (Resp.UserError (Resp.SourceParseError err))
          pure (Right (Ctxt.dbgInputs ctx))
        Right stmts -> Right <$> Inps.prepend stmts (Ctxt.dbgInputs ctx)

usage ::
  PP.Pretty cExt =>
  Cmd.CommandExt cExt ->
  Cmd.Command cExt ->
  PP.Doc ann
usage cExt cmd =
  case Cmd.regex cExt cmd of
    Some rx -> PP.vcat (map (PP.pretty cmd PP.<+>) (Arg.usage rx))
