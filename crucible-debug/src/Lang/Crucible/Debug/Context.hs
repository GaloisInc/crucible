{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Debug.Context
  ( RunningState(..)
  , DebuggerState(..)
  , CommandImpl(..)
  , ExtImpl(..)
  , voidImpl
  , EvalResult(..)
  , Context(..)
  , initCtx
  , toCompletionEnv
  , toStyleEnv
  ) where

import Data.Parameterized.NatRepr (knownNat)
import Data.Set qualified as Set
import Data.Set (Set)
import Data.Void (Void, absurd)
import Lang.Crucible.Debug.Arg qualified as Arg
import Lang.Crucible.Debug.Arg.Type qualified as AType
import Lang.Crucible.Debug.Breakpoint (Breakpoint)
import Lang.Crucible.Debug.Command (CommandExt)
import Lang.Crucible.Debug.Complete (CompletionT, CompletionEnv)
import Lang.Crucible.Debug.Complete qualified as Complete
import Lang.Crucible.Debug.Inputs (Inputs)
import Lang.Crucible.Debug.Outputs (Outputs)
import Lang.Crucible.Debug.Regex qualified as Rgx
import Lang.Crucible.Debug.Response (Response)
import Lang.Crucible.Debug.Statement (Statement)
import Lang.Crucible.Debug.Style qualified as Style
import Lang.Crucible.Debug.Style (StyleT, StyleEnv)
import Lang.Crucible.Debug.Trace (Trace)
import Lang.Crucible.Debug.Trace qualified as Trace
import Lang.Crucible.Pretty (IntrinsicPrinters)
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Types (TypeRepr)
import What4.Interface qualified as W4

data RunningState
  = -- | User issued 'Cmd.Finish'
    Finish
    -- | User issued 'Cmd.Run'
  | Run
    -- | User issued 'Cmd.Step'
  | Step {-# UNPACK #-} !Int

data DebuggerState
  = Running RunningState
    -- | User issued 'Cmd.Quit'
  | Quit
  | Stopped

data CommandImpl cExt p sym ext t
  = forall r.
    CommandImpl
    { -- | A regular expression describing what kinds of arguments this command
      -- takes. See "Lang.Crucible.Debug.Regex".
      implRegex :: Rgx.RegexRepr AType.ArgTypeRepr r
      -- | The implementation of the command, taking the arguments that result
      -- from matching 'implRegex' against the command line provided by the
      -- user.
    , implBody ::
        Context cExt p sym ext t ->
        C.ExecState p sym ext (C.RegEntry sym t) ->
        Rgx.Match (Arg.Arg cExt) r ->
        IO (EvalResult cExt p sym ext t)
    }

newtype ExtImpl cExt p sym ext t
  = ExtImpl { getExtImpl :: cExt -> CommandImpl cExt p sym ext t }

voidImpl :: ExtImpl Void p sym ext t
voidImpl = ExtImpl absurd

-- | The result of evaluating a 'Statement'
data EvalResult cExt p sym ext t
  = EvalResult
  { evalCtx :: Context cExt p sym ext t
  , evalFeatureResult :: C.ExecutionFeatureResult p sym ext (C.RegEntry sym t)
  , evalResp :: Response cExt
  }

-- | Debugger state.
--
-- Type parameters:
--
-- * 'cExt' is the command extension type, see 'CommandExt'
-- * 'p', 'sym', 'ext' are as in @OverrideSim@
-- * 't' is the Crucible type of the @RegValue@ returned by the program
--
-- 'cExt' is different from 'ext' because it\'s not necessarily true that you
-- would want the debugger command extensions to be tied in a 1:1 fashion with
-- the syntax extension (source language).
data Context cExt p sym ext t
  = Context
  { dbgBreakpoints :: Set Breakpoint
  , dbgCommandExt :: CommandExt cExt
  , dbgExtImpl :: ExtImpl cExt p sym ext t
  , dbgInputs :: Inputs (CompletionT cExt (StyleT cExt IO)) (Statement cExt)
  , dbgOutputs :: Outputs IO (Response cExt)
  , dbgPpIntrinsic :: IntrinsicPrinters sym
  , dbgRetTy :: TypeRepr t
  , dbgState :: DebuggerState
  , dbgStopOnAbort :: Bool
  , dbgTrace :: Trace ext
  }

initCtx ::
  W4.IsExpr (W4.SymExpr sym) =>
  CommandExt cExt ->
  ExtImpl cExt p sym ext t ->
  IntrinsicPrinters sym ->
  Inputs (CompletionT cExt (StyleT cExt IO)) (Statement cExt) ->
  Outputs IO (Response cExt) ->
  TypeRepr t ->
  IO (Context cExt p sym ext t)
initCtx cExts impl iFns ins outs rTy = do
  t <- Trace.empty (knownNat @512)  -- arbitrary max size
  pure $
    Context
    { dbgBreakpoints = Set.empty
    , dbgCommandExt = cExts
    , dbgExtImpl = impl
    , dbgInputs = ins
    , dbgOutputs = outs
    , dbgPpIntrinsic = iFns
    , dbgRetTy = rTy
    , dbgState = Stopped
    , dbgStopOnAbort = False
    , dbgTrace = t
    }

toCompletionEnv ::
  Context cExt p sym ext t ->
  C.ExecState p sym ext r ->
  CompletionEnv cExt
toCompletionEnv ctxt execState =
  Complete.CompletionEnv
  { Complete.envBreakpoints = dbgBreakpoints ctxt
  , Complete.envCommandExt = dbgCommandExt ctxt
  , Complete.envState = execState
  }

toStyleEnv ::
  Context cExt p sym ext t ->
  C.ExecState p sym ext r ->
  StyleEnv cExt
toStyleEnv ctxt execState =
  Style.StyleEnv
  { Style.envBreakpoints = dbgBreakpoints ctxt
  , Style.envCommandExt = dbgCommandExt ctxt
  , Style.envState = execState
  }
