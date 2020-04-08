{-# Language GADTs #-}
{-# Language OverloadedStrings #-}

module Print where

import Text.PrettyPrint
import Lang.Crucible.Simulator.ExecutionTree


ppExecState :: ExecState p sym ext rtp -> Doc
ppExecState (ResultState          {})  = "ResultState"
ppExecState (AbortState           {})  = "AbortState"
ppExecState (UnwindCallState      {})  = "UnwindCallState"
ppExecState (CallState            {})  = "CallState"
ppExecState (TailCallState        {})  = "TailCallState"
ppExecState (ReturnState          {})  = "ReturnState"
ppExecState (RunningState         {})  = "RunningState"
ppExecState (SymbolicBranchState  {})  = "SymbolicBranchState"
ppExecState (ControlTransferState {})  = "ControlTransferState"
ppExecState (OverrideState        {})  = "OverrideState"
ppExecState (BranchMergeState     t _) = "BranchMergeState" <+> text (ppBranchTarget t)
ppExecState (InitialState         {})  = "InitialState"
