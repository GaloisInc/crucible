{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
module Print where

import Text.PrettyPrint
import Lang.Crucible.Simulator.ExecutionTree


ppExecState :: ExecState p sym ext rtp -> Doc
ppExecState st =
  case st of
    ResultState {} -> "ResultState"
    AbortState {}  -> "AbortState"
    UnwindCallState {} -> "UnwindCallState"
    CallState {} -> "CallState"
    TailCallState {} -> "TailCallState"
    ReturnState {} -> "ReturnState"
    RunningState {} -> "RunningState"
    SymbolicBranchState {} -> "SymbolicBranchState"
    ControlTransferState {} -> "ControlTransferState"
    OverrideState {} -> "OverrideState"
    BranchMergeState t _st -> "BranchMergeState" <+> text (ppBranchTarget t)
    InitialState {} -> "InitialState"





