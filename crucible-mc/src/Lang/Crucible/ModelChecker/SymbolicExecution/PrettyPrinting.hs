{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.SymbolicExecution.PrettyPrinting
-- Description      : Symbolic simulation of Crucible blocks to gather @BlockInfo@s
-- Copyright        : (c) Galois, Inc 2020-2022
-- License          : BSD3
-- Maintainer       : Valentin Robert <val@galois.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SymbolicExecution.PrettyPrinting
  ( ppExecState,
  )
where

import Control.Lens
import Data.Parameterized.TraversableFC
import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.Simulator.CallFrame
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.RegMap
import Prettyprinter
import What4.Interface
import Prelude hiding ((<>))

ppRegEntry ::
  IsSymExprBuilder sym =>
  RegEntry sym tp ->
  Doc ()
ppRegEntry RegEntry {..} =
  case regType of
    LLVMPointerRepr _ -> ppPtr regValue <+> ":" <+> pretty regType
    UnitRepr -> "()"
    _ -> error $ show regType

ppExecState ::
  IsSymExprBuilder sym =>
  ExecState p sym ext (RegEntry sym ret) ->
  Doc ()
ppExecState (ResultState (FinishedResult _ (TotalRes gp))) =
  vcat
    [ "---[ResultState, FinishedResult, TotalRes]",
      ppRegEntry (view gpValue gp)
    ]
ppExecState (ResultState (FinishedResult _ (PartialRes {}))) =
  vcat
    [ "---[ResultState, FinishedResult, PartialRes]"
    ]
ppExecState (ResultState (AbortedResult {})) = "---[ResultState, Aborted]"
ppExecState (ResultState (TimeoutResult {})) = "---[ResultState, Timeout]"
ppExecState (AbortState reason _) = vcat ["---[AbortState]", ppAbortExecReason reason]
ppExecState (UnwindCallState {}) = "---[UnwindCallState]"
ppExecState (CallState _ (CrucibleCall bID f) _) =
  vcat
    [ "---[CallState]",
      "The simulator is about to call within the Crucible function"
        <+> pretty (show $ frameHandle f)
        <+> "at block"
        <+> pretty bID,
      "The arguments are: " <+> vcat (toListFC ppRegEntry (regMap (view frameRegs f)))
    ]
ppExecState (CallState _ (OverrideCall _ f) _) =
  vcat
    [ "---[CallState]",
      "The simulator is about to call the override function"
        <+> pretty (show $ view overrideHandle f)
    ]
ppExecState (TailCallState {}) = "TailCallState"
ppExecState (ReturnState _ _ ret _) =
  vcat
    [ "ReturnState",
      ppRegEntry ret
    ]
ppExecState (RunningState (RunBlockStart bID) _) =
  vcat
    [ "---[RunningState]",
      "The simulator is now in a running state at the start of block" <+> pretty bID
    ]
ppExecState (RunningState (RunBlockEnd (Some bID)) _) =
  vcat
    [ "---[RunningState]",
      "The simulator is now in a running state at the end of block" <+> pretty bID
    ]
ppExecState (RunningState (RunReturnFrom name) _) =
  vcat
    [ "---[RunningState]",
      "The simulator is now in a running state because it returned from function" <+> pretty name
    ]
ppExecState (RunningState (RunPostBranchMerge bID) _) =
  vcat
    [ "---[RunningState]",
      "The simulator is now in a running state because it finished merging branches prior to the start of block" <+> pretty bID
    ]
ppExecState (SymbolicBranchState cond _true _false merge _) =
  vcat
    [ "---[SymbolicBranchState]",
      "The simulator is now branching based on condition" <+> printSymExpr cond,
      "The merge point for this branching is" <+> pretty (ppBranchTarget merge)
    ]
ppExecState (ControlTransferState (ContinueResumption (ResolvedJump bID args)) _st) =
  vcat
    [ "---[ControlTransferState]",
      "The simulator is about to resume execution at block" <+> pretty bID,
      "The arguments are: " <+> vcat (toListFC ppRegEntry (regMap args))
    ]
ppExecState (ControlTransferState (CheckMergeResumption (ResolvedJump bID args)) _st) =
  vcat
    [ "---[ControlTransferState]",
      "The simulator is about to merge execution into block" <+> pretty bID,
      "The arguments are: " <+> vcat (toListFC ppRegEntry (regMap args))
    ]
ppExecState (ControlTransferState (SwitchResumption bs) _st) =
  let f (p, ResolvedJump _bID args) =
        hsep
          [ printSymExpr p,
            vcat (toListFC ppRegEntry (regMap args))
          ]
   in vcat
        [ "The simulator is about to switch execution, where the pending branches are:",
          vcat $ map f bs
        ]
ppExecState (ControlTransferState (OverrideResumption _k args) _st) =
  vcat
    [ "The simulator is about to resume from an override execution, with arguments:",
      vcat . toListFC ppRegEntry $ regMap args
    ]
ppExecState (OverrideState {}) = "---[OverrideState]"
ppExecState (BranchMergeState t _) =
  vcat
    [ "---[BranchMergeState]",
      "The simulator is now checking for pending branches as it transfers control to"
        <+> pretty (ppBranchTarget t)
    ]
ppExecState (InitialState {}) = "---[InitialState]"

-- ppResolvedCall :: ResolvedCall p sym ext ret -> Doc ()
-- ppResolvedCall (OverrideCall _o f) =
--   let fnHandle = view overrideHandle f
--    in "Override" <+> pretty (show fnHandle)
-- ppResolvedCall (CrucibleCall _b f) =
--   let fnHandle = frameHandle f
--    in "Crucible" <+> pretty (show fnHandle)
