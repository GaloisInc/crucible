{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Lang.Crucible.Protobuf.Encodings.ExecState (
)
where

-- import Lang.Crucible.Simulator.ExecutionTree (ExecState (SymbolicBranchState), stateContext, actContext, SimContext, stateTree, stateLocation, withBackend)
-- import CrucibleProtobufTrace.ProtoDefs.OperationTrace (OperationTrace)
-- import qualified CrucibleProtobufTrace.ProtoDefs.OperationTrace as ProtoOT
-- import Data.ProtoLens (Message(defMessage))
-- import Data.ProtoLens.Prism
-- import Lang.Crucible.Simulator.ExecutionTree (ExecState (BranchMergeState))
-- import Lang.Crucible.Backend (IsSymBackend(getPathCondition, saveAssumptionState))
-- import CrucibleProtobufTrace.Encoding
-- import CrucibleProtobufTrace.What4Encodings (SymExprWrapper (SymExprWrapper), expr_id)
-- import What4.Expr (ExprBuilder)
-- import Lens.Micro ((^.), (.~), (&))
-- import Lang.Crucible.Protobuf.Encodings.Assumptions (encodeAssumptionState)
-- import Lang.Crucible.Protobuf.Encodings.Events (encodePathID)

-- instance (sym ~ (ExprBuilder s t st)) => ProtoEncoding (ExecState p sym ext retT) ProtoOT.TraceEvent where
--     encodeProto (SymbolicBranchState pred frame1 frame2 target sim_state) = do
--         assumption_state_pre <- (withBackend (sim_state ^. stateContext) saveAssumptionState)
--         path_id_pre <- encodePathID assumption_state_pre
--         _loc <- (encodeProto $ sim_state ^. stateLocation)
--         cond_enc <- (expr_id pred)
--         return $ defMessage
--             & ProtoOT.location .~ _loc
--             & ProtoOT.pathId .~ path_id_pre
--             & ProtoOT.maybe'pathSplit .~ _Just # (
--                 defMessage
--                     & ProtoOT.splitCondition .~ cond_enc
--             )



--     encodeProto (BranchMergeState target state) = do
--         assumption_state_pre <- (withBackend (sim_state ^. stateContext) saveAssumptionState)
--         path_id_pre <- encodePathID assumption_state_pre
--         _loc <- (encodeProto $ state ^. stateLocation)
--         return $ defMessage
--             & ProtoOT.location .~ _loc
--             & ProtoOT.pathId .~ path_id_pre
--             & ProtoOT.maybe'pathMerge .~ _Just # (
--                 defMessage
--                     & ProtoOT.newPathId .~ path_id_pre
--             )
--     encodeProto _ = error "encodeExecState: not an encodeable state"
