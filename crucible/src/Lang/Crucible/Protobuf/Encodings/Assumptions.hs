{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Lang.Crucible.Protobuf.Encodings.Assumptions (
      encodeAssumptionState
    , encodeAssumptions
    , encodeFrameIdentifier
)
where

import qualified CrucibleProtobufTrace.ProtoDefs.Assumptions as ProtoA
import qualified CrucibleProtobufTrace.ProtoDefs.OperationTrace as ProtoOT
import Lang.Crucible.Backend (Assumptions, IsSymBackend, Assumption, CrucibleAssumption (..), CrucibleEvent (..), AssumptionState, CrucibleAssumptions (SingleAssumption, ManyAssumptions, SingleEvent, MergeAssumptions), Assertion, assumptionPred)
import CrucibleProtobufTrace.What4Encodings
import Data.ProtoLens (Message(defMessage))

import Control.Lens
import What4.Expr (ExprBuilder, Expr)
import What4.Interface (asConstantPred)
import Data.Text (pack)
import What4.Expr.Builder (SymExpr)
import Lang.Crucible.Backend.ProofGoals (traverseGoals, traverseGoalCollector, gcFinish, gcFrames, FrameIdentifier (FrameIdentifier))
import Lang.Crucible.Backend.AssumptionStack
import Data.Foldable (fold, Foldable (toList))

encodeAssumption :: (sym ~ ExprBuilder s t st) => Assumption sym -> IO ProtoA.Assumption
encodeAssumption (GenericAssumption loc msg expr) = do
    id' <- expr_id expr
    loc' <- (encodeProto loc)
    let msg':: ProtoA.AssumptionKind_Generic
        msg' = defMessage
                    & ProtoA.location .~ loc'
                    & ProtoA.message .~ (pack msg)

    let res = defMessage
                & ProtoA.assumedExpr .~ id'
                & ProtoA.maybe'generic .~ _Just # msg'

    return res

encodeAssumption (BranchCondition loc tgt expr) = do
    id' <- expr_id expr
    loc' <- (encodeProto loc)
    tgt' <- (encodeProto tgt)
    let msg':: ProtoA.AssumptionKind_BranchCondition
        msg' = defMessage
                    & ProtoA.location .~ loc'
                    & ProtoA.branchTarget .~ tgt'

    let res = defMessage
                & ProtoA.assumedExpr .~ id'
                & ProtoA.maybe'branchCondition .~ _Just # msg'

    return res

encodeAssumption (AssumingNoError err_desc expr) = do
    id' <- expr_id expr
    let errmsg = show err_desc
    let msg':: ProtoA.AssumptionKind_SimulatorAssumingNoError
        msg' = defMessage
                    & ProtoA.reason .~ (pack errmsg)

    let res = defMessage
                & ProtoA.assumedExpr .~ id'
                & ProtoA.maybe'simulatorAssumingNoError .~ _Just # msg'

    return res

encodeAssumptions :: (sym ~ (ExprBuilder s t st)) => Assumptions sym -> IO ProtoA.Assumptions
encodeAssumptions (SingleAssumption ass) = do
    ass' <- encodeAssumption ass
    return
        $ defMessage
            & ProtoA.maybe'singleAssumption .~ _Just # ass'

encodeAssumptions (ManyAssumptions assumptionsSeq) = do
    ass' <-
        foldl
            (\xs y -> do
                xs' <- xs
                y' <- encodeAssumptions y
                return $ case y of
                    SingleAssumption ass -> case asConstantPred $ assumptionPred ass of
                        Just true -> xs'
                        _ -> y':xs'
                    MergeAssumptions _ _ _ -> y':xs'

                    ManyAssumptions Empty -> xs'
                    ManyAssumptions _ -> y':xs'
                    SingleEvent _ -> xs'
            )
            (return [])
            assumptionsSeq
    return
        $ defMessage
            & ProtoA.maybe'manyAssumptions .~ _Just # (defMessage & ProtoA.assumptions .~ ass')

encodeAssumptions (SingleEvent ev) = do
    ev' <- encodeCrucibleEvent ev
    return $ defMessage
                -- & ProtoA.maybe'singleEvent .~ _Just # ev'

encodeAssumptions (MergeAssumptions cond_ then_ else_) = do
    cond' <- expr_id cond_
    then' <- encodeAssumptions then_
    else' <- encodeAssumptions else_
    return $ defMessage
                & ProtoA.maybe'mergedAssumptions .~ _Just # (defMessage
                    & ProtoA.predicate .~ cond'
                    & ProtoA.assumptionsThen .~ then'
                    & ProtoA.assumptionsElse .~ else'
                )


encodeFrameIdentifier :: FrameIdentifier -> IO ProtoA.FrameIdentifier
encodeFrameIdentifier (FrameIdentifier i) = do
    return $ defMessage & ProtoA.id .~ i

encodeAssumptionFrames :: (sym ~ ExprBuilder s t st) => AssumptionFrames (Assumptions sym) -> IO ProtoA.AssumptionFrames
encodeAssumptionFrames (AssumptionFrames globalAssumptions frames) = do
    global' <- encodeAssumptions globalAssumptions
    frames' <- traverse encFrame frames
    return $ defMessage
        & ProtoA.globalAssumptions .~ global'
        & ProtoA.frames .~ (toList frames')
    where
        encFrame :: (sym ~ ExprBuilder s t st) =>
            (FrameIdentifier, Assumptions sym) -> IO ProtoA.AssumptionFrame
        encFrame (id, asms) = do
            asms' <- encodeAssumptions asms
            id' <- encodeFrameIdentifier id
            return
                $ defMessage
                    & ProtoA.frameIdentifier .~ id'
                    & ProtoA.assumptions .~ asms'

encodeAssumptionState :: (sym ~ ExprBuilder s t st) => AssumptionState sym -> IO ProtoA.AssumptionFrames
encodeAssumptionState = encodeAssumptionFrames . gcFrames

encodeCrucibleEvent :: (sym ~ ExprBuilder s t st) => CrucibleEvent (SymExpr sym) -> IO ProtoA.AssumptionEvent
encodeCrucibleEvent (CreateVariableEvent loc name tp expr) = do
    id' <- expr_id expr
    loc' <- (encodeProto loc)
    tp' <- encodeProto tp
    let name' = pack name

    return $ defMessage
            & ProtoA.maybe'createVariable .~ _Just # (
                defMessage
                    & ProtoA.location .~ loc'
                    & ProtoA.name .~ name'
                    & ProtoA.sort .~ tp'
                    & ProtoA.varExpr .~ id'
            )

encodeCrucibleEvent (LocationReachedEvent loc) = do
    loc' <- (encodeProto loc)
    return $ defMessage
            & ProtoA.maybe'locationReached .~ _Just # (
                defMessage
                    & ProtoA.location .~ loc'
            )