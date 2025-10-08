{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}  -- IntrinsicClass

module Lang.Crucible.Simulator.RecordAndReplay (
  HasRecordAndReplayState(..),
  RecordAndReplayState,
  recordAndReplayState,
  TraceType,
  getTrace,
  RecordedTrace,
  getRecordedTrace,
  recordFeature,
  replayFeature,
) where

import Control.Exception qualified as X
import Control.Lens ((%~), (&), (^.))
import Control.Lens qualified as Lens
import Data.Foldable qualified as F
import Data.Kind (Type)
import Data.Text qualified as Text
import Data.Sequence qualified as Seq
import Lang.Crucible.Backend qualified as CB
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator.GlobalState qualified as C
import Lang.Crucible.Simulator.SymSequence qualified as CSSS
import Lang.Crucible.Types qualified as CT
import What4.Interface qualified as W4
import What4.Partial qualified as W4P

-- | A trace consists of the 'W4.ProgramLoc's returned by
-- 'W4.getCurrentProgramLoc' in 'C.RunningState's during symbolic execution.
type TraceType = CT.SequenceType (CT.StringType W4.Unicode)

-- | Type parameters:
--
-- * @p@: see 'C.cruciblePersonality'
-- * @sym@: instance of 'Lang.Crucible.Backend.IsSymInterface'
-- * @ext@: language extension, see "Lang.Crucible.CFG.Extension"
-- * @rtp@: type of the simulator return value
type RecordAndReplayState :: Type -> Type -> Type -> Type -> Type
newtype RecordAndReplayState p sym ext rtp
  = RecordAndReplayState { _traceRef :: C.GlobalVar TraceType }

-- | Constructor for 'RecordAndReplayState'
recordAndReplayState ::
  C.GlobalVar TraceType -> RecordAndReplayState p sym ext rtp
recordAndReplayState = RecordAndReplayState

-- | A class for Crucible personality types @p@ which contain a
-- 'RecordAndReplayState'. This execution feature is polymorphic over
-- 'RecordAndReplayState' so that downstream users can supply their own
-- personality types that extend 'RecordAndReplay' further.
class HasRecordAndReplayState p r sym ext rtp | p -> r sym ext rtp where
  rrState :: Lens.Lens' p (RecordAndReplayState r sym ext rtp)

instance HasRecordAndReplayState (RecordAndReplayState p sym ext rtp) p sym ext rtp where
  rrState = id
  {-# INLINE rrState #-}

data TraceGlobalNotDefined = TraceGlobalNotDefined

instance Show TraceGlobalNotDefined where
  show _ = "record and replay trace global not defined"

instance X.Exception TraceGlobalNotDefined

locAsStr ::
  W4.IsExprBuilder sym =>
  sym ->
  IO (C.RegValue sym (CT.StringType W4.Unicode))
locAsStr sym = do
  loc <- W4.getCurrentProgramLoc sym
  let txtLoc = Text.pack (show loc)
  W4.stringLit sym (W4.UnicodeLiteral txtLoc)

getTrace ::
  HasRecordAndReplayState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  Maybe (C.RegValue sym TraceType)
getTrace simState = do
  let ctx = simState ^. C.stateContext
  let RecordAndReplayState g = ctx ^. C.cruciblePersonality . rrState
  C.lookupGlobal g (simState ^. C.stateGlobals)

getTraceOrThrow ::
  HasRecordAndReplayState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  IO (C.RegValue sym TraceType)
getTraceOrThrow st =
  case getTrace st of
    Nothing -> X.throw TraceGlobalNotDefined
    Just t -> pure t

insertTrace ::
  HasRecordAndReplayState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  C.RegValue sym TraceType ->
  C.SimState p sym ext rtp f args
insertTrace st v = do
  let simCtx = st ^. C.stateContext
  let RecordAndReplayState g = simCtx ^. C.cruciblePersonality . rrState
  st & C.stateGlobals %~ C.insertGlobal g v

-- | An 'C.ExecutionFeature' to record traces.
--
-- During execution this logs program locations to a Crucible global variable
-- (@'C.GlobalVar' 'TraceType'@). Such a trace may be passed as the first
-- parameter to this function to \"replay\" it, i.e., to abort all branches that
-- deviate from it.
--
-- If this is not called with 'C.InitialState' before any other 'C.ExecState',
-- it may throw a 'TraceGlobalNotDefined' exception.
recordFeature ::
  ( HasRecordAndReplayState p p sym ext rtp
  , W4.IsExprBuilder sym
  ) =>
  C.ExecutionFeature p sym ext rtp
recordFeature =
  C.ExecutionFeature $
    \case
      C.InitialState simCtx globals abortHandler retTy cont -> do
        globals' <- insertNewTrace simCtx globals
        let iState = C.InitialState simCtx globals' abortHandler retTy cont
        return $ C.ExecutionFeatureModifiedState iState
      C.RunningState runStateInfo st -> do
        loc <- locAsStr (st ^. C.stateSymInterface)
        st' <- consTrace st loc
        let rState = C.RunningState runStateInfo st'
        return $ C.ExecutionFeatureModifiedState rState
      _ -> pure C.ExecutionFeatureNoChange
  where
    insertNewTrace ::
      HasRecordAndReplayState p p sym ext rtp =>
      C.SimContext p sym ext ->
      C.SymGlobalState sym ->
      IO (C.SymGlobalState sym)
    insertNewTrace simCtx globals = do
      let RecordAndReplayState g = simCtx ^. C.cruciblePersonality . rrState
      let sym = simCtx ^. C.ctxSymInterface
      nil <- CSSS.nilSymSequence sym
      return (C.insertGlobal g nil globals)

    consTrace ::
      HasRecordAndReplayState p p sym ext rtp =>
      C.SimState p sym ext rtp f args ->
      C.RegValue sym (CT.StringType W4.Unicode) ->
      IO (C.SimState p sym ext rtp f args)
    consTrace st v = do
      s <- getTraceOrThrow st
      let sym = st ^. C.stateSymInterface
      s' <- CSSS.consSymSequence sym v s
      pure (insertTrace st s')

-- | A trace from 'recordFeature', processed and ready for consumption by
-- 'replayFeature'.
newtype RecordedTrace sym = RecordedTrace (C.RegValue sym TraceType)

-- | Obtain a 'RecordedTrace' after execution.
--
-- This currently requires concretizing the trace, because there is no efficient
-- reverse operation for 'CSSS.SymSequence'.
getRecordedTrace ::
  W4.IsExprBuilder sym =>
  C.SymGlobalState sym ->
  C.GlobalVar TraceType ->
  sym ->
  -- | Evaluation for booleans, usually a 'What4.Expr.GroundEval.GroundEvalFn'
  (W4.Pred sym -> IO Bool) ->
  -- | Evaluation for strings, usually a 'What4.Expr.GroundEval.GroundEvalFn'
  (W4.SymString sym W4.Unicode -> IO Text.Text) ->
  IO (RecordedTrace sym)
getRecordedTrace globals g sym evalBool evalStr = do
  case C.lookupGlobal g globals of
    Nothing -> X.throw TraceGlobalNotDefined
    Just s -> RecordedTrace <$> concretizeAndReverseTrace s
  where
    concretizeAndReverseTrace s = do
      concretized <- CSSS.concretizeSymSequence evalBool evalStr s
      let reversed = Seq.reverse concretized
      symbolized <- mapM (W4.stringLit sym . W4.UnicodeLiteral) reversed
      CSSS.fromListSymSequence sym (F.toList symbolized)

-- | An 'C.ExecutionFeature' to replay traces recorded with 'recordFeature'.
--
-- Branches that deviate from the given trace will be aborted with
-- 'C.InfeasibleBranch'.
--
-- If this is not called with 'C.InitialState' before any other 'C.ExecState',
-- it may throw a 'TraceGlobalNotDefined' exception.
replayFeature ::
  ( HasRecordAndReplayState p p sym ext rtp
  , W4.IsExprBuilder sym
  ) =>
  RecordedTrace sym ->
  -- | Whether to stop at the end of the trace. If this is 'True' and execution
  -- has exhausted the trace, then any further execution will be aborted via
  -- 'C.InfeasibleBranch'.
  Bool ->
  C.ExecutionFeature p sym ext rtp
replayFeature (RecordedTrace trace) stop =
  C.ExecutionFeature $
    \case
      C.InitialState simCtx globals abortHandler retTy cont -> do
        let RecordAndReplayState g = simCtx ^. C.cruciblePersonality . rrState
        let globals' = C.insertGlobal g trace globals
        let iState = C.InitialState simCtx globals' abortHandler retTy cont
        return $ C.ExecutionFeatureModifiedState iState
      C.RunningState runStateInfo st -> do
        let sym = st ^. C.stateSymInterface
        s <- getTraceOrThrow st
        partExpr <- CSSS.unconsSymSequence sym (W4.stringIte sym) s
        let badPath = do
              loc <- W4.getCurrentProgramLoc sym
              let st' = C.AbortState (CB.InfeasibleBranch loc) st
              pure (C.ExecutionFeatureNewState st')
        case partExpr of
          W4P.Unassigned
            | stop -> badPath
            | otherwise -> pure C.ExecutionFeatureNoChange
          W4P.PE valid (expectedLoc, rest) ->
            C.withBackend (st ^. C.stateContext) $ \bak -> do
              let msg = "Trace must be valid"
              CB.assert bak valid (C.AssertFailureSimError msg "")

              currLoc <- locAsStr sym
              atExpectedLoc <- W4.stringEq sym currLoc expectedLoc
              case W4.asConstantPred atExpectedLoc of
                Just False -> badPath
                _ -> do
                  let msg' = "Execution deviated from trace"
                  CB.assert bak atExpectedLoc (C.AssertFailureSimError msg' "")
                  let st' = insertTrace st rest
                  let rState = C.RunningState runStateInfo st'
                  pure (C.ExecutionFeatureNewState rState)

      _ -> pure C.ExecutionFeatureNoChange
