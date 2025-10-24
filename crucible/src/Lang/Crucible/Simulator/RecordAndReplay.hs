{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.Simulator.RecordAndReplay (
  HasRecordState(..),
  RecordState,
  mkRecordState,
  HasReplayState(..),
  ReplayState,
  mkReplayState,
  recordTraceLength,
  replayTraceLength,
  RecordedTrace,
  getRecordedTrace,
  recordFeature,
  replayFeature,
  initialTrace,
  traceGlobal,
  emptyReplayTrace
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
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Panic (panic)
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
--
-- Intentionally not part of the API so as to keep the implementation abstract.
type TraceType = CT.SequenceType (CT.StringType W4.Unicode)

-- | Type parameters:
--
-- * @p@: see 'C.cruciblePersonality'
-- * @sym@: instance of 'Lang.Crucible.Backend.IsSymInterface'
-- * @ext@: language extension, see "Lang.Crucible.CFG.Extension"
-- * @rtp@: type of the simulator return value
type RecordState :: Type -> Type -> Type -> Type -> Type
newtype RecordState p sym ext rtp
  = RecordState (C.GlobalVar TraceType)
    -- ^ constructor intentionally not exported

{- | A trace from 'recordFeature', processed and ready for consumption by
'replayFeature'.
-}
newtype RecordedTrace sym
  = RecordedTrace (C.RegValue sym TraceType)

-- | Type parameters:
--
-- * @p@: see 'C.cruciblePersonality'
-- * @sym@: instance of 'Lang.Crucible.Backend.IsSymInterface'
-- * @ext@: language extension, see "Lang.Crucible.CFG.Extension"
-- * @rtp@: type of the simulator return value
type ReplayState :: Type -> Type -> Type -> Type -> Type
data ReplayState p sym ext rtp
  = ReplayState
    { _traceGlobal :: (C.GlobalVar TraceType)
    , _initialTrace :: (RecordedTrace sym)
    }
    -- ^ constructor intentionally not exported
Lens.makeLenses ''ReplayState
-- | Constructor for 'RecordState'
mkRecordState ::
  C.HandleAllocator -> IO (RecordState p sym ext rtp)
mkRecordState halloc =
  RecordState <$> C.freshGlobalVar halloc "recordState" W4.knownRepr

-- | Constructor for 'ReplayState'
mkReplayState ::
  C.HandleAllocator -> RecordedTrace sym  -> IO (ReplayState p sym ext rtp)
mkReplayState halloc rt =
  ReplayState <$> C.freshGlobalVar halloc "replayState" W4.knownRepr <*> pure rt

-- | A class for Crucible personality types @p@ which contain a
-- 'RecordState'. This execution feature is polymorphic over
-- 'RecordState' so that downstream users can supply their own
-- personality types that extend 'RecordAndReplay' further.
class HasRecordState p r sym ext rtp | p -> r sym ext rtp where
  recordState :: Lens.Lens' p (RecordState r sym ext rtp)

instance HasRecordState (RecordState p sym ext rtp) p sym ext rtp where
  recordState = id
  {-# INLINE recordState #-}

-- | A class for Crucible personality types @p@ which contain a
-- 'ReplayState'. This execution feature is polymorphic over
-- 'ReplayState' so that downstream users can supply their own
-- personality types that extend 'ReplayAndReplay' further.
class HasReplayState p r sym ext rtp | p -> r sym ext rtp where
  replayState :: Lens.Lens' p (ReplayState r sym ext rtp)

instance HasReplayState (ReplayState p sym ext rtp) p sym ext rtp where
  replayState = id
  {-# INLINE replayState #-}

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


emptyReplayTrace :: sym -> IO (RecordedTrace sym)
emptyReplayTrace sym =  RecordedTrace <$> CSSS.nilSymSequence sym
   

getRecordTrace ::
  HasRecordState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  Maybe (C.RegValue sym TraceType)
getRecordTrace simState = do
  let ctx = simState ^. C.stateContext
  let RecordState g = ctx ^. C.cruciblePersonality . recordState
  C.lookupGlobal g (simState ^. C.stateGlobals)

-- | Get the length of the currently recorded trace
recordTraceLength ::
  W4.IsExprBuilder sym =>
  HasRecordState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  IO (Maybe (W4.SymNat sym))
recordTraceLength simState = do
  let sym = simState ^. C.stateSymInterface
  case getRecordTrace simState of
    Nothing -> pure Nothing
    Just s -> Just <$> CSSS.lengthSymSequence sym s

getReplayTrace ::
  HasReplayState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  Maybe (C.RegValue sym TraceType)
getReplayTrace simState = do
  let ctx = simState ^. C.stateContext
  let g = ctx ^. C.cruciblePersonality . replayState . traceGlobal
  C.lookupGlobal g (simState ^. C.stateGlobals)

-- | Get the length of the trace being replayed
replayTraceLength ::
  W4.IsExprBuilder sym =>
  HasReplayState p p sym ext rtp =>
  C.SimState p sym ext rtp f args ->
  IO (Maybe (W4.SymNat sym))
replayTraceLength simState = do
  let sym = simState ^. C.stateSymInterface
  case getReplayTrace simState of
    Nothing -> pure Nothing
    Just s -> Just <$> CSSS.lengthSymSequence sym s

-- | An 'C.ExecutionFeature' to record traces.
--
-- During execution this logs program locations to a Crucible global variable.
-- After execution, this variable may be read with 'getRecordedTrace' and the
-- 'RecordedTrace' can be passed to 'replayFeature' to \"replay\" it, i.e., to
-- abort all branches that deviate from it.
--
-- If this is not called with 'C.InitialState' before any other 'C.ExecState',
-- it may throw a 'TraceGlobalNotDefined' exception.
recordFeature ::
  ( HasRecordState p p sym ext rtp
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
      HasRecordState p p sym ext rtp =>
      C.SimContext p sym ext ->
      C.SymGlobalState sym ->
      IO (C.SymGlobalState sym)
    insertNewTrace simCtx globals = do
      let RecordState g = simCtx ^. C.cruciblePersonality . recordState
      let sym = simCtx ^. C.ctxSymInterface
      nil <- CSSS.nilSymSequence sym
      return (C.insertGlobal g nil globals)

    getTraceOrThrow ::
      HasRecordState p p sym ext rtp =>
      C.SimState p sym ext rtp f args ->
      IO (C.RegValue sym TraceType)
    getTraceOrThrow st =
      case getRecordTrace st of
        Nothing -> X.throw TraceGlobalNotDefined
        Just t -> pure t

    insertTrace ::
      HasRecordState p p sym ext rtp =>
      C.SimState p sym ext rtp f args ->
      C.RegValue sym TraceType ->
      C.SimState p sym ext rtp f args
    insertTrace st v = do
      let simCtx = st ^. C.stateContext
      let RecordState g = simCtx ^. C.cruciblePersonality . recordState
      st & C.stateGlobals %~ C.insertGlobal g v

    consTrace ::
      HasRecordState p p sym ext rtp =>
      C.SimState p sym ext rtp f args ->
      C.RegValue sym (CT.StringType W4.Unicode) ->
      IO (C.SimState p sym ext rtp f args)
    consTrace st v = do
      s <- getTraceOrThrow st
      let sym = st ^. C.stateSymInterface
      s' <- CSSS.consSymSequence sym v s
      pure (insertTrace st s')


    -- ^ constructor intentionally not exported to keep 'TraceType' out of the
    -- API, but it could be exported in the future if necessary.

-- | Obtain a 'RecordedTrace' after execution.
--
-- This currently requires concretizing the trace, because there is no efficient
-- reverse operation for 'CSSS.SymSequence'.
getRecordedTrace ::
  W4.IsExprBuilder sym =>
  C.SymGlobalState sym ->
  RecordState p sym ext rtp ->
  sym ->
  -- | Evaluation for booleans, usually a 'What4.Expr.GroundEval.GroundEvalFn'
  (W4.Pred sym -> IO Bool) ->
  IO (RecordedTrace sym)
getRecordedTrace globals (RecordState g) sym evalBool = do
  case C.lookupGlobal g globals of
    Nothing -> X.throw TraceGlobalNotDefined
    Just s -> RecordedTrace <$> concretizeAndReverseTrace s
  where
    concretizeAndReverseTrace s = do
      concretized <- CSSS.concretizeSymSequence evalBool (evalStr sym) s
      let reversed = Seq.reverse concretized
      symbolized <- mapM (W4.stringLit sym . W4.UnicodeLiteral) reversed
      CSSS.fromListSymSequence sym (F.toList symbolized)

    evalStr ::
      W4.IsExpr (W4.SymExpr sym) =>
      sym ->
      W4.SymString sym W4.Unicode ->
      IO Text.Text
    evalStr _sym s =
      case W4.asString s of
        Just (W4.UnicodeLiteral s') -> pure s'
        Nothing -> panic "getRecordedTrace" ["Non-literal trace element?"]

{- | Inserts a recorded trace into the state's replay trace variable
The replay feature will follow this trace if it is enabled
-}
insertReplayTrace ::
  (HasReplayState p p sym ext rtp) =>
  C.SimState p sym ext rtp f args ->
  C.RegValue sym TraceType ->
  C.SimState p sym ext rtp f args
insertReplayTrace st v = do
  let simCtx = st ^. C.stateContext
  let g = simCtx ^. C.cruciblePersonality . replayState . traceGlobal
  st & C.stateGlobals %~ C.insertGlobal g v

-- | An 'C.ExecutionFeature' to replay traces recorded with 'recordFeature'.
--
-- Branches that deviate from the given trace will be aborted with
-- 'C.InfeasibleBranch'.
--
-- If this is not called with 'C.InitialState' before any other 'C.ExecState',
-- it may throw a 'TraceGlobalNotDefined' exception.
replayFeature ::
  ( HasReplayState p p sym ext rtp
  , W4.IsExprBuilder sym
  ) =>
  -- | Whether to stop at the end of the trace. If this is 'True' and execution
  -- has exhausted the trace, then any further execution will be aborted via
  -- 'C.InfeasibleBranch'.
  Bool ->
  C.ExecutionFeature p sym ext rtp
replayFeature stop =
  C.ExecutionFeature $
    \case
      C.InitialState simCtx globals abortHandler retTy cont -> do
        let rstate = simCtx ^. C.cruciblePersonality . replayState
        let g =  rstate ^. traceGlobal
        let RecordedTrace trace = rstate ^. initialTrace
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
                  let st' = insertReplayTrace st rest
                  let rState = C.RunningState runStateInfo st'
                  pure (C.ExecutionFeatureModifiedState rState)

      _ -> pure C.ExecutionFeatureNoChange
  where
    getTraceOrThrow ::
      HasReplayState p p sym ext rtp =>
      C.SimState p sym ext rtp f args ->
      IO (C.RegValue sym TraceType)
    getTraceOrThrow st =
      case getReplayTrace st of
        Nothing -> X.throw TraceGlobalNotDefined
        Just t -> pure t
