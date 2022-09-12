{-# LANGUAGE GADTs #-}

module Lang.Crucible.Protobuf.Encodings.Events (
    buildTraceEvent,
    assembleBranchSwitchEvent,
    assembleBranchAbortEvent,
    assemblePathSplitEvent,
    assemblePathMergeEvent,
    assembleCallEvent,
    assembleReturnEvent,
    encodePathID,
) where
import Data.ProtoLens (Message(defMessage), showMessage, encodeMessage)
import Lens.Micro

import Lang.Crucible.Backend (AssumptionState)
import Lang.Crucible.Protobuf.Encodings.Assumptions(encodeAssumptionState)
import What4.Expr (ExprBuilder)
import qualified CrucibleProtobufTrace.ProtoDefs.Common as COM
import qualified CrucibleProtobufTrace.ProtoDefs.SymExpr as SE
import qualified CrucibleProtobufTrace.ProtoDefs.Abort as AB
import qualified CrucibleProtobufTrace.ProtoDefs.Assumptions as AS
import qualified CrucibleProtobufTrace.ProtoDefs.OperationTrace as OT
import CrucibleProtobufTrace.What4Encodings ()
import CrucibleProtobufTrace.ProtoDefs.OperationTrace (newPathId)

import Data.Text (pack, unpack)

import qualified System.Directory (doesFileExist, doesDirectoryExist, createDirectory)

import qualified Data.ByteString
import qualified Crypto.Hash.SHA1 as SHA1
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.UTF8 as UTF8
import qualified Text.Printf
import CrucibleProtobufTrace.GlobalEncodingState (getOutDirRef)
import System.FilePath ((</>))
import What4.FunctionName

encodePathID :: (sym ~ ExprBuilder s t st) => AssumptionState sym -> IO OT.PathID
encodePathID state = do
    out_dir <- getOutDirRef
    let dirPath = out_dir </> "path_ids"
    state' <- encodeAssumptionState state
    let
      hash = (pack . UTF8.toString . Base16.encode . SHA1.hash . encodeMessage $ state')
      data' = showMessage state'
    do
      System.Directory.doesDirectoryExist dirPath >>= \x ->
          case x of
              True -> return ()
              False -> System.Directory.createDirectory dirPath

      let filePath = dirPath </> (unpack hash)
      System.Directory.doesFileExist filePath >>= \exists -> case exists of
              False -> do
                  writeFile filePath data'
                  return ()
              _ -> return ()

    -- return $ defMessage & OT.assumptionFrames .~ state'
    return $ defMessage & OT.text .~ hash

buildTraceEvent :: IO OT.PathID -> IO COM.MaybeProgramLoc -> IO OT.TraceEvent'EventKind -> IO OT.TraceEvent
buildTraceEvent pathId loc eventKind = do
    pathId' <- pathId
    loc' <- loc
    eventKind' <- eventKind
    return $ defMessage
        & OT.pathId .~ pathId'
        & OT.location .~ loc'
        & OT.maybe'eventKind ?~ eventKind'

assembleBranchSwitchEvent :: IO OT.PathID -> IO OT.PathID -> IO AS.Assumptions -> IO SE.ExpressionID -> IO COM.MaybeProgramLoc -> IO OT.TraceEvent'EventKind
assembleBranchSwitchEvent from to suspendedAssumptions pred branchLoc = do
    from' <- from
    to' <- to
    pred' <- pred
    suspendedAssumptions' <- suspendedAssumptions
    branchLoc' <- branchLoc
    return $
      OT.TraceEvent'BranchSwitch $
        defMessage
          & OT.idSuspended .~ from'
          & OT.idResumed .~ to'
          & OT.suspendedAssumptions .~ suspendedAssumptions'
          & OT.branchCondition .~ pred'
          & OT.branchLocation .~ branchLoc'

assembleBranchAbortEvent :: IO AB.AbortedResult -> IO AS.Assumptions -> IO OT.PathID -> IO OT.PathID -> IO OT.TraceEvent'EventKind
assembleBranchAbortEvent abortReason abortedAssumptions abortedPID resumedPID = do
    abortReason' <- abortReason
    abortedAssumptions' <- abortedAssumptions
    abortedPID' <- abortedPID
    resumedPID' <- resumedPID
    return $
      OT.TraceEvent'BranchAbort $
        defMessage
          & OT.abortResult .~ abortReason'
          & OT.abortedAssumptions .~ abortedAssumptions'
          & OT.idResumed .~ resumedPID'
          & OT.idAborted .~ abortedPID'

assemblePathSplitEvent :: IO OT.PathID -> IO SE.ExpressionID -> IO OT.TraceEvent'EventKind
assemblePathSplitEvent newPId condition = do
    pid <- newPId
    cond <- condition
    -- suspendedFrame' <- suspendedFrame
    return
      $ OT.TraceEvent'PathSplit
        $ defMessage
          & OT.splitCondition .~ cond
          & OT.continuingPathId .~ pid

assemblePathMergeEvent ::
  IO OT.PathID        ->
  IO SE.ExpressionID  ->
  IO AS.Assumptions   ->
  IO AS.Assumptions   ->
  IO OT.PathID        ->
  IO OT.PathID        ->
  IO OT.TraceEvent'EventKind

assemblePathMergeEvent oldPId condition pathAssumptions otherAssumptions basePID newPID = do
    pid <- oldPId
    cond <- condition
    pathAssumptions' <- pathAssumptions
    otherAssumptions' <- otherAssumptions
    basePID' <- basePID
    newPID' <- newPID
    return
      $ OT.TraceEvent'PathMerge
        $ defMessage
          & OT.mergingPathId .~ pid
          & OT.mergeCondition .~ cond
          & OT.pathAssumptions .~ pathAssumptions'
          & OT.otherAssumptions .~ otherAssumptions'
          & OT.pathIdBase .~ basePID'
          & OT.pathIdAfter .~ newPID'

assembleCallEvent :: FunctionName -> Bool -> IO OT.TraceEvent'EventKind
assembleCallEvent funcName isTailCall = do
  return
    $ OT.TraceEvent'CallFunction
        $ defMessage
            & OT.funcName .~ (functionName funcName)
            & OT.isTailCall .~ isTailCall

assembleReturnEvent :: FunctionName -> IO OT.TraceEvent'EventKind
assembleReturnEvent fname = do
  return
      $ OT.TraceEvent'ReturnFromFunction
          $ defMessage
              & OT.funcName .~ (functionName fname)

-- assembleAssumeEvent :: IO SE.ExpressionID -> IO OT.PathID -> IO OT.TraceEvent'EventKind
-- assembleAssumeEvent pred pathIDAfter = do
--   encodedPathIDAfter <- pathIDAfter
--   encodedPred <- pred

--   return
--     $ OT.TraceEvent'Assume
--       $ defMessage
--           & OT.predicate .~ encodedPred
--           & OT.newPathId .~ encodedPathIDAfter
