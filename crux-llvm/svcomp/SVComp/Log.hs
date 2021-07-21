{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module SVComp.Log
  ( EvaluationProcessFailureReason (..),
    SupportsSVCompLogMessage,
    SVCompLogMessage (..),
    SVCompSkipReason (..),
    saySVComp,
    svCompLogMessageToSayWhat,
  )
where

import Crux (SayLevel (..), SayWhat (..))
import qualified Crux.Log as Log
import Crux.SVCOMP (ComputedVerdict (..))
import Data.Aeson (ToJSON)
import qualified Data.Text as T
import GHC.Generics (Generic)

data EvaluationProcessFailureReason
  = ExitedWithFailureCode T.Text
  | StoppedBySignal T.Text
  | TerminatedBySignal T.Text
  | UnknownStatus
  deriving (Generic, ToJSON)

data SVCompSkipReason
  = DueToBlacklist
  | NoInputFiles
  deriving (Generic, ToJSON)

svCompSkipReasonSuffix :: SVCompSkipReason -> T.Text
svCompSkipReasonSuffix DueToBlacklist = " due to blacklist"
svCompSkipReasonSuffix NoInputFiles = " because no input files are present"

data SVCompLogMessage
  = DoubleFaultWhileTryingToRemove T.Text
  | ElapsedWallClockTime T.Text
  | Evaluating
      T.Text
      -- ^ task root
      T.Text
      -- ^ source file
  | EvaluationProcessFailed EvaluationProcessFailureReason
  | FailedToCompileTask T.Text
  | SimulatorThrewException
  | VerdictExpecting
      Bool
      -- ^ the expected verdict (True for success, False for failure)
      ComputedVerdict
      -- ^ the actual verdict
  | NoVerdict [T.Text]
  | Skipping SVCompSkipReason T.Text
  deriving (Generic, ToJSON)

type SupportsSVCompLogMessage msgs =
  (?injectSVCompLogMessage :: SVCompLogMessage -> msgs)

saySVComp ::
  Log.Logs msgs =>
  SupportsSVCompLogMessage msgs =>
  SVCompLogMessage ->
  IO ()
saySVComp msg =
  let ?injectMessage = ?injectSVCompLogMessage
   in Log.say msg


svCompTag :: T.Text
svCompTag = "SVCOMP"

svCompFail :: T.Text -> SayWhat
svCompFail = SayWhat Fail svCompTag

svCompOK :: T.Text -> SayWhat
svCompOK = SayWhat OK svCompTag

svCompWarn :: T.Text -> SayWhat
svCompWarn = SayWhat Warn svCompTag

svCompLogMessageToSayWhat :: SVCompLogMessage -> SayWhat
svCompLogMessageToSayWhat (DoubleFaultWhileTryingToRemove path) =
  svCompFail ("Double fault! While trying to remove: " <> path)
svCompLogMessageToSayWhat (ElapsedWallClockTime time) =
  svCompOK ("Elapsed wall-clock time: " <> time)
svCompLogMessageToSayWhat (Evaluating taskRoot sourceFile) =
  svCompOK
    ( T.unlines
        [ "Evaluating:",
          "  " <> taskRoot,
          "  " <> sourceFile
        ]
    )
svCompLogMessageToSayWhat (EvaluationProcessFailed (ExitedWithFailureCode code)) =
  svCompFail ("Evaluation process exited with failure code " <> code)
svCompLogMessageToSayWhat (EvaluationProcessFailed (TerminatedBySignal signal)) =
  svCompWarn ("Evaluation process terminated by signal " <> signal)
svCompLogMessageToSayWhat (EvaluationProcessFailed (StoppedBySignal signal)) =
  svCompWarn ("Evaluation process stopped by signal " <> signal)
svCompLogMessageToSayWhat (EvaluationProcessFailed UnknownStatus) =
  svCompFail "Could not retrieve evaluation process status"
svCompLogMessageToSayWhat (FailedToCompileTask path) =
  svCompFail ("Failed to compile task:" <> path)
svCompLogMessageToSayWhat (NoVerdict task) =
  svCompWarn (T.unlines ("No verdict to evaluate!" : task))
svCompLogMessageToSayWhat SimulatorThrewException =
  svCompFail "Simulator threw exception"
svCompLogMessageToSayWhat (Skipping reason path) =
  svCompWarn
    ( T.unlines
        [ "Skipping:",
          "  " <> path <> svCompSkipReasonSuffix reason
        ]
    )
svCompLogMessageToSayWhat (VerdictExpecting False Verified) =
  svCompFail "FAILED! benchmark should contain an error!"
svCompLogMessageToSayWhat (VerdictExpecting False Falsified) =
  svCompOK "CORRECT (Falsified)"
svCompLogMessageToSayWhat (VerdictExpecting False Unknown) =
  svCompWarn "UNKNOWN (Should be falsified)"
svCompLogMessageToSayWhat (VerdictExpecting True Verified) =
  svCompOK "CORRECT (Verified)"
svCompLogMessageToSayWhat (VerdictExpecting True Falsified) =
  svCompFail "FAILED! benchmark should be verified"
svCompLogMessageToSayWhat (VerdictExpecting True Unknown) =
  svCompWarn "UNKNOWN (Should verify)"
