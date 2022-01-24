{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module SVComp.Log
  ( SupportsSVCompLogMessage,
    SVCompLogMessage (..),
    SVCompSkipReason (..),
    saySVComp,
    svCompLogMessageToSayWhat,
  )
where

import Crux (SayLevel (..), SayWhat (..))
import qualified Crux.Log as Log
import Crux.SVCOMP (ComputedVerdict (..), SVCompProperty (..))
import Data.Aeson (ToJSON)
import qualified Data.Text as T
import GHC.Generics (Generic)

data SVCompSkipReason
  = DueToBlacklist
  | NoInputFiles
  deriving (Generic, ToJSON)

svCompSkipReasonSuffix :: SVCompSkipReason -> T.Text
svCompSkipReasonSuffix DueToBlacklist = " due to blacklist"
svCompSkipReasonSuffix NoInputFiles = " because no input files are present"

data SVCompLogMessage
  = SimulatorThrewException
  | PropertyParseError T.Text T.Text
  | Skipping SVCompSkipReason T.Text
  | Verdict ComputedVerdict SVCompProperty
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

resultPrefix :: T.Text
resultPrefix = "Verification result: "

svCompLogMessageToSayWhat :: SVCompLogMessage -> SayWhat
svCompLogMessageToSayWhat SimulatorThrewException =
  svCompFail $ T.unlines
    [ resultPrefix <> "ERROR"
    , "Simulator threw exception"
    ]
svCompLogMessageToSayWhat (PropertyParseError prop msg) =
  svCompFail $ T.unlines
    [ resultPrefix <> "ERROR"
    , "Could not parse property:" <> prop
    , msg
    ]
svCompLogMessageToSayWhat (Skipping reason path) =
  svCompWarn
    ( T.unlines
        [ "Skipping:",
          "  " <> path <> svCompSkipReasonSuffix reason
        ]
    )
svCompLogMessageToSayWhat (Verdict verdict prop) =
  case verdict of
    Verified  -> svCompOK   $ resultPrefix <> "VERIFIED"
    Falsified -> svCompOK   $ resultPrefix <> "FALSIFIED (" <> displayProp prop <> ")"
    Unknown   -> svCompWarn $ resultPrefix <> "UNKNOWN"
  where
    displayProp CheckValidFree       = "valid-free"
    displayProp CheckValidDeref      = "valid-deref"
    displayProp CheckValidMemtrack   = "valid-memtrack"
    displayProp CheckValidMemCleanup = "valid-memcleanup"
    displayProp CheckNoOverflow      = "no-overflow"
    displayProp CheckTerminates      = "termination"
    displayProp CheckNoError{}       = "unreach-call"
    displayProp CheckDefBehavior     = "def-behavior"
    displayProp CoverageFQL{}        = "coverage"
