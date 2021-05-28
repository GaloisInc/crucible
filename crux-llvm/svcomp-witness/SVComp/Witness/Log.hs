{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module SVComp.Witness.Log
  ( SupportsSVCompWitnessLogMessage,
    SVCompWitnessLogMessage (..),
    SVCompWitnessSkipReason (..),
    saySVCompWitness,
    svCompWitnessLogMessageToSayWhat,
  ) where

import Crux (SayLevel (..), SayWhat (..))
import qualified Crux.Log as Log
import Crux.SVCOMP (ComputedVerdict (..), SVCompProperty (..))
import qualified Data.Text as T

data SVCompWitnessSkipReason
  = DueToBlacklist
  | NoInputFiles

svCompWitnessSkipReasonSuffix :: SVCompWitnessSkipReason -> T.Text
svCompWitnessSkipReasonSuffix DueToBlacklist = " due to blacklist"
svCompWitnessSkipReasonSuffix NoInputFiles = " because no input files are present"

data SVCompWitnessLogMessage
  = SimulatorThrewException
  | PropertyParseError T.Text T.Text
  | Skipping SVCompWitnessSkipReason T.Text
  | Verdict ComputedVerdict SVCompProperty

type SupportsSVCompWitnessLogMessage msgs =
  (?injectSVCompWitnessLogMessage :: SVCompWitnessLogMessage -> msgs)

saySVCompWitness ::
  Log.Logs msgs =>
  SupportsSVCompWitnessLogMessage msgs =>
  SVCompWitnessLogMessage ->
  IO ()
saySVCompWitness msg =
  let ?injectMessage = ?injectSVCompWitnessLogMessage
   in Log.say msg


svCompWitnessTag :: T.Text
svCompWitnessTag = "SVCOMP"

svCompWitnessFail :: T.Text -> SayWhat
svCompWitnessFail = SayWhat Fail svCompWitnessTag

svCompWitnessOK :: T.Text -> SayWhat
svCompWitnessOK = SayWhat OK svCompWitnessTag

svCompWitnessWarn :: T.Text -> SayWhat
svCompWitnessWarn = SayWhat Warn svCompWitnessTag

resultPrefix :: T.Text
resultPrefix = "Verification result: "

svCompWitnessLogMessageToSayWhat :: SVCompWitnessLogMessage -> SayWhat
svCompWitnessLogMessageToSayWhat SimulatorThrewException =
  svCompWitnessFail $ T.unlines
    [ resultPrefix <> "ERROR"
    , "Simulator threw exception"
    ]
svCompWitnessLogMessageToSayWhat (PropertyParseError prop msg) =
  svCompWitnessFail $ T.unlines
    [ resultPrefix <> "ERROR"
    , "Could not parse property:" <> prop
    , msg
    ]
svCompWitnessLogMessageToSayWhat (Skipping reason path) =
  svCompWitnessWarn
    ( T.unlines
        [ "Skipping:",
          "  " <> path <> svCompWitnessSkipReasonSuffix reason
        ]
    )
svCompWitnessLogMessageToSayWhat (Verdict verdict prop) =
  case verdict of
    Verified  -> svCompWitnessOK   $ resultPrefix <> "VERIFIED"
    Falsified -> svCompWitnessOK   $ resultPrefix <> "FALSIFIED (" <> displayProp prop <> ")"
    Unknown   -> svCompWitnessWarn $ resultPrefix <> "UNKNOWN"
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
