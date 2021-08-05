{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Crux.Log (
  -- * Output Configuration
  Logs,
  OutputConfig(..)
  , outputHandle
  , quiet
  -- * Standard output API functions
  , CruxLogMessage(..)
  , LogDoc(..)
  , LogProofObligation(..)
  , SayWhat(..)
  , SayLevel(..)
  , SerializedLogProofObligation
  , SupportsCruxLogMessage
  , cruxJSONOptions
  , cruxLogMessageToSayWhat
  , cruxLogTag
  , logException
  , logGoal
  , logSimResult
  , say
  , sayCrux
  , withCruxLogMessage
  -- * Low-level output API functions
  , output
  , outputLn
  -- * Converting and emitting output
  , logToStd
  ) where

import           Control.Exception ( SomeException, bracket_,  )
import           Control.Lens ( Getter, view )
import qualified Data.Aeson as JSON
import           Data.Aeson.TH ( deriveToJSON )
import           Data.Aeson.TypeScript.TH ( deriveTypeScript, TypeScript(..) )
import           Data.Proxy (Proxy(Proxy))
import qualified Data.Text as T
import           Data.Text.IO as TIO ( hPutStr, hPutStrLn )
import           Data.Version ( Version, showVersion )
import           Data.Word ( Word64 )
import           GHC.Generics ( Generic )
import qualified Lumberjack as LJ
import           Prettyprinter ( SimpleDocStream )
import           Prettyprinter.Render.Text ( renderStrict )
import           System.Console.ANSI
    ( Color(..), ColorIntensity(..), ConsoleIntensity(..), ConsoleLayer(..)
    , SGR(..), hSetSGR )
import           System.IO ( Handle, hPutStr, hPutStrLn )

import           Crux.LogConfiguration ( cruxJSONOptions )
import           Crux.Types
    ( CruxSimulationResult, ProvedGoals, SayLevel(..), SayWhat(..) )
import           Crux.Version ( version )
import           Lang.Crucible.Backend ( ProofGoal(..), ProofObligation )
import           What4.Expr.Builder ( ExprBuilder )
import           What4.LabeledPred ( labeledPred, labeledPredMsg )


----------------------------------------------------------------------
-- Various functions used by the main code to generate logging output

newtype LogDoc = LogDoc (SimpleDocStream ())

instance TypeScript LogDoc where
  getTypeScriptType _ = "string"

instance JSON.ToJSON LogDoc where
  toJSON (LogDoc doc) = JSON.String (renderStrict doc)

-- | A version of 'ProofObligation' that supports a 'ToJSON' instance.
data LogProofObligation =
  forall t st fs.
  LogProofObligation (ProofObligation (ExprBuilder t st fs))

data SerializedLogProofObligation =
  SerializedLogProofObligation
    { labeledPred :: String
    , labeledPredMsg :: String
    }
    deriving ( Generic, JSON.ToJSON )

$(deriveTypeScript cruxJSONOptions ''SerializedLogProofObligation)


instance TypeScript LogProofObligation where
  getTypeScriptType _ = getTypeScriptType (Proxy :: Proxy SerializedLogProofObligation)

instance JSON.ToJSON LogProofObligation where
  -- for now, we only need the goal in the IDE
  toJSON (LogProofObligation g) =
    let
      goal = proofGoal g
    in
    JSON.toJSON (SerializedLogProofObligation {
      Crux.Log.labeledPred = show (view What4.LabeledPred.labeledPred goal),
      Crux.Log.labeledPredMsg = show (view What4.LabeledPred.labeledPredMsg goal)
    })

-- | All messages that Crux wants to output should be listed here.
--
-- Messages ought to be serializable to JSON so that they have a somewhat
-- portable machine-readable representation.  Some tools may rely on the
-- serialization format, so be sure to check with consumers before changing the
-- 'ToJSON' instance.
--
-- Other crux-based tools are encouraged to create their own:
--
-- * log message datatype '<Tool>LogMessage', similar to 'CruxLogMessage' below,
--
-- * constraint synonym 'Supports<Tool>LogMessage' similar to
-- 'SupportsCruxLogMessage' below,
--
-- * constraint dispatcher 'with<Tool>LogMessage' similar to
-- 'withCruxLogMessage' below,
--
-- * logger method 'say<Tool>' similar to 'sayCrux' below,
--
-- * default log message converter '<Tool>LogMessageToSayWhat' similar to
-- 'cruxLogMessageToSayWhat'.
--
-- The default log message converter can be used to decide how messages are
-- displayed to the standard output for a human consumer.  Automated tools may
-- prefer to filter and encode log messages in some machine-readable format and
-- exchange it over a separate channel.
data CruxLogMessage
  = AttemptingProvingVCs
  | Checking [FilePath]
  | DisablingBranchCoverageRequiresPathSatisfiability
  | DisablingProfilingIncompatibleWithPathSplitting
  | EndedGoal Integer
  | FoundCounterExample
  | Help LogDoc
  | PathsUnexplored Int
  | ProofObligations [LogProofObligation]
  | SimulationComplete
  | SimulationTimedOut
  | SkippingUnsatCoresBecauseMCSatEnabled
  | StartedGoal Integer
  | TotalPathsExplored Word64
  | UnsupportedTimeoutFor String -- ^ name of the backend
  | Version T.Text Version
  deriving (Generic)

$(deriveToJSON cruxJSONOptions ''CruxLogMessage)

$(deriveTypeScript cruxJSONOptions ''CruxLogMessage)


type SupportsCruxLogMessage msgs =
  ( ?injectCruxLogMessage :: CruxLogMessage -> msgs )

withCruxLogMessage ::
  (SupportsCruxLogMessage CruxLogMessage => a) -> a
withCruxLogMessage a =
  let ?injectCruxLogMessage = id in a


cruxLogTag :: T.Text
cruxLogTag = "Crux"


cruxNoisily :: T.Text -> SayWhat
cruxNoisily = SayWhat Noisily cruxLogTag

cruxOK :: T.Text -> SayWhat
cruxOK = SayWhat OK cruxLogTag

cruxSimply :: T.Text -> SayWhat
cruxSimply = SayWhat Simply cruxLogTag

cruxWarn :: T.Text -> SayWhat
cruxWarn = SayWhat Warn cruxLogTag


cruxLogMessageToSayWhat :: CruxLogMessage -> SayWhat

cruxLogMessageToSayWhat AttemptingProvingVCs =
  cruxSimply "Attempting to prove verification conditions."

cruxLogMessageToSayWhat (Checking files) =
  cruxNoisily ("Checking " <> T.intercalate ", " (T.pack <$> files))

cruxLogMessageToSayWhat DisablingBranchCoverageRequiresPathSatisfiability =
  cruxWarn
    "Branch coverage requires enabling path satisfiability checking.  Coverage measurement is disabled!"

cruxLogMessageToSayWhat DisablingProfilingIncompatibleWithPathSplitting =
  cruxWarn
    "Path splitting strategies are incompatible with Crucible profiling. Profiling is disabled!"

-- for now, this message is only for IDE consumers
cruxLogMessageToSayWhat (EndedGoal {}) = SayNothing

cruxLogMessageToSayWhat FoundCounterExample =
  cruxOK "Counterexample found, skipping remaining goals"

cruxLogMessageToSayWhat (Help (LogDoc doc)) =
  cruxOK (renderStrict doc)

cruxLogMessageToSayWhat (PathsUnexplored numberOfPaths) =
  cruxWarn
    ( T.unwords
        [ T.pack $ show numberOfPaths,
          "paths remaining not explored: program might not be fully verified"
        ]
    )

-- for now, this message is only for IDE consumers
cruxLogMessageToSayWhat (ProofObligations {}) = SayNothing

cruxLogMessageToSayWhat SimulationComplete =
  cruxNoisily "Simulation complete."

cruxLogMessageToSayWhat SimulationTimedOut =
  cruxWarn
    "Simulation timed out! Program might not be fully verified!"

cruxLogMessageToSayWhat SkippingUnsatCoresBecauseMCSatEnabled =
  cruxWarn "Warning: skipping unsat cores because MC-SAT is enabled."

-- for now, this message is only for IDE consumers
cruxLogMessageToSayWhat (StartedGoal {}) = SayNothing

cruxLogMessageToSayWhat (TotalPathsExplored i) =
  cruxSimply ("Total paths explored: " <> T.pack (show i))

cruxLogMessageToSayWhat (UnsupportedTimeoutFor backend) =
  cruxWarn
    (T.pack ("Goal timeout requested but not supported by " <> backend))

cruxLogMessageToSayWhat (Version nm ver) =
  cruxOK
    ( T.pack
        ( unwords
            [ "version: " <> version <> ",",
              T.unpack nm,
              "version: " <> (showVersion ver)
            ]
        )
    )

-- | Main function used to log/output a general text message of some kind
say ::
  Logs msgs =>
  ( ?injectMessage :: msg -> msgs ) =>
  msg -> IO ()
say = LJ.writeLog (view logMsg ?outputConfig) . ?injectMessage

sayCrux ::
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxLogMessage -> IO ()
sayCrux msg =
  let ?injectMessage = ?injectCruxLogMessage in
  say msg

-- | Function used to log/output exception information
logException :: Logs msgs => SomeException -> IO ()
logException = LJ.writeLog (_logExc ?outputConfig)

-- | Function used to output the summary result for a completed
-- simulation.  If the flag is true, show the details of each failed
-- goal before showing the summary.
logSimResult :: Logs msgs => Bool -> CruxSimulationResult -> IO ()
logSimResult showFailedGoals = LJ.writeLog (_logSimResult ?outputConfig showFailedGoals)

-- | Function used to output any individual goal proof failures from a simulation
logGoal :: Logs msgs => ProvedGoals -> IO ()
logGoal = LJ.writeLog (_logGoal ?outputConfig)


----------------------------------------------------------------------
-- Logging types and constraints

-- | The Logs constraint should be applied for any function that will
-- use the main logging functions: says, logException, logSimResult,
-- or logGoal.
type Logs msgs = ( ?outputConfig :: OutputConfig msgs )

-- | Global options for Crux's main. These are not CruxOptions because
-- they are expected to be set directly by main, rather than by a
-- user's command-line options. They exist primarily to improve the
-- testability of the code.
--
-- The Crux mkOutputConfig is recommended as a helper function for
-- creating this object, although it can be initialized directly if
-- needed.
data OutputConfig msgs =
  OutputConfig { _outputHandle :: Handle
               , _quiet :: Bool
               , _logMsg :: LJ.LogAction IO msgs
               , _logExc :: LJ.LogAction IO SomeException
               , _logSimResult :: Bool -> LJ.LogAction IO CruxSimulationResult
                 -- ^ True to show individual goals, false for summary only
               , _logGoal :: LJ.LogAction IO ProvedGoals
               }

-- | Some client code will want to output to the main output stream
-- directly instead of using the logging/output functions above.  It
-- can either get the _outputHandle directly or it can use the
-- output/outputLn functions below.
outputHandle :: Getter (OutputConfig msgs) Handle
outputHandle f o = o <$ f (_outputHandle o)

-- | Lens to allow client code to determine if running in quiet mode.
quiet :: Getter (OutputConfig msgs) Bool
quiet f o = o <$ f (_quiet o)

logMsg :: Getter (OutputConfig msgs) (LJ.LogAction IO msgs)
logMsg f o = o <$ f (_logMsg o)


----------------------------------------------------------------------
-- Logging default implementations (can be over-ridden by different
-- front end configurations).

-- | This is the default logging output function for a SayWhat
-- message.  It will emit the information with possible coloring (if
-- enabled via the first argument) to the proper handle (normal output
-- goes to the first handle, error output goes to the second handle,
-- and the same handle may be used for both).
--
-- Front-ends that don't have specific output needs can simply use
-- this function.  Alternative output functions can be used where
-- useful (e.g. JSON output).
logToStd :: Bool -> Handle -> Handle -> SayWhat -> IO ()
logToStd withColors outH errH = \case
  SayWhat lvl frm msg ->
    let sayer = case lvl of
                  OK -> colOut Green outH
                  Warn -> colOut Yellow errH
                  Fail -> colOut Red errH
                  Simply -> straightOut outH
                  Noisily -> straightOut outH
        colOut clr =
           if withColors
           then \hndl l -> do bracket_
                                (hSetSGR hndl [ SetConsoleIntensity BoldIntensity
                                              , SetColor Foreground Vivid clr])
                                (hSetSGR hndl [Reset])
                                (TIO.hPutStr hndl $ "[" <> frm <> "] ")
                              TIO.hPutStrLn hndl l
           else straightOut
        straightOut hndl l = do TIO.hPutStr hndl $ "[" <> frm <> "] "
                                TIO.hPutStrLn hndl l
    in mapM_ sayer $ T.lines msg
  SayMore s1 s2 -> do logToStd withColors outH errH s1
                      logToStd withColors outH errH s2
  SayNothing -> return ()


----------------------------------------------------------------------
-- Direct Output

-- | This function emits output to the normal output handle (specified
-- at initialization time).  This function is not recommended for
-- general use (the 'says', 'logException', 'logSimResult', 'logGoal',
-- etc. are preferred), but can be used by code needing more control
-- over the output formatting.
--
-- This function does _not_ emit a newline at the end of the output.

output :: Logs msgs => String -> IO ()
output str = System.IO.hPutStr (view outputHandle ?outputConfig) str

-- | This function emits output to the normal output handle (specified
-- at initialization time).  This function is not recommended for
-- general use (the 'says', 'logException', 'logSimResult', 'logGoal',
-- etc. are preferred), but can be used by code needing more control
-- over the output formatting.
--
-- This function emits a newline at the end of the output.

outputLn :: Logs msgs => String -> IO ()
outputLn str = System.IO.hPutStrLn (view outputHandle ?outputConfig) str
