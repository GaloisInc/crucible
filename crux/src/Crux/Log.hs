{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Crux.Log (
  -- * Output Configuration
  Logs,
  OutputConfig(..)
  , outputHandle
  , quiet
  -- * Standard output API functions
  , SayWhat(..)
  , SayLevel(..)
  , say
  , logException
  , logSimResult
  , logGoal
  -- * Low-level output API functions
  , output
  , outputLn
  -- * Converting and emitting output
  , logToStd
  ) where

import           Control.Exception ( SomeException, bracket_,  )
import           Control.Lens
import           Data.Text ( Text, lines )
import           Data.Text.IO as TIO
import qualified Lumberjack as LJ
import           System.Console.ANSI
import           System.IO

import           Lang.Crucible.Backend ( AssumptionReason )
import qualified Lang.Crucible.Simulator.SimError as CSE

import           Crux.Types

----------------------------------------------------------------------
-- Various functions used by the main code to generate logging output

-- | Main function used to log/output a general text message of some kind
say :: Logs => SayLevel -> Text -> Text -> IO ()
say lvl frm = LJ.writeLog (?outputConfig ^. logWhat) . SayWhat lvl frm

-- | Function used to log/output exception information
logException :: Logs => SomeException -> IO ()
logException = LJ.writeLog (_logExc ?outputConfig)

-- | Function used to output the summary result for a completed
-- simulation.  If the flag is true, show the details of each failed
-- goal before showing the summary.
logSimResult :: Logs => Bool -> CruxSimulationResult -> IO ()
logSimResult showFailedGoals = LJ.writeLog (_logSimResult ?outputConfig showFailedGoals)

-- | Function used to output any individual goal proof failures from a simulation
logGoal :: Logs => ProvedGoals (Either AssumptionReason CSE.SimError) -> IO ()
logGoal = LJ.writeLog (_logGoal ?outputConfig)


----------------------------------------------------------------------
-- Logging types and constraints

-- | The Logs constraint should be applied for any function that will
-- use the main logging functions: says, logException, logSimResult,
-- or logGoal.
type Logs = (?outputConfig :: OutputConfig)

-- | Global options for Crux's main. These are not CruxOptions because
-- they are expected to be set directly by main, rather than by a
-- user's command-line options. They exist primarily to improve the
-- testability of the code.
--
-- The Crux mkOutputConfig is recommended as a helper function for
-- creating this object, although it can be initialized directly if
-- needed.
data OutputConfig =
  OutputConfig { _outputHandle :: Handle
               , _quiet :: Bool
               , _logWhat :: LJ.LogAction IO SayWhat
               , _logExc :: LJ.LogAction IO SomeException
               , _logSimResult :: Bool -> LJ.LogAction IO CruxSimulationResult
                 -- ^ True to show individual goals, false for summary only
               , _logGoal :: LJ.LogAction IO (ProvedGoals
                                              (Either AssumptionReason
                                               CSE.SimError))
               }

-- | Some client code will want to output to the main output stream
-- directly instead of using the logging/output functions above.  It
-- can either get the _outputHandle directly or it can use the
-- output/outputLn functions below.
outputHandle :: Getter OutputConfig Handle
outputHandle f o = o <$ f (_outputHandle o)

-- | Lens to allow client code to determine if running in quiet mode.
quiet :: Getter OutputConfig Bool
quiet f o = o <$ f (_quiet o)

logWhat :: Getter OutputConfig (LJ.LogAction IO SayWhat)
logWhat f o = o <$ f (_logWhat o)


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
    in mapM_ sayer $ Data.Text.lines msg
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

output :: Logs => String -> IO ()
output str = System.IO.hPutStr (view outputHandle ?outputConfig) str

-- | This function emits output to the normal output handle (specified
-- at initialization time).  This function is not recommended for
-- general use (the 'says', 'logException', 'logSimResult', 'logGoal',
-- etc. are preferred), but can be used by code needing more control
-- over the output formatting.
--
-- This function emits a newline at the end of the output.

outputLn :: Logs => String -> IO ()
outputLn str = System.IO.hPutStrLn (view outputHandle ?outputConfig) str
