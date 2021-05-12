{-# LANGUAGE ImplicitParams, ConstraintKinds #-}
-- from crucible-c/src/Log.hs
module Crux.Log (
  -- * Configuring output
  Logs,
  OutputConfig(..), showColors, outputHandle, errorHandle, defaultOutputConfig, quiet,
  -- * Performing output
  say, sayOK, sayWarn, sayFail, output, outputLn, sayIDE
  ) where

import Control.Exception (bracket_)
import Control.Lens

import System.Console.ANSI
import System.IO

type Logs =
  ( ?outputConfig :: OutputConfig
  , ?outputForIDE :: Bool
  )

-- | Global options for Crux's main. These are not CruxOptions because
-- they are expected to be set directly by main, rather than by a
-- user's command-line options. They exist primarily to improve the
-- testability of the code.
data OutputConfig =
  OutputConfig { _showColors :: Bool
               , _outputHandle :: Handle
               , _errorHandle :: Handle
               , _quiet :: Bool
               }

showColors :: Lens' OutputConfig Bool
showColors = lens _showColors (\ o s -> o { _showColors = s })

outputHandle :: Lens' OutputConfig Handle
outputHandle = lens _outputHandle (\ o h -> o { _outputHandle = h })

errorHandle :: Lens' OutputConfig Handle
errorHandle = lens _errorHandle (\ o h -> o { _errorHandle = h })

quiet :: Lens' OutputConfig Bool
quiet = lens _quiet (\ o b -> o { _quiet = b })

defaultOutputConfig :: OutputConfig
defaultOutputConfig = OutputConfig True stdout stderr False

output :: Logs => String -> IO ()
output str = hPutStr (view outputHandle ?outputConfig) str

outputLn :: Logs => String -> IO ()
outputLn str = hPutStrLn (view outputHandle ?outputConfig) str

outputColored :: Logs => Color -> String -> IO ()
outputColored c msg =
  let outH = view outputHandle ?outputConfig
      inColor = view showColors ?outputConfig
  in if inColor
       then bracket_
              (hSetSGR outH [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid c])
              (hSetSGR outH [Reset])
              (hPutStr outH msg)
       else output msg

sayOK :: Logs => String -> String -> IO ()
sayOK = sayCol (Just Green)

sayWarn :: Logs => String -> String -> IO ()
sayWarn = sayCol (Just Yellow)

sayFail :: Logs => String -> String -> IO ()
sayFail = sayCol (Just Red)

say :: Logs => String -> String -> IO ()
say = sayCol Nothing

sayIDE :: Logs => String -> String -> IO ()
sayIDE x y
  | not ?outputForIDE = return ()
  | otherwise = outputLn ("[" ++ x ++ "] " ++ y)

sayCol :: Logs => Maybe Color -> String -> String -> IO ()
sayCol col x y
  | view quiet ?outputConfig || ?outputForIDE = return ()
  | otherwise =
    do output "["
       maybe outputLn outputColored col x
       outputLn ("] " ++ y)
