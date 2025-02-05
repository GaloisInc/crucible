{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Data.Text.IO qualified as IO
import Lang.Crucible.Debug qualified as Debug

main :: IO ()
main = do
  inputs <- Debug.defaultDebuggerInputs Debug.voidExts
  Debug.bareDebugger
    inputs
    Debug.defaultDebuggerOutputs
    IO.putStrLn
