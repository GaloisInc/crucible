{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Text.IO qualified as IO
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.MIR.Debug qualified as Debug
import Lang.Crucible.MIR.Syntax (emptyParserHooks, mirParserHooks)
import Mir.Intrinsics (mirExtImpl)

main :: IO ()
main = do
  let ?parserHooks = mirParserHooks emptyParserHooks
  let cmdExt = Debug.mirCommandExt
  inputs <- Debug.defaultDebuggerInputs cmdExt
  Debug.bareDebuggerExt
    cmdExt
    Debug.mirExtImpl
    mirExtImpl
    inputs
    Debug.defaultDebuggerOutputs
    IO.putStrLn
