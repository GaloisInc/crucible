{-
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}

module Logging
  ( Log.Logs,
    UCCruxLLVMTestLogging,
    withUCCruxLLVMTestLogging,
    ucCruxLLVMTestLoggingToSayWhat,
    sayUCCruxLLVMTest,
    UCCruxLLVMTestLogMessage(ClangTrouble)
  ) where

{- ORMOLU_DISABLE -}
import           Data.Aeson (ToJSON)
import           GHC.Generics (Generic)

import qualified Crux
import qualified Crux.Log as Log

import qualified Crux.LLVM.Log as Log

import qualified UCCrux.LLVM.Main as Main
import qualified UCCrux.LLVM.Logging as Log
{- ORMOLU_ENABLE -}

-- | Extra logging messages specific to this test suite

data UCCruxLLVMTestLogMessage
  = ClangTrouble
  deriving (Generic, ToJSON)

type SupportsUCCruxLLVMTestLogMessage msgs =
  (?injectUCCruxLLVMTestLogMessage :: UCCruxLLVMTestLogMessage -> msgs)

sayUCCruxLLVMTest ::
  Crux.Logs msgs =>
  (?injectUCCruxLLVMTestLogMessage :: UCCruxLLVMTestLogMessage -> msgs) =>
  UCCruxLLVMTestLogMessage ->
  IO ()
sayUCCruxLLVMTest msg =
  let ?injectMessage = ?injectUCCruxLLVMTestLogMessage
   in Crux.say msg

ucCruxLLVMTestLogMessageToSayWhat ::
  UCCruxLLVMTestLogMessage ->
  Crux.SayWhat
ucCruxLLVMTestLogMessageToSayWhat ClangTrouble =
  Crux.SayWhat Crux.Fail Log.ucCruxLLVMTag "Trouble when running Clang:"

-- | Logging data type joining test log messages and uc-crux-llvm log messages

data UCCruxLLVMTestLogging
  = LoggingViaUCCruxLLVM Main.UCCruxLLVMLogging
  | LoggingUCCruxLLVMTest UCCruxLLVMTestLogMessage
  deriving (Generic, ToJSON)

ucCruxLLVMTestLoggingToSayWhat :: UCCruxLLVMTestLogging -> Log.SayWhat
ucCruxLLVMTestLoggingToSayWhat (LoggingViaUCCruxLLVM msg) =
  Main.ucCruxLLVMLoggingToSayWhat msg
ucCruxLLVMTestLoggingToSayWhat (LoggingUCCruxLLVMTest msg) =
  ucCruxLLVMTestLogMessageToSayWhat msg

withUCCruxLLVMTestLogging ::
  ( ( Log.SupportsCruxLogMessage UCCruxLLVMTestLogging,
      Log.SupportsCruxLLVMLogMessage UCCruxLLVMTestLogging,
      Log.SupportsUCCruxLLVMLogMessage UCCruxLLVMTestLogging,
      SupportsUCCruxLLVMTestLogMessage UCCruxLLVMTestLogging
    ) =>
    computation
  ) ->
  computation
withUCCruxLLVMTestLogging computation =
  let ?injectCruxLogMessage = LoggingViaUCCruxLLVM . Main.LoggingCrux
      ?injectCruxLLVMLogMessage = LoggingViaUCCruxLLVM . Main.LoggingCruxLLVM
      ?injectUCCruxLLVMLogMessage = LoggingViaUCCruxLLVM . Main.LoggingUCCruxLLVM
      ?injectUCCruxLLVMTestLogMessage = LoggingUCCruxLLVMTest
   in computation
