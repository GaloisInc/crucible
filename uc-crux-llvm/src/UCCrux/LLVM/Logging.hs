{-
Module       : UCCrux.LLVM.Logging
Description  : Logging for uc-crux-llvm.
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

NOTE! This module contains an orphan instance of a 'LJ.HasLog' instance for
'IO'. It'd be nice to be rid of this but it seems like a not-unsizable chunk of
work...
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module UCCrux.LLVM.Logging
  ( SupportsUCCruxLLVMLogMessage,
    UCCruxLLVMLogMessage (..),
    Verbosity (..),
    ucCruxLLVMLogMessageToSayWhat,
    log,
    sayUCCruxLLVM,
    ucCruxLLVMTag,
    verbosityToInt,
    verbosityFromInt,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Data.Text as Text
import qualified Data.Text.IO as TextIO

import qualified Lumberjack as LJ
import           Lumberjack (writeLogM)

import qualified Crux.Log as Log
{- ORMOLU_ENABLE -}

instance LJ.HasLog Text IO where
  getLogAction = pure $ LJ.LogAction (TextIO.putStrLn . ("[Crux] " <>))

log :: Verbosity -> Text -> IO ()
log _ = writeLogM

data Verbosity
  = Low
  | Med
  | Hi
  deriving (Bounded, Eq, Enum, Ord)

verbosityToInt :: Verbosity -> Int
verbosityToInt =
  \case
    Low -> 0
    Med -> 1
    Hi -> 2

verbosityFromInt :: Int -> Verbosity
verbosityFromInt =
  \case
    0 -> Low
    1 -> Med
    _ -> Hi

data UCCruxLLVMLogMessage
  = Results
      Text
      -- ^ Function name
      Text
      -- ^ Summary

type SupportsUCCruxLLVMLogMessage msgs =
  (?injectUCCruxLLVMLogMessage :: UCCruxLLVMLogMessage -> msgs)

sayUCCruxLLVM ::
  Log.Logs msgs =>
  SupportsUCCruxLLVMLogMessage msgs =>
  UCCruxLLVMLogMessage ->
  IO ()
sayUCCruxLLVM msg =
  let ?injectMessage = ?injectUCCruxLLVMLogMessage
   in Log.say msg

ucCruxLLVMTag :: Text
ucCruxLLVMTag = "UC-Crux-LLVM"

ucCruxLLVMLogMessageToSayWhat :: UCCruxLLVMLogMessage -> Log.SayWhat
ucCruxLLVMLogMessageToSayWhat (Results func summary) =
  Log.SayWhat
    Log.Simply
    ucCruxLLVMTag
    ( Text.unlines
        [ "Results for " <> func,
          summary
        ]
    )
