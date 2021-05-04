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
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module UCCrux.LLVM.Logging
  ( Verbosity (..),
    verbosityToInt,
    verbosityFromInt,
    log,
  )
where

{- ORMOLU_DISABLE -}
import           Prelude hiding (log)

import           Data.Text as Text
import qualified Data.Text.IO as TextIO

import qualified Lumberjack as LJ
import           Lumberjack (writeLogM)
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
