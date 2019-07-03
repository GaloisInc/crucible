{-# Language RankNTypes, ImplicitParams #-}
module Crux.Extension where

import Lang.Crucible.Simulator(GenericExecutionFeature,SimError)
import Lang.Crucible.Backend(IsSymInterface,AssumptionReason)

import Crux.Types(Model,Result,ProvedGoals)
import Crux.Log(Logs)
import Crux.Config(Config(..))
import Crux.Config.Common

data Language opts = Language
  { name :: String
    -- ^ Name for the extension

  , version :: String

  , configuration :: Config opts
    {- ^ Various configuration settings: configuration file, environment
         variables, and command line options. -}

  , initialize :: Options opts -> IO (Options opts)
    -- ^ Additional validation and setup

    -- | Call-back to do the actual simulation after initialization.
  , simulate :: SimulateCallback opts

    -- | Call back to generate counter examples, if needed.
  , makeCounterExamples :: CounterExampleCallback opts
 }

-- | Combined options for Crux and an extension.
type Options opts = (CruxOptions, opts)

-- | Type of the 'simulate' method.
type SimulateCallback opts =
    forall sym.  (IsSymInterface sym, Logs) =>
    [GenericExecutionFeature sym] {- ^ Execution features -} ->
    Options opts {- ^ Configuration -} ->
    sym          {- ^ The backend -} ->
    Model sym    {- ^ Initial model -} ->
    IO (Result sym)

-- | The type of the `makeCounterExamples` method.
type CounterExampleCallback opts =
  Logs =>
  Options opts {- ^ Configuration optsions -} ->
  ProvedGoals (Either AssumptionReason SimError)
  {- ^ The goals we looked at, and if they were proved. -} ->
  IO ()



