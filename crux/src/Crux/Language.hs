{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# Language ExistentialQuantification #-}
{-# Language FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# Language ScopedTypeVariables #-}

{-# Language TypeFamilies #-}
{-# Language UndecidableInstances #-}

module Crux.Language where

import Data.Typeable(Typeable)
import System.Console.GetOpt

import Lang.Crucible.Simulator
import Lang.Crucible.Backend

import Crux.Log
import Crux.Types

type Verbosity = Int

-- | Default options for command-line crux programs
-- These options can be set using command-line flags and environment
-- variables.
-- They can also be extended on a per-language basis
data CruxOptions = CruxOptions
  {
    showHelp         :: Bool
    -- ^ describe options & quit
  , showVersion      :: Bool
    -- ^ show tool version & quit
  , simVerbose       :: Verbosity
    -- ^ chattiness of the output
  , inputFile        :: FilePath
    -- ^ the file to analyze
  , outDir           :: FilePath
    -- ^ write results in this location
    -- if unset, do not produce any analysis results
  , checkPathSat             :: Bool
    -- ^ Should we enable path satisfiability checking?
  , profileCrucibleFunctions :: Bool
  , profileSolver            :: Bool
  , globalTimeout            :: Maybe String
  , goalTimeout            :: Integer
  , profileOutputInterval    :: Maybe String
  , loopBound :: Maybe String
    -- ^ Should we artifically bound the number of loop iterations
  , makeCexes :: Bool
    -- ^ Should we construct counter-example executables
  }

type Options a = (CruxOptions, LangOptions a)

-- A language configuration consists of an instantiation of
-- the Crux.Language type class, as well as the values of
-- language specific options for a particular run.
-- SCW: This is totally an object.
data LangConf where
  LangConf :: forall a. Language a => LangOptions a -> LangConf

type EnvDescr a = (String, String -> a)

-- Type of the [simulate] method
type Simulate sym a = IsSymInterface sym =>
    [GenericExecutionFeature sym]
    -> Options a           -- ^ crux & lang-specific options
    -> sym
    -> Model sym
    -> IO (Result sym)


class (Typeable a) => Language a where

  -- name of the language
  name :: String

  -- extensions (must be non-empty)
  validExtensions :: [String]

  -- additional options for this language
  -- (a data family, so must be instantiated by a data type declaration in each instance)
  data LangOptions a :: *

  -- all language-specific options must have default values
  defaultOptions :: LangOptions a

  -- set language-specific options from the commandline
  cmdLineOptions :: [OptDescr (LangOptions a -> LangOptions a)]
  cmdLineOptions = []

  -- set language-specific options using the environment
  envOptions :: [EnvDescr (LangOptions a -> LangOptions a)]
  envOptions = []

  -- set options using IO monad
  -- (and do any necessary preprocessing)
  -- this function also has access to the crux options.
  -- All options should be set at the end of this function
  ioOptions :: Options a -> IO (Options a)
  ioOptions = return

  -- how to display language-specfic errors during simulation
  type LangError a ::  *
  formatError :: LangError a -> String

  -- simulation function, see above for interface
  simulate :: (?outputConfig :: OutputConfig) => Simulate sym a

  -- use the result of the simulation function
  makeCounterExamples :: (?outputConfig :: OutputConfig) => Options a -> Maybe (ProvedGoals (Either AssumptionReason SimError)) -> IO ()
  makeCounterExamples _opts _proved = return ()

-- Trivial instance of the class
-- For demonstration purposes only.
data Trivial = Trivial
instance Language Trivial where
  name = "trivial"
  validExtensions = [".triv"]
  type LangError Trivial = ()
  formatError () = ""
  data LangOptions Trivial = TrivialOptions
  defaultOptions = TrivialOptions
  simulate _opts _sym _s = error "TRIVIAL"
