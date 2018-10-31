{-# Language ExistentialQuantification #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}

module Crux.Language where

import System.Console.GetOpt
import Lang.Crucible.Simulator
--import Lang.Crucible.Types
import Lang.Crucible.CFG.Extension
--import qualified Lang.Crucible.CFG.Core as C


import           Lang.Crucible.Backend
--import qualified What4.Interface                       as W4
--import qualified What4.InterpretedFloatingPoint        as W4

import Data.Typeable(Typeable)

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
  , profileOutputInterval    :: Maybe String
  }

type Options a = (CruxOptions, LangOptions a)

-- A language configuration consists of an instantiation of
-- the Crux.Language type class, as well as the values of
-- language specific options for a particular run.
-- SCW: This is totally an object.
data LangConf where
  LangConf :: forall a. Language a => LangOptions a -> LangConf

type EnvDescr a = (String, String -> a)

-- Type of the executeCrucible callback argument to
--  [simulate]. Implementations of the method should use this function
--  to execute symbolic simulation (automatically with and without
--  profiling)
type ExecuteCrucible sym = (forall p ext rtp f a0.
     IsSyntaxExtension ext =>
      SimState p sym ext rtp f a0  ->
      ExecCont p sym ext rtp f a0  ->
      IO (ExecResult p sym ext rtp))

-- Gathering of constraints on the sym used by the [simulate] method
type SymConstraint sym = IsSymInterface sym
--  (IsBoolSolver sym, IsSymInterface sym)
--    W4.SymInterpretedFloatType sym W4.SingleFloat ~ C.BaseRealType,
--    W4.SymInterpretedFloatType sym W4.DoubleFloat ~ C.BaseRealType) 

-- Type of the [simulate] method
type Simulate sym a = (SymConstraint sym)  =>
    ExecuteCrucible sym    -- ^ callback to executeCrucible
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
  simulate :: Simulate sym a 

  -- use the result of the simulation function
  makeCounterExamples :: Options a -> Maybe (ProvedGoals (Either AssumptionReason SimError)) -> IO ()
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
