{-# Language ExistentialQuantification #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language UndecidableInstances #-}
{-# Language TypeApplications #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}

module Crux.Language where

import System.Console.GetOpt
import Lang.Crucible.Simulator
import Lang.Crucible.Types
import qualified Lang.Crucible.CFG.Core as C

import qualified What4.InterpretedFloatingPoint        as W4
import           Lang.Crucible.Backend
import qualified What4.Interface                       as W4

import Data.Typeable(Typeable)

import Crux.Types

type Verbosity = Int

-- | Default options for command-line crux programs
-- These options can be set using command-line flags and environment
-- variables.
-- They can also be extended on a per-language basis
data CruxOptions = CruxOptions
  {
    importPath       :: [FilePath]
  , simVerbose       :: Verbosity
  , showHelp         :: Bool
  , showVersion      :: Bool
  , printShowPos     :: Bool
  , outDir           :: FilePath
    -- ^ store results in this file
  , inputFile        :: FilePath
    -- ^ the file to analyze
  }


type Options a = (CruxOptions, LangOptions a)

-- A language configuration consists of an instantiation of
-- the Crux.Language type class, as well as the values of
-- language specific options for a particular run.
-- SCW: This is totally an object.
data LangConf where
  LangConf :: forall a. Language a => LangOptions a -> LangConf

type EnvDescr a = (String, String -> a)


class (Typeable a) => Language a where

  -- name of the language
  name :: String
  -- extensions
  validExtensions :: [String]
  
  -- additional options for this language
  -- (a data family, so must be instantiated by a data type declaration in each instance)
  data LangOptions a :: *

  -- all language-specific options must have default values
  defaultOptions :: LangOptions a
  -- set options from the commandline
  cmdLineOptions :: [OptDescr (LangOptions a -> LangOptions a)]
  -- set options using the environment
  envOptions     :: [EnvDescr (LangOptions a -> LangOptions a)]
  -- set options using IO monad
  -- (and do any necessary preprocessing)
  -- this function also has access to the crux options.
  -- All options should be set at the end of this function
  ioOptions :: Options a -> IO (Options a)
  
  -- how to display language-specfic errors during simulation
  type LangError a ::  *
  formatError :: LangError a -> String

  -- simulation function
  simulate :: (IsBoolSolver sym, W4.IsSymExprBuilder sym, W4.IsInterpretedFloatSymExprBuilder sym,
      W4.SymInterpretedFloatType sym W4.SingleFloat ~ C.BaseRealType,
      W4.SymInterpretedFloatType sym W4.DoubleFloat ~ C.BaseRealType) =>    
    Options a
    -> sym
    -> Model sym
    -> String
    -> IO (Result sym)

  makeCounterExamples :: Options a -> Maybe ProvedGoals -> IO ()

-- Trivial instance of the class
-- For demonstration purposes only. 
data Trivial = Trivial

instance Language Trivial where
  name = "trivial"
  validExtensions = []
  type LangError Trivial = ()
  formatError _ = "()"
  data LangOptions Trivial = TrivialOptions
  defaultOptions = TrivialOptions
  cmdLineOptions = []
  envOptions     = []
  ioOptions      = return 
  simulate _opts _sym _s = error "TRIVIAL"
  makeCounterExamples _opts _proved = return ()
