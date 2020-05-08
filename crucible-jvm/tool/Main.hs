-- | Command line interface to crucible-jvm
--
-- Currently this executable works as a simulator for Java classes.
-- It expects a static method "main" that takes no arguments and
-- returns an int result. It then executes the method and prints out
-- the result in hex.

-- TODO: set this up so we can make it run test cases

{-# Language OverloadedStrings #-}
{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# Language ImplicitParams #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Main where

import Data.String(fromString)
import qualified Data.Sequence as Seq
import qualified Data.Map as Map
import Control.Lens((^.), (&), (%~))
import Control.Monad.ST
import Control.Monad
import Control.Monad.State.Strict

import Control.Exception(SomeException(..),displayException,catch)
import Data.List

import System.Console.GetOpt
import System.IO
import System.Environment(getProgName,getArgs)
import System.Exit (ExitCode(..), exitWith, exitFailure)
import System.FilePath(takeExtension,takeBaseName)
import System.FilePath(splitSearchPath)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle
import Lang.Crucible.ProgramLoc
import Lang.Crucible.Types

import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.PathSplitting
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.RegMap

-- what4
import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

-- jvm-verifier
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J

-- crux
import qualified Crux
import qualified Crux.Log     as Crux
import qualified Crux.Model   as Crux
import qualified Crux.Types   as Crux
import qualified Crux.Config.Common as Crux


import qualified Lang.JVM.Codebase as JCB

import           Lang.Crucible.JVM.Simulate (setupCrucibleJVMCrux)
import           Lang.Crucible.JVM.Types

-- executable

import System.Console.GetOpt

-- | A simulator context
type SimCtxt sym = SimContext (Crux.Model sym) sym JVM

data JVMOptions = JVMOptions
  { classPath        :: [FilePath]
    -- ^ where to look for the class path
  , jarList          :: [FilePath]
    -- ^ additional jars to use when evaluating jvm code
    -- this must include rt.jar from the JDK
    -- (The JDK_JAR environment variable can also be used to
    -- to specify this JAR).
  , mainMethod       :: String
  }

defaultOptions :: JVMOptions
defaultOptions =
  JVMOptions
  { classPath  = ["."]
  , jarList    = []
  , mainMethod = "main"
  }

cruxJVMConfig :: Crux.Config JVMOptions
cruxJVMConfig = Crux.Config
  { Crux.cfgFile = pure defaultOptions
  , Crux.cfgEnv =
      [ Crux.EnvVar "JDK_JAR"
        "Path to .jar file containing the JDK"
        $ \p opts -> Right $ opts { jarList = p : jarList opts }
      ]
  , Crux.cfgCmdLineFlag =
      [ Crux.Option ['c'] ["classpath"]
        "TODO"
        $ Crux.ReqArg "TODO"
        $ \p opts ->
            Right $ opts { classPath = classPath opts ++ splitSearchPath p }
      , Crux.Option ['j'] ["jars"]
        "TODO"
        $ Crux.ReqArg "TODO"
        $ \p opts ->
            Right $ opts { jarList = jarList opts ++ splitSearchPath p }
      , Crux.Option ['m'] ["method"]
        "Method to simulate"
        $ Crux.ReqArg "method name"
        $ \p opts -> Right $ opts { mainMethod = p }
      ]
  }

simulateJVM :: Crux.CruxOptions -> JVMOptions -> Crux.SimulatorCallback
simulateJVM copts opts = Crux.SimulatorCallback $ \sym _maybeOnline -> do
   let files = Crux.inputFiles copts
   let verbosity = Crux.simVerbose copts
   file <- case files of
             [file] -> return file
             _ -> fail "crux-jvm requires a single file name as an argument"

   cb <- JCB.loadCodebase (jarList opts) (classPath opts)

   let cname = takeBaseName file
   let mname = mainMethod opts

   -- create a null array of strings for `args`
   -- TODO: figure out how to allocate an empty array
   let nullstr = RegEntry refRepr W4.Unassigned
   let regmap = RegMap (Ctx.Empty `Ctx.extend` nullstr)

   initSt <- setupCrucibleJVMCrux @UnitType cb verbosity sym Crux.emptyModel
     cname mname regmap

   return $ Crux.RunnableState $ initSt


-- | Entry point, parse command line opions
main :: IO ()
main =
  Crux.loadOptions Crux.defaultOutputConfig "crux-jvm" "0.1" cruxJVMConfig $
    \(cruxOpts, jvmOpts) ->
      exitWith =<< Crux.postprocessSimResult cruxOpts =<<
        Crux.runSimulator cruxOpts (simulateJVM cruxOpts jvmOpts)
