-- | Command line interface to crucible-jvm
--
-- Currently this executable works as a simulator for Java classes.
-- It expects a static method "main" that takes no arguments and
-- returns an int result. It then executes the method and prints out
-- the result in hex.

-- TODO: set this up so we can make it run test cases

{-# Language TypeFamilies #-}
{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language FlexibleContexts #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Main where

import Data.String(fromString)
import qualified Data.Map as Map
import Control.Lens((^.))
import Control.Monad.ST
import Control.Monad
import Control.Monad.State.Strict

import Control.Exception(SomeException(..),displayException)
import Data.List

import System.Console.GetOpt
import System.IO
import System.Environment(getProgName,getArgs)
import System.FilePath(takeExtension,takeBaseName)
import System.FilePath(splitSearchPath)

import Data.Parameterized.Nonce(withIONonceGenerator)
import Data.Parameterized.Some(Some(..))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF

-- crucible/crucible
import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(SomeCFG(..), AnyCFG(..), cfgArgTypes)
import Lang.Crucible.FunctionHandle

import Lang.Crucible.Simulator hiding (executeCrucible)
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.RegMap


-- crucible/what4
import What4.ProgramLoc
import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

-- jvm-verifier
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J

-- crux
import qualified Crux.Types    as Crux
import qualified Crux.Language as Crux
import qualified Crux.CruxMain as Crux
import qualified Crux.Options  as Crux


import qualified Lang.JVM.Codebase as JCB

import           Lang.Crucible.JVM.Translation
import           Lang.Crucible.JVM.Types

-- executable

import System.Console.GetOpt

-- | A simulator context
type SimCtxt sym = SimContext (Crux.Model sym) sym JVM


instance Crux.Language JVM where
  type LangError JVM = ()
  formatError _ = ""

  -- command line options specific to crux-jvm
  data LangOptions JVM =  JVMOptions
    { classPath        :: [FilePath]
      -- ^ where to look for the class path
    , jarList          :: [FilePath]
      -- ^ additional jars to use when evaluating jvm code
      -- this must include rt.jar from the JDK
      -- (The JDK_JAR environment variable can also be used to
      -- to specify this JAR).
    , mainMethod       :: String
    }

  defaultOptions =
    JVMOptions
    { classPath  = ["."]
    , jarList    = []
    , mainMethod = "main"
    }

  cmdLineOptions = [
    Option "c" ["classpath"]
    (ReqArg
     (\p opts -> opts { classPath = classPath opts ++ splitSearchPath p })
     "path"
    )
    Crux.pathDesc
    , Option "j" ["jars"]
    (ReqArg
     (\p opts -> opts { jarList = jarList opts ++ splitSearchPath p })
     "path"
    )
    Crux.pathDesc
    ,  Option "m" ["method"]
    (ReqArg
     (\p opts -> opts { mainMethod = p })
     "method name"
    )
    "Method to similate"
    ]

  envOptions   = [("JDK_JAR", \ p os -> os { jarList = p : jarList os })]


  name = "jvm"
  validExtensions = [".java"]
  
  simulate feats (copts,opts) sym ext = do
     let file = Crux.inputFile copts
     let verbosity = Crux.simVerbose copts
     
     cb <- JCB.loadCodebase (jarList opts) (classPath opts)

     let cname = takeBaseName file
     let mname = mainMethod opts

     -- create a null array of strings for `args`
     -- TODO: figure out how to allocate an empty array
     let nullstr = RegEntry refRepr W4.Unassigned
     let regmap = RegMap (Ctx.Empty `Ctx.extend` nullstr)

     Crux.Result <$> executeCrucibleJVMCrux @UnitType feats cb verbosity sym
       ext cname mname regmap
       


    

-- | Entry point, parse command line opions
main :: IO ()
main = Crux.main [Crux.LangConf (Crux.defaultOptions @JVM)]

