{- |
Module      : Options
Description : Datatype for command-line options.
License     : BSD3
Maintainer  : sweirich
Stability   : provisional
-}

{-# LANGUAGE CPP                 #-}

module Options where

import System.Console.GetOpt
import System.Environment
import System.FilePath
--import Text.Show.Functions ()


data Options = Options
  {
    importPath       :: [FilePath]
  , classPath        :: [FilePath]
  , jarList          :: [FilePath]
  , simVerbose       :: Int
  , showHelp         :: Bool
  , showVersion      :: Bool
  , printShowPos     :: Bool
  , outDir   :: FilePath
    -- ^ Store results in this directory
  , inputFile :: FilePath
    -- ^ The file to analyze
  }


defaultOptions :: Options
defaultOptions = Options {
    importPath = ["."]
  , classPath = ["."]
  , jarList = []
  , simVerbose = 1
  , outDir = "../"
  , inputFile = ""
  , showHelp = False
  , showVersion = False
  , printShowPos = False
  }


options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Print this help message"
  , Option "V" ["version"]
    (NoArg (\opts -> opts { showVersion = True }))
    "Show the version of the tool"
  , Option "c" ["classpath"]
    (ReqArg
     (\p opts -> opts { classPath = classPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "i" ["import-path"]
    (ReqArg
     (\p opts -> opts { importPath = importPath opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "j" ["jars"]
    (ReqArg
     (\p opts -> opts { jarList = jarList opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option [] ["output-locations"]
    (NoArg
     (\opts -> opts { printShowPos = True }))
     "Show the source locations that are responsible for output."
  , Option "d" ["sim-verbose"]
    (ReqArg
     (\v opts -> opts { simVerbose = read v })
     "num"
    )
    "Set simulator verbosity level"
  ]


processEnv :: Options -> IO Options
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addOpt opts curEnv
    where addOpt ("IMPORT_PATH", p) os =
            os { importPath = importPath os ++ splitSearchPath p }
          addOpt ("JDK_JAR", p) os = os { jarList = p : jarList opts }
          addOpt _ os = os


pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
