{-# LANGUAGE CPP #-}
module SAWScript.Options where

import System.Console.GetOpt
import System.Environment
import System.FilePath

data Options = Options
  { importPath       :: [FilePath]
  , classPath        :: [FilePath]
  , jarList          :: [FilePath]
  , verbLevel        :: Int
  , simVerbose       :: Int
  , extraChecks      :: Bool
  , runInteractively :: Bool
  , showHelp         :: Bool
  } deriving (Show)

defaultOptions :: Options
defaultOptions
  = Options {
      importPath = ["."]
    , classPath = ["."]
    , jarList = []
    , verbLevel = 1
    , simVerbose = 1
    , extraChecks = False
    , runInteractively = False
    , showHelp = False
    }

options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Print this help message"
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
  , Option "t" ["extra-type-checking"]
    (NoArg
     (\opts -> opts { extraChecks = True }))
    "Perform extra type checking of intermediate values"
  , Option "I" ["interactive"]
    (NoArg
     (\opts -> opts { runInteractively = True }))
    "Run interactively (with a REPL)"
  , Option "j" ["jars"]
    (ReqArg
     (\p opts -> opts { jarList = jarList opts ++ splitSearchPath p })
     "path"
    )
    pathDesc
  , Option "d" ["sim-verbose"]
    (ReqArg
     (\v opts -> opts { simVerbose = read v })
     "num"
    )
    "Set simulator verbosity level"
  , Option "v" ["verbose"]
    (ReqArg
     (\v opts -> opts { verbLevel = read v })
     "num"
    )
    "Set verbosity level"
  ]

processEnv :: Options -> IO Options
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addOpt opts curEnv
    where addOpt ("SAW_IMPORT_PATH", p) os =
            os { importPath = importPath os ++ splitSearchPath p }
          addOpt ("SAW_JDK_JAR", p) os = os { jarList = p : jarList opts }
          addOpt _ os = os

pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
