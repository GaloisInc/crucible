{- |
Module      : Crux.Options
Description : Datatype for command-line options.
License     : BSD3
Maintainer  : sweirich
Stability   : provisional
-}

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Crux.Options where

import System.Console.GetOpt
import System.Environment
import System.FilePath
--import Text.Show.Functions ()


import qualified Crux.Language as CL

data Options a = Options
  {
    importPath       :: [FilePath]
  , simVerbose       :: Int
  , showHelp         :: Bool
  , showVersion      :: Bool
  , printShowPos     :: Bool
  , outDir           :: FilePath
    -- ^ Store output report in this directory
  , inputFile        :: FilePath
    -- ^ The file to analyze
  , langOptions      :: CL.LangOptions a
    -- ^ language specific options
  }


defaultOptions :: forall a. CL.Language a => Options a
defaultOptions = Options {
    importPath = ["."]
  , simVerbose = 1
  , outDir = "report/"
  , inputFile = ""
  , showHelp = False
  , showVersion = False
  , printShowPos = False
  , langOptions = CL.defaultOptions @a
  }


promote :: (CL.LangOptions a -> CL.LangOptions a) -> (Options a -> Options a)
promote g = \ opts -> opts { langOptions = g (langOptions opts) }
  

options :: forall a. CL.Language a => [OptDescr (Options a -> Options a)]
options =
  (map (fmap promote) (CL.options @a)) ++ 
  [ Option "h?" ["help"]
    (NoArg (\opts -> opts { showHelp = True }))
    "Print this help message"
  , Option "V" ["version"]
    (NoArg (\opts -> opts { showVersion = True }))
    "Show the version of the tool"
  , Option "i" ["import-path"]
    (ReqArg
     (\p opts -> opts { importPath = importPath opts ++ splitSearchPath p })
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


processEnv :: forall a. CL.Language a => Options a -> IO (Options a)
processEnv opts = do
  curEnv <- getEnvironment
  return $ foldr addOpt opts curEnv
    where addOpt :: (String, String) -> Options a -> Options a
          addOpt ("IMPORT_PATH", p) os =
            os { importPath = importPath os ++ splitSearchPath p }
          addOpt pair os = promote (CL.addOpt @a pair) os


pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
