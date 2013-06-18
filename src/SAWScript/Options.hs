{-# LANGUAGE CPP #-}
module SAWScript.Options where

import System.Console.GetOpt
import System.Environment
import System.FilePath

data Options = Options
  { importPath :: [FilePath]
  , classPath  :: [FilePath]
  , jarList    :: [FilePath]
  , verbLevel  :: Int
  } deriving (Show)

defaultOptions :: Options
defaultOptions
  = Options {
      importPath = []
    , classPath = ["."]
    , jarList = []
    , verbLevel = 1
    }

options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"] (NoArg id) "Print this help message"
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
  , Option "v" ["verbose"]
    (ReqArg
     (\v opts -> opts { verbLevel = read v })
     "num"
    )
    "Set verbosity level"
  ]

processEnv :: Options -> IO Options
processEnv opts = do
  env <- getEnvironment
  return $ foldr addOpt opts env
    where addOpt ("SAW_IMPORT_PATH", p) os =
            os { importPath = importPath os ++ splitSearchPath p }
          addOpt _ os = os

pathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
pathDesc = "Semicolon-delimited list of paths"
pathDelim = ";"
#else
pathDesc = "Colon-delimited list of paths"
pathDelim = ":"
#endif
