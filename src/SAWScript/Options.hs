{-# LANGUAGE CPP #-}
module SAWScript.Options where

import System.Console.GetOpt
import System.Environment
import System.FilePath

data Options = Options
  { importPath :: [FilePath]
  } deriving (Show)

defaultOptions :: Options
defaultOptions = Options { importPath = [] }

options :: [OptDescr (Options -> Options)]
options =
  [ Option "h?" ["help"] (NoArg id) "Print this help message"
  , Option "i" ["import-path"]
    (ReqArg
     (\p opts -> opts { importPath = importPath opts ++ splitSearchPath p })
     "path"
    )
    importPathDesc
  ]

processEnv :: Options -> IO Options
processEnv opts = do
  env <- getEnvironment
  return $ foldr addOpt opts env
    where addOpt ("SAW_IMPORT_PATH", p) os =
            os { importPath = importPath os ++ splitSearchPath p }
          addOpt _ os = os

importPathDesc, pathDelim :: String

#ifdef mingw32_HOST_OS
importPathDesc = "Semicolon-delimited list of import search directories"
pathDelim = ";"
#else
importPathDesc = "Colon-delimited list of import search directories"
pathDelim = ":"
#endif
