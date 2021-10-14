{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# Language DeriveGeneric, MultiWayIf, OverloadedStrings #-}
-- | This module deals with loading configurations.
module Crux.Config.Load where


import Control.Lens (set)
import Control.Monad(foldM, (<=<))
import Control.Exception(Exception(..),catch,catches,throwIO, Handler(..))
import Data.Generics.Product.Fields (field, setField)
import Data.Text (Text)
import GHC.Generics (Generic)

import System.Environment

import SimpleGetOpt
import Config
import Config.Schema
import Config.Schema.Load.Error(ErrorAnnotation(..))

import Crux.Config

-- | The result of loading a configuration.
data Options opts =
    ShowHelp {- XXX: Add help strings -} -- ^ Show help and exit
  | ShowVersion -- ^ Show version and exit
  | Options opts [FilePath]   -- ^ We loaded some options


data ColorOptions = ColorOptions
  { noColorsErr :: Bool
  , noColorsOut :: Bool
  }
  deriving (Generic)

defaultColorOptions :: ColorOptions
defaultColorOptions = ColorOptions
  { noColorsErr = False
  , noColorsOut = False
  }

allColors :: ColorOptions
allColors = ColorOptions
  { noColorsErr = False
  , noColorsOut = False
  }

noColors :: ColorOptions
noColors = ColorOptions
  { noColorsErr = True
  , noColorsOut = True
  }


-- | Command line options processed before loading the configuration file.
data EarlyConfig opts = EarlyConfig
  { showHelp      :: Bool -- ^ Describe options & quit
  , showVersion   :: Bool -- ^ Show tool version & quit
  , configFile    :: Maybe FilePath
    -- ^ Load configuratoin from here.
    -- Other command line options override the settings in the file.
  , colorOptions  :: ColorOptions
  , options       :: OptSetter opts
  , files         :: [FilePath]
  }
  deriving (Generic)


commandLineOptions :: Config opts -> OptSpec (EarlyConfig opts)
commandLineOptions cfg = OptSpec
  { progDefaults = EarlyConfig
                     { showHelp     = False
                     , showVersion  = False
                     , configFile   = Nothing
                     , colorOptions = defaultColorOptions
                     , options      = Right
                     , files        = []
                     }

  , progOptions =
      [ Option "h?" ["help"]
        "Print this help message"
        $ NoArg $ \opts -> Right opts { showHelp = True }

      , Option "V" ["version"]
        "Show the version of the tool"
        $ NoArg $ \opts -> Right opts { showVersion = True }

      , Option "" ["config"]
        "Load configuration from this file."
        $ ReqArg "FILE" $ \f opts -> Right opts { configFile = Just f }

      , Option [] ["no-colors-err"]
        "Suppress color codes in the errors"
        $ NoArg $ Right . set (field @"colorOptions" . field @"noColorsErr") True

      , Option [] ["no-colors-out"]
        "Suppress color codes in the output"
        $ NoArg $ Right . set (field @"colorOptions" . field @"noColorsOut") True

      , Option [] ["no-colors"]
        "Suppress color codes in both the output and the errors"
        $ NoArg $ Right . setField @"colorOptions" noColors

      ] ++ map (mapOptDescr delayOpt) (cfgCmdLineFlag cfg)

  , progParamDocs = [("FILES", "Input files to process.")]
  , progParams = \f opts -> Right opts { files = f : files opts }
  }


delayOpt :: OptSetter opts -> OptSetter (EarlyConfig opts)
delayOpt f opts = Right opts { options = f <=< options opts }



data ConfigFileLoc =
    NoConfgFile
  | AtPosition Position
    deriving Show

instance ErrorAnnotation ConfigFileLoc where
  displayAnnotation a =
    case a of
      NoConfgFile -> "(no configuration file)"
      AtPosition p -> displayAnnotation p

data ConfigError =
    FailedToReadFile IOError
  | FailedToParseFile ParseError
  | FailedToProcessFile (ValueSpecMismatch ConfigFileLoc)
  | InvalidEnvVar String String String -- ^ variable, value, error message
  | InvalidCommandLine [String]
    deriving Show

instance Exception ConfigError where
  displayException = ppConfigError

ppConfigError :: ConfigError -> String
ppConfigError (FailedToReadFile ioe) =
  "Failed to read config file: " ++ displayException ioe
ppConfigError (FailedToParseFile pe) =
  "Failed to parse config file: " ++ displayException pe
ppConfigError (FailedToProcessFile vsm) =
  "Failed to check config file: " ++ displayException vsm
ppConfigError (InvalidEnvVar var val msg) =
  unwords ["Environment variable", var, "has invalid value", val ++ ":",  msg]
ppConfigError (InvalidCommandLine msg) =
  unlines ("Invalid command line option:" : msg)

-- | Merges command-line options, environment variable options, and
-- configuration file options (in that order) to get the overall
-- Options configuration for running Crux. Throws 'ConfigError' on
-- failure.
loadConfig :: Text -> Config opts -> IO (ColorOptions, Options opts)
loadConfig nm cfg =
  do earlyOpts <- getOptsX (commandLineOptions cfg) `catch`
                  \(GetOptException errs) -> throwIO (InvalidCommandLine errs)
     let copts = colorOptions earlyOpts
     if | showHelp earlyOpts -> pure (copts, ShowHelp)
        | showVersion earlyOpts -> pure (copts, ShowVersion)
        | otherwise ->
          do opts  <- fromFile nm cfg (configFile earlyOpts)
             opts1 <- foldM fromEnv opts (cfgEnv cfg)
             case options earlyOpts opts1 of
               Left err    -> throwIO (InvalidCommandLine [err])
               Right opts2 -> pure (copts, Options opts2 (reverse (files earlyOpts)))


-- | Load settings from a file, or from an empty configuration value.
fromFile :: Text -> Config opts -> Maybe FilePath -> IO opts
fromFile nm cfg mbFile =
  do let spec = sectionsSpec nm (cfgFile cfg)
     case mbFile of

       Nothing -> -- no file, use an empty value
         case loadValue spec (Sections NoConfgFile []) of
           Left err -> throwIO (FailedToProcessFile err)
           Right opts -> pure opts

       Just file ->
        loadValueFromFile spec file
           `catches` [ Handler (throwIO . FailedToReadFile)
                     , Handler (throwIO . FailedToParseFile)
                     , Handler (throwIO . FailedToProcessFile)
                     ]


-- | Modify the options using an environment variable.
fromEnv :: opts -> EnvDescr opts -> IO opts
fromEnv opts v =
  do mb <- lookupEnv (evName v)
     case mb of
       Just s -> case evValue v s opts of
                   Right opts1 -> pure opts1
                   Left err    -> throwIO (InvalidEnvVar (evName v) s err)
       Nothing -> pure opts
