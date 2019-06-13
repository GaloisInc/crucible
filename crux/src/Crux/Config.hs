{-# Language MultiWayIf, OverloadedStrings #-}
-- | This module deals with loading configurations.
module Crux.Config
  ( -- * Loading configuration
    loadConfig , Options(..)

    -- ** Handling errors
  , ConfigError(..)
  , ConfigFileLoc(..)
  , ParseError(..)
  , ValueSpecMismatch(..)
  , Position(..)

    -- * Writing confugrations
  , Config(..), cfgJoin

    -- ** Configuration files
  , SectionsSpec, section, sectionMaybe
  , yesOrNoSpec, stringSpec, numSpec, fractionalSpec
  , oneOrList, fileSpec, dirSpec

    -- ** Environment vairables
  , EnvDescr(..)

    -- ** Command line options
  , OptDescr(..), ArgDescr(..), OptSetter
  ) where

import Control.Monad(foldM, (<=<))
import Control.Exception(Exception,catch,catches,throwIO, Handler(..))
import Data.Text (Text)
import Data.Maybe (fromMaybe)

import System.Environment

import SimpleGetOpt
import Config
import Config.Schema
import Config.Schema.Load.Error(ErrorAnnotation(..))

-- | The result of loading a configuration.
data Options opts =
    ShowHelp  {- XXX: Add help strings -}  -- ^ Show help and exit
  | ShowVersion               -- ^ Show version and exti
  | Options opts [FilePath]   -- ^ We loaded some options


-- | Command line options processed before loading the configuration file.
data EarlyConfig opts = EarlyConfig
  { showHelp    :: Bool -- ^ Describe options & quit
  , showVersion :: Bool -- ^ Show tool version & quit
  , configFile  :: Maybe FilePath
    -- ^ Load configuratoin from here.
    -- Other command line options override the settings in the file.

  , options     :: OptSetter opts
  , files       :: [FilePath]
  }

commandLineOptions :: Config opts -> OptSpec (EarlyConfig opts)
commandLineOptions cfg = OptSpec
  { progDefaults = EarlyConfig
                     { showHelp    = False
                     , showVersion = False
                     , configFile  = Nothing
                     , options     = Right
                     , files       = []
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
      ] ++ map (mapOptDescr delayOpt) (cfgCmdLineFlag cfg)

  , progParamDocs = [("FILES", "Input files to process.")]
  , progParams = \f opts -> Right opts { files = f : files opts }
  }


delayOpt :: OptSetter opts -> OptSetter (EarlyConfig opts)
delayOpt f opts = Right opts { options = f <=< options opts }

mapArgDescr :: (OptSetter a -> OptSetter b) -> ArgDescr a -> ArgDescr b
mapArgDescr g ad =
  case ad of
    NoArg os   -> NoArg (g os)
    ReqArg s f -> ReqArg s (g . f)
    OptArg s f -> OptArg s (g . f)

mapOptDescr :: (OptSetter a -> OptSetter b) -> OptDescr a -> OptDescr b
mapOptDescr f o = o { optArgument = mapArgDescr f (optArgument o) }


-- | An option that can be confugred in the file.
section :: Text        {- ^ Option name -} ->
           ValueSpec a {- ^ What type of value we expect -} ->
           a           {- ^ Default value to use if option not specified -} ->
           Text        {-^ Documentation -} ->
           SectionsSpec a
section nm spec def doc = fromMaybe def <$> optSection' nm spec doc

sectionMaybe :: Text {- ^ Option name -} ->
                ValueSpec a {- ^ What type of value we expect -} ->
                Text        {- ^ Documentation -} ->
                SectionsSpec (Maybe a)
sectionMaybe = optSection'

fileSpec :: ValueSpec FilePath
fileSpec = namedSpec "FILE" stringSpec

dirSpec :: ValueSpec FilePath
dirSpec = namedSpec "DIR" stringSpec




{- | Loading optoins from multiple sources.  First we load configuration
from a file, then we consider environment variable, and finally we
update using the command line flags. If there is no configuration file
provided, then this is equvalent to having an empty configuration file,
so the config file schema should be able to cope with missing settings. -}

data Config opts = Config
  { cfgFile     :: SectionsSpec opts
    -- ^ Configuration file settings (and, implcitly, defaults).

  , cfgEnv      :: [ EnvDescr opts ]
    -- ^ Settings from environment variables

  , cfgCmdLineFlag  :: [ OptDescr opts ]
    -- ^ Command line flags.
  }


-- | Join two configurations.
cfgJoin :: Config a -> Config b -> Config (a,b)
cfgJoin cfg1 cfg2 = Config
  { cfgFile         = (,) <$> cfgFile cfg1 <*> cfgFile cfg2
  , cfgEnv          = map (mapEnvDescr inFst) (cfgEnv cfg1) ++
                      map (mapEnvDescr inSnd) (cfgEnv cfg2)
  , cfgCmdLineFlag  = map (mapOptDescr inFst) (cfgCmdLineFlag cfg1) ++
                      map (mapOptDescr inSnd) (cfgCmdLineFlag cfg2)
  }


inFst :: OptSetter a -> OptSetter (a,b)
inFst f = \(a,b) -> do a' <- f a
                       pure (a',b)

inSnd :: OptSetter b -> OptSetter (a,b)
inSnd f = \(a,b) -> do b' <- f b
                       pure (a,b')

mapEnvDescr :: (OptSetter a -> OptSetter b) -> EnvDescr a -> EnvDescr b
mapEnvDescr f e = e { evValue = f . evValue e }


-- | How the value of an environment variable contributes to the options.
data EnvDescr opts = EnvDescr { evName  :: String   -- ^ Name of variable
                              , evDoc   :: String   -- ^ Documentation
                              , evValue :: String -> OptSetter opts
                                -- ^ How it affects the options
                              }

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

instance Exception ConfigError




-- | Throws 'ConfigError'
loadConfig :: Text -> Config opts -> IO (Options opts)
loadConfig nm cfg =
  do earlyOpts <- getOptsX (commandLineOptions cfg) `catch`
                  \(GetOptException errs) -> throwIO (InvalidCommandLine errs)
     if | showHelp earlyOpts -> pure ShowHelp
        | showVersion earlyOpts -> pure ShowVersion
        | otherwise ->
          do opts  <- fromFile nm cfg (configFile earlyOpts)
             opts1 <- foldM fromEnv opts (cfgEnv cfg)
             case options earlyOpts opts1 of
               Left err    -> throwIO (InvalidCommandLine [err])
               Right opts2 -> pure (Options opts2 (reverse (files earlyOpts)))


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



