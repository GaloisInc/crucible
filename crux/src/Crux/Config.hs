{-# Language MultiWayIf, OverloadedStrings #-}
-- | This module deals with loading configurations.
module Crux.Config
  ( -- * Writing confugrations
    Config(..), cfgJoin

    -- ** Configuration files
  , SectionsSpec, section, sectionMaybe
  , yesOrNoSpec, stringSpec, numSpec, fractionalSpec
  , oneOrList, fileSpec, dirSpec

    -- ** Environment vairables
  , EnvDescr(..), mapEnvDescr

    -- ** Command line options
  , OptDescr(..), ArgDescr(..), OptSetter
  , mapOptDescr, mapArgDescr
  ) where

import Data.Text (Text)
import Data.Maybe (fromMaybe)

import SimpleGetOpt
import Config.Schema

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

-- | How the value of an environment variable contributes to the options.
data EnvDescr opts =
  EnvVar { evName  :: String                   -- ^ Name of variable
         , evDoc   :: String                   -- ^ Documentation
         , evValue :: String -> OptSetter opts -- ^ How it affects the options
         }


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

--------------------------------------------------------------------------------


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

--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

mapEnvDescr :: (OptSetter a -> OptSetter b) -> EnvDescr a -> EnvDescr b
mapEnvDescr f e = e { evValue = f . evValue e }

mapArgDescr :: (OptSetter a -> OptSetter b) -> ArgDescr a -> ArgDescr b
mapArgDescr g ad =
  case ad of
    NoArg os   -> NoArg (g os)
    ReqArg s f -> ReqArg s (g . f)
    OptArg s f -> OptArg s (g . f)

mapOptDescr :: (OptSetter a -> OptSetter b) -> OptDescr a -> OptDescr b
mapOptDescr f o = o { optArgument = mapArgDescr f (optArgument o) }


