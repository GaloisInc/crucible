{-# LANGUAGE OverloadedStrings #-}

module Crux.Config.Doc (configDocs) where

import Config.Schema (sectionsSpec,generateDocs)
import Data.Text (Text)
import Prettyprinter
import SimpleGetOpt (usageString)

import Crux.Config
import Crux.Config.Load (commandLineOptions)

configDocs :: Text -> Config opts -> Doc ann
configDocs nm cfg =
  vcat [ heading "Command line flags:"
       , nest 2 (pretty $ usageString (commandLineOptions cfg))
       , envVarDocs cfg
       , heading "Configuration file format:"
       , nest 2 (viaShow $ generateDocs (sectionsSpec nm (cfgFile cfg)))
       ]

envVarDocs :: Config a -> Doc ann
envVarDocs cfg
  | null vs = mempty
  | otherwise = vcat [ heading "Environment variables:"
                     , nest 2 (vcat (map pp vs))
                     ]
    where
    vs = cfgEnv cfg
    m  = maximum (map (length . evName) vs)
    pp v = pretty (n ++ replicate (1 + m - length n) ' ') <+> (pretty $ evDoc v)
      where n = evName v

heading :: String -> Doc ann
heading x = vcat [ mempty
                 , pretty x
                 , pretty (replicate (length x) '=')
                 , mempty ]
