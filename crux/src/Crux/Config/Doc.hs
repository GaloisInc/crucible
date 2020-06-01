module Crux.Config.Doc (configDocs) where

import Data.Text(Text)
import Text.PrettyPrint
import Config.Schema(sectionsSpec,generateDocs)
import SimpleGetOpt(usageString)

import Crux.Config
import Crux.Config.Load(commandLineOptions)

configDocs :: Text -> Config opts -> Doc
configDocs nm cfg =
  vcat [ heading "Command line flags:"
       , nest 2 (text (usageString (commandLineOptions cfg)))
       , envVarDocs cfg
       , heading "Configuration file format:"
       , nest 2 (generateDocs (sectionsSpec nm (cfgFile cfg)))
       ]

envVarDocs :: Config a -> Doc
envVarDocs cfg
  | null vs = empty
  | otherwise = heading "Environment variables:"
                $$ nest 2 (vcat (map pp vs))
    where
    vs = cfgEnv cfg
    m  = maximum (map (length . evName) vs)
    pp v = text (n ++ replicate (1 + m - length n) ' ') <+> text (evDoc v)
      where n = evName v

heading :: String -> Doc
heading x = text " " $$ text x $$ text (replicate (length x) '=') $$ text " "


