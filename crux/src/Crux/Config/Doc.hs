{-# LANGUAGE OverloadedStrings #-}

module Crux.Config.Doc (configDocs) where

import           Config.Schema (sectionsSpec,generateDocs)
import           Data.Function ( on )
import qualified Data.List as L
import           Data.Text ( Text )
import qualified Data.Text as T
import           Prettyprinter
import           Prettyprinter.Util ( reflow )
import           SimpleGetOpt ( OptSpec(..) )

import           Crux.Config
import           Crux.Config.Load (commandLineOptions)

configDocs :: Text -> Config opts -> Doc ann
configDocs nm cfg =
  vcat [ heading "Command line flags:"
       , indent 2 $ cmdLineDocs $ commandLineOptions cfg
       , envVarDocs cfg
       , heading "Configuration file format:"
       , nest 2 (viaShow $ generateDocs (sectionsSpec nm (cfgFile cfg)))
       ]

cmdLineDocs :: OptSpec a -> Doc ann
cmdLineDocs opts =
  vcat [ nest 2 $ vcat $ "Parameters:" : ppParams
       , mempty
       , nest 2 $ vcat $ "Flags:" : ppFlags
       ]
  where
    ppParams = let maxLen = maximum $ (length . fst) <$> progParamDocs opts
               in map (ppParam maxLen) $ progParamDocs opts
    ppParam l (n,d) = let pad = max 0 $ l - length d
                      in hcat [ pretty n
                              , pretty $ T.replicate (pad + 4) " "
                              , nest 2 $ reflow $ T.pack d ]
    ppFlags = let flagset = fmap ppFlag $ L.sortBy (compare `on` optSort)  $ progOptions opts
                  optSort o = (L.sort $ optShortFlags o <> "zzzzz", L.sort $ optLongFlags o)
                  lengths = fmap (maximum . fmap T.length) $ L.transpose flagset
                  textLen (l,t) = let f = T.replicate (max 0 $ l - T.length t) " " in t <> f
                  sizedCols = fmap (fmap textLen . zip lengths) $ flagset
                  padLast = align . reflow
                  prettyLine = hcat . fst . foldr (\c (p,g) -> (g c : space : p, pretty)) ([], padLast)
              in fmap prettyLine sizedCols
    ppFlag :: OptDescr a -> [Text]
    ppFlag od = let sfs = if null (optShortFlags od) then ""
                          else let each =
                                     let f = case optArgument od of
                                            NoArg _ -> T.singleton
                                            ReqArg a _ -> (\c -> T.singleton c <> " " <> T.pack a)
                                            OptArg a _ -> (\c -> T.singleton c <> " [" <> T.pack a <> "]")
                                     in f <$> optShortFlags od
                               in "-" <> T.intercalate ",-" each
                    lfs = if null (optLongFlags od) then ""
                          else let each =
                                     let f = case optArgument od of
                                           NoArg _ -> T.pack
                                           ReqArg a _ -> (\s -> T.pack s <> "=" <> T.pack a)
                                           OptArg a _ -> (\s -> T.pack s <> "=[" <> T.pack a <> "]")
                                     in f <$> optLongFlags od
                               in "--" <> T.intercalate ",--" each
                in [ sfs, lfs, T.pack $ optDescription od ]


envVarDocs :: Config a -> Doc ann
envVarDocs cfg
  | null vs = mempty
  | otherwise = vcat [ heading "Environment variables:"
                     , indent 2 (vcat (map pp vs))
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
