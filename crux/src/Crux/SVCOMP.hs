-- | This module provides various helper functionality
--   for participating in the SV-COMP comptetion, including
--   parsing comptetion set files, configuration data,
--   reporting results, etc.

{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Crux.SVCOMP where

import           Config.Schema
import           Control.Applicative
import           Data.Aeson (ToJSON)
import qualified Data.Attoparsec.Text as Atto
import           Data.Functor.Identity (Identity(..))
import           Data.Kind (Type)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Yaml as Yaml
import           GHC.Generics (Generic)
import           System.FilePath
import qualified System.FilePath.Glob as Glob
import qualified Data.Vector as V

#if MIN_VERSION_aeson(2,0,0)
import qualified Data.Aeson.KeyMap as KM
#else
import qualified Data.HashMap.Strict as HM
#endif

import Crux.Config
import Crux.Config.Common


data SVCOMPOptions (f :: Type -> Type) = SVCOMPOptions
  { svcompBlacklist :: [FilePath]
      -- ^ Benchmarks to skip when evaluating in SV-COMP mode

  , svcompArch :: f Arch
      -- ^ The architecture assumed for the verification task

  , svcompSpec :: f FilePath
      -- ^ The file containing the specification text used to verify the program. Likely a .prp file.

  , svcompWitnessOutput :: FilePath
      -- ^ Write the witness automaton to this filename
  }

data Arch = Arch32 | Arch64
  deriving (Show,Eq,Ord)

archSpec :: ValueSpec Arch
archSpec =
  (Arch32 <$ atomSpec "32bit") <!>
  (Arch64 <$ atomSpec "64bit")

parseArch :: (Arch -> opts -> opts) -> String -> OptSetter opts
parseArch mk = \txt opts ->
  case txt of
    "32bit" -> Right (mk Arch32 opts)
    "64bit" -> Right (mk Arch64 opts)
    _       -> Left "Invalid architecture"

-- | We cannot verify an SV-COMP program without knowing the architecture and
-- the specification. Unfortunately, Crux's command-line argument parser makes
-- it somewhat awkward to require certain arguments (without defaults). As a
-- hacky workaround, we parse the command-line arguments for the
-- architecture/specification as if they were optional and later check here to
-- see if they were actually provided, throwing an error if they were not
-- provided.
processSVCOMPOptions :: SVCOMPOptions Maybe -> IO (SVCOMPOptions Identity)
processSVCOMPOptions
    (SVCOMPOptions{ svcompArch, svcompSpec
                  , svcompBlacklist, svcompWitnessOutput}) = do
  svcompArch' <- process "svcomp-arch" svcompArch
  svcompSpec' <- process "svcomp-spec" svcompSpec
  pure $ SVCOMPOptions{ svcompArch = svcompArch', svcompSpec = svcompSpec'
                      , svcompBlacklist, svcompWitnessOutput }
  where
    process :: String -> Maybe a -> IO (Identity a)
    process optName = maybe (fail $ "A value for --" ++ optName ++ " must be provided") (pure . Identity)

svcompOptions :: Config (SVCOMPOptions Maybe)
svcompOptions = Config
  { cfgFile =
      do svcompBlacklist <-
           section "svcomp-blacklist" (listSpec stringSpec) []
           "SV-COMP benchmark tasks to skip"

         svcompArch <-
           sectionMaybe "svcomp-arch" archSpec
           "The architecture assumed for the verification task."

         svcompSpec <-
           sectionMaybe "svcomp-spec" fileSpec
           "The file containing the specification text used to verify the program. Likely a .prp file."

         svcompWitnessOutput <-
           section "svcomp-witness-output" fileSpec "witness.graphml"
           (Text.unwords [ "The file name to which the witness automaton file should be written"
                         , "(default: witness.graphml)."
                         ])

         return SVCOMPOptions{ .. }

  , cfgEnv = []

  , cfgCmdLineFlag =
      [ Option [] ["svcomp-arch"]
        "The architecture assumed for the verification task."
        $ ReqArg "`32bit` or `64bit`"
        $ parseArch
        $ \a opts -> opts{ svcompArch = Just a }

      , Option [] ["svcomp-spec"]
        "The file containing the specification text used to verify the program. Likely a .prp file."
        $ ReqArg "FILE"
        $ \f opts -> Right opts{ svcompSpec = Just f }

      , Option [] ["svcomp-witness-output"]
        (unwords [ "The file name to which the witness automaton file should be written"
                 , "(default: witness.graphml)."
                 ])
        $ ReqArg "FILE"
        $ \f opts -> Right opts{ svcompWitnessOutput = f }
      ]
  }

propertyVerdict :: VerificationTask -> Maybe Bool
propertyVerdict task = foldl f Nothing (verificationProperties task)
 where
 comb b Nothing  = Just b
 comb b (Just x) = Just $! b && x

 f v (CheckNoError _nm, Just b)  = comb b v
 f v (CheckValidFree, Just b)    = comb b v
 f v (CheckValidDeref, Just b)   = comb b v
 f v (CheckDefBehavior, Just b)  = comb b v
 f v (CheckNoOverflow, Just b)   = comb b v
 f v _ = v

data ComputedVerdict
  = Verified
  | Falsified
  | Unknown
 deriving (Eq, Generic, Ord, Show, ToJSON)

data BenchmarkSet =
  BenchmarkSet
  { benchmarkName :: Text
  , benchmarkTasks :: [VerificationTask]
  }
 deriving (Show,Eq,Ord)

data SVCompProperty
  = CheckNoError Text
  | CheckValidFree
  | CheckValidDeref
  | CheckValidMemtrack
  | CheckValidMemCleanup
  | CheckDefBehavior
  | CheckNoOverflow
  | CheckTerminates
  | CoverageFQL Text
 deriving (Show,Eq,Ord,Generic,ToJSON)

data SVCompLanguage
  = C CDataModel
  | Java
 deriving (Show,Eq,Ord)

data CDataModel = ILP32 | LP64
 deriving (Show,Eq,Ord)

data VerificationTask =
  VerificationTask
  { verificationSourceFile :: FilePath
  , verificationInputFiles :: [FilePath]
  , verificationProperties :: [(SVCompProperty, Maybe Bool)]
  , verificationLanguage   :: SVCompLanguage
  }
 deriving (Show,Eq,Ord)

checkParse :: Atto.Parser SVCompProperty
checkParse = Atto.skipSpace *> Atto.string "init(main())," *> Atto.skipSpace *> ltl
 where
 ltl = Atto.string "LTL(" *> Atto.skipSpace *> go <* Atto.skipSpace <* Atto.string ")" <* Atto.skipSpace
 go = Atto.choice
      [ CheckNoError <$> (Atto.string "G ! call(" *> bracketedText <* ")")
      , pure CheckTerminates      <* Atto.string "F end"
      , pure CheckValidFree       <* Atto.string "G valid-free"
      , pure CheckValidDeref      <* Atto.string "G valid-deref"
      , pure CheckValidMemtrack   <* Atto.string "G valid-memtrack"
      , pure CheckValidMemCleanup <* Atto.string "G valid-memcleanup"
      , pure CheckNoOverflow      <* Atto.string "G ! overflow"
      , pure CheckDefBehavior     <* Atto.string "G def-behavior"
      ]

coverParse :: Atto.Parser SVCompProperty
coverParse = CoverageFQL <$> (Atto.skipSpace *> Atto.string "init(main())," *> Atto.skipSpace *> bracketedText)

bracketedText :: Atto.Parser Text
bracketedText =
 do xs <- Atto.takeTill (\x -> x `elem` ['(',')'])
    (do _ <- Atto.char '('
        ys <- bracketedText
        _ <- Atto.char ')'
        zs <- bracketedText
        return (xs <> "(" <> ys <> ")" <> zs)
     ) <|> (return xs)


propParse :: Atto.Parser SVCompProperty
propParse = Atto.skipSpace *> Atto.choice
  [ Atto.string "CHECK(" *> checkParse <* ")"
  , Atto.string "COVER(" *> coverParse <* ")"
  ]

loadVerificationTask :: FilePath -> IO VerificationTask
loadVerificationTask fp =
   Yaml.decodeFileEither fp >>= \case
     Left err -> fail $ unlines ["Failure parsing YAML file: " ++ show fp, show err]
     Right a  -> decodeVT a
 where
 decodeVT :: Yaml.Value -> IO VerificationTask
 decodeVT (Yaml.Object o) =
  do case lookupKM "format_version" o of
       Just (Yaml.String "2.0") -> return ()
       _ -> fail $ unwords ["Expected verification task version 2.0 while parsing", show fp]

     fs <- case lookupKM "input_files" o of
             Just v -> getStrs v
             Nothing -> fail $ unwords ["No 'input_files' section while parsing", show fp]

     ps <- case lookupKM "properties" o of
             Just v -> getProps v
             Nothing -> fail $ unwords ["No 'properties' section while parsing", show fp]

     lang <- case lookupKM "options" o of
               Just v -> getLang v
               Nothing -> fail $ unwords ["No 'options' section while parsing", show fp]

     return VerificationTask
            { verificationSourceFile = fp
            , verificationInputFiles = fs
            , verificationProperties = ps
            , verificationLanguage   = lang
            }
 decodeVT v = fail $ unwords ["Expected Yaml object but got:", show v, "when parsing", show fp]


 decodeProp p =
   case Atto.parseOnly propParse p of
     Left msg -> fail $ unlines [ "Could not parse property:"
                                , Text.unpack p
                                , msg
                                ]

     Right p' -> return p'

 getStrs (Yaml.String f) = return [Text.unpack f]
 getStrs (Yaml.Array xs) = concat <$> V.mapM getStrs xs
 getStrs v = fail $ unwords ["expected strings, but got:", show v]

 getProp (Yaml.Object o) =
   do propf <- case lookupKM "property_file" o of
                 Just (Yaml.String f) -> return (Text.unpack f)
                 _ -> fail $ unwords ["expected string value in 'property_file' while parsing", show fp]

      prop <- decodeProp =<< Text.readFile (takeDirectory fp </> propf)

      verdict <- case lookupKM "expected_verdict" o of
                   Nothing -> return Nothing
                   Just (Yaml.Bool b) -> return (Just b)
                   Just (Yaml.String "true") -> return (Just True)
                   Just (Yaml.String "false") -> return (Just False)
                   Just _ -> fail $ unwords ["expected boolean value in 'expected_verdict' while parsing", show fp]

      return (prop, verdict)

 getProp _v = fail $ unwords ["expected object in 'properties' section when parsing", show fp]

 getProps (Yaml.Array xs) = mapM getProp (V.toList xs)
 getProps _v = fail $ unwords ["expected property array in 'properties' section when parsing", show fp]

 getLang (Yaml.Object o) =
   case lookupKM "language" o of
     Just (Yaml.String "C")    -> getCDataModel o
     Just (Yaml.String "Java") -> return Java
     _ -> fail $ unwords ["expected 'C' or 'Java' in 'language' while parsing", show fp]

 getLang _v = fail $ unwords ["expected object in 'options' section when parsing", show fp]

 getCDataModel o =
   case lookupKM "data_model" o of
     Just (Yaml.String "ILP32") -> return (C ILP32)
     Just (Yaml.String "LP64")  -> return (C LP64)
     _ -> fail $ unwords ["expected 'ILP32' or 'LP64' in 'data_model' while parsing", show fp]

 -- TODO: When the ecosystem widely uses aeson-2.0.0.0 or later, remove this CPP.
#if MIN_VERSION_aeson(2,0,0)
 lookupKM = KM.lookup
#else
 lookupKM = HM.lookup
#endif

compilePats :: [Text] -> [Glob.Pattern]
compilePats xs =
  let xs' = filter (not . Text.null) $ map Text.strip xs
   in map (Glob.compile . Text.unpack) xs'

loadSVCOMPBenchmarks :: CruxOptions -> IO [BenchmarkSet]
loadSVCOMPBenchmarks cruxOpts = mapM loadBenchmarkSet (inputFiles cruxOpts)

loadBenchmarkSet :: FilePath -> IO BenchmarkSet
loadBenchmarkSet fp =
  do let dir  = takeDirectory fp
         base = takeBaseName fp
         set  = dir </> base <> ".set"

     pats <- compilePats . Text.lines <$> Text.readFile set
     fs <- concat <$> Glob.globDir pats dir
     tasks <- mapM loadVerificationTask fs

     return BenchmarkSet
            { benchmarkName = Text.pack base
            , benchmarkTasks = tasks
            }


type TaskMap = Map VerificationTask [BenchmarkSet]

-- | There is significant overlap between the various verification tasks found in
--   different benchmark sets in the SV-COMP repository.  This operation collects
--   together all the potentially duplicated tasks found in a collection of benchmark sets
--   and places them in a map, ensuring there is at most one reference to each one.
--   The tasks are the keys of the map; the benchmark set(s) that referenced a given task
--   are stored in the elements the map.
deduplicateTasks :: [BenchmarkSet] -> TaskMap
deduplicateTasks = Map.unionsWith (++) . map f
  where
  f bs = Map.fromList
           [ (t, [bs]) | t <- benchmarkTasks bs ]
