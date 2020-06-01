-- | This module provides various helper functionality
--   for participating in the SV-COMP comptetion, including
--   parsing comptetion set files, configuration data,
--   reporting results, etc.

{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Crux.SVCOMP where

import           Config.Schema
import           Control.Applicative
import           Control.Monad
import qualified Data.Attoparsec.Text as Atto
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import qualified Data.Yaml as Yaml
import           System.FilePath
import qualified System.FilePath.Glob as Glob
import qualified Data.HashMap.Strict as HM
import qualified Data.Vector as V

import Crux.Config
import Crux.Config.Common
import Crux.Log


data SVCOMPOptions = SVCOMPOptions
  { svcompBlacklist :: [FilePath]
      -- ^ Benchmarks to skip when evaluating in SV-COMP mode

  , svcompMemlimit :: Maybe Integer
      -- ^ total memory usage limit (in MB) per verification task

  , svcompCPUlimit :: Maybe Integer
      -- ^ CPU time limit (in seconds) per verification task

  , svcompOutputFile :: FilePath
      -- ^ file path for JSON verification results output
  }

svcompOptions :: Config SVCOMPOptions
svcompOptions = Config
  { cfgFile =
      do svcompBlacklist <-
           section "svcomp-blacklist" (listSpec stringSpec) []
           "SV-COMP benchmark tasks to skip"

         svcompMemlimit <-
           sectionMaybe "svcomp-memlimit" numSpec
           "total memory usage limit (in MB) per verification task"

         svcompCPUlimit <-
           sectionMaybe "svcomp-cpulimit" numSpec
           "total CPU time limit (in seconds) per verification task"

         svcompOutputFile <-
           section "svcomp-output" fileSpec "svcomp.json"
           "output file path for JSON verification results output"

         return SVCOMPOptions{ .. }

  , cfgEnv = []

  , cfgCmdLineFlag = []
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

data BenchmarkSet =
  BenchmarkSet
  { benchmarkName :: Text
  , benchmarkDescription :: Text
  , benchmarkArchWidth   :: Maybe Int
  , benchmarkTasks :: [VerificationTask]
  }
 deriving Show

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
 deriving Show

data VerificationTask =
  VerificationTask
  { verificationSourceFile :: FilePath
  , verificationInputFiles :: [FilePath]
  , verificationProperties :: [(SVCompProperty, Maybe Bool)]
  }
 deriving Show

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

cfgParse :: Atto.Parser (Text, Maybe Int)
cfgParse =
  do d <- parseDesc
     arch <- (Just <$> parseArch) <|> return Nothing
     return (d, arch)
 where
 sp = Atto.skipWhile Atto.isHorizontalSpace

 parseDesc =
   do void $ Atto.string "Description:"
      sp
      d <- Atto.takeTill Atto.isEndOfLine
      Atto.endOfLine
      return d

 parseArch =
   do void $ Atto.string "Architecture:"
      sp
      w <- Atto.decimal
      sp
      void $ Atto.string "bit"
      sp
      Atto.endOfLine
      return w

loadVerificationTask :: FilePath -> IO VerificationTask
loadVerificationTask fp =
   Yaml.decodeFileEither fp >>= \case
     Left err -> fail $ unlines ["Failure parsing YAML file: " ++ show fp, show err]
     Right a  -> decodeVT a
 where
 decodeVT :: Yaml.Value -> IO VerificationTask
 decodeVT (Yaml.Object o) =
  do case HM.lookup "format_version" o of
       Just (Yaml.String "1.0") -> return ()
       _ -> fail $ unwords ["Expected verification task version 1.0 while parsing", show fp]

     fs <- case HM.lookup "input_files" o of
             Just v -> getStrs v
             Nothing -> fail $ unwords ["No 'input_files' section while parsing", show fp]

     ps <- case HM.lookup "properties" o of
             Just v -> getProps v
             Nothing -> fail $ unwords ["No 'properties' section while parsing", show fp]

     return VerificationTask
            { verificationSourceFile = fp
            , verificationInputFiles = fs
            , verificationProperties = ps
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
   do propf <- case HM.lookup "property_file" o of
                 Just (Yaml.String f) -> return (Text.unpack f)
                 _ -> fail $ unwords ["expected string value in 'property_file' while parsing", show fp]

      prop <- decodeProp =<< Text.readFile (takeDirectory fp </> propf)

      verdict <- case HM.lookup "expected_verdict" o of
                   Nothing -> return Nothing
                   Just (Yaml.Bool b) -> return (Just b)
                   Just (Yaml.String "true") -> return (Just True)
                   Just (Yaml.String "false") -> return (Just False)
                   Just _ -> fail $ unwords ["expected boolean value in 'expected_verdict' while parsing", show fp]

      return (prop, verdict)

 getProp _v = fail $ unwords ["expected object in 'properties' section when parsing", show fp]

 getProps (Yaml.Array xs) = mapM getProp (V.toList xs)
 getProps _v = fail $ unwords ["expected property array in 'properties' section when parsing", show fp]


compilePats :: [Text] -> [Glob.Pattern]
compilePats xs =
  let xs' = filter (not . Text.null) $ map Text.strip xs
   in map (Glob.compile . Text.unpack) xs'

loadSVCOMPBenchmarks :: Logs => CruxOptions -> IO [BenchmarkSet]
loadSVCOMPBenchmarks cruxOpts = mapM loadBenchmarkSet (inputFiles cruxOpts)

loadBenchmarkSet :: FilePath -> IO BenchmarkSet
loadBenchmarkSet fp =
  do let dir  = takeDirectory fp
         base = takeBaseName fp
         cfg  = dir </> base <> ".cfg"
         set  = dir </> base <> ".set"

     (desc, arch) <- either fail return =<< (Atto.parseOnly cfgParse <$> Text.readFile cfg)
     pats <- compilePats . Text.lines <$> Text.readFile set
     fs <- concat <$> Glob.globDir pats dir
     tasks <- mapM loadVerificationTask fs

     return BenchmarkSet
            { benchmarkName = Text.pack base
            , benchmarkDescription = desc
            , benchmarkArchWidth = arch
            , benchmarkTasks = tasks
            }
