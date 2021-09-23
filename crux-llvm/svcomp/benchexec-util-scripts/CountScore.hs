#!/usr/bin/env cabal
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{- cabal:
build-depends: base
             , bytestring
             , bzlib
             , extra
             , filepath
             , Glob
             , optparse-applicative
             , parsec
             , text
             , xml
-}
{-# OPTIONS_GHC -Wall #-}
module Main (main) where

import Codec.Compression.BZip (decompress)
import qualified Data.ByteString.Lazy as BL
import Data.Foldable
import qualified Data.List.Extra as L
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Options.Applicative as Options (Parser)
import Options.Applicative hiding (Parser)
import System.Exit (ExitCode(..))
import System.FilePath ((</>))
import System.FilePath.Glob
import Text.Parsec
import Text.XML.Light
import Text.XML.Light.Cursor

data Options = Options
  { bz2File :: FilePath
  , setBlacklist :: [FilePath]
  } deriving stock Show

optionsParser :: Options.Parser Options
optionsParser = Options
  <$> strArgument
      (  metavar "FILE"
      <> help "The .bz2 file with the results of a benchexec run" )
  <*> csListOption
      (  long "set-blacklist"
      <> value []
      <> help "Do not include results from these .set files" )

-- | Comma-separated lists of arguments.
csListOption :: Mod OptionFields String -> Options.Parser [String]
csListOption flags = splitAtElement ',' <$> strOption flags

splitAtElement :: Eq a => a -> [a] -> [[a]]
splitAtElement x l =
  case l of
    []          -> []
    e:es | e==x -> split' es
    es          -> split' es
  where
    split' es = let (esx,esxs) = break (x==) es
                in esx : splitAtElement x esxs

main :: IO ()
main = execParser opts >>= countScoreBZ2
  where
    opts = info (optionsParser <**> helper)
      ( fullDesc
     <> progDesc spiel
     <> header spiel )

    spiel = "Compute the scores in a benchexec run"

countScoreBZ2 :: Options -> IO ()
countScoreBZ2 opts@Options{bz2File} = do
  bz2BS <- BL.readFile bz2File
  countScoreXML opts $ parseXML $ decompress bz2BS

data Verdict
  = VerdictTrue
  | VerdictFalse
  | VerdictUnknown
  deriving stock (Eq, Show)

data Result
  = ResultCorrect Bool
  | ResultCorrectUnconfirmed Bool
  | ResultIncorrect Bool
  | ResultUnknown
  deriving stock (Eq, Show)

resultCorrectMaybe :: Result -> Maybe Bool
resultCorrectMaybe (ResultCorrect b)          = Just b
resultCorrectMaybe ResultCorrectUnconfirmed{} = Nothing
resultCorrectMaybe ResultIncorrect{}          = Nothing
resultCorrectMaybe ResultUnknown              = Nothing

resultCorrectUnconfirmedMaybe :: Result -> Maybe Bool
resultCorrectUnconfirmedMaybe (ResultCorrectUnconfirmed b) = Just b
resultCorrectUnconfirmedMaybe ResultCorrect{}              = Nothing
resultCorrectUnconfirmedMaybe ResultIncorrect{}            = Nothing
resultCorrectUnconfirmedMaybe ResultUnknown                = Nothing

resultIncorrectMaybe :: Result -> Maybe Bool
resultIncorrectMaybe (ResultIncorrect b)        = Just b
resultIncorrectMaybe ResultCorrect{}            = Nothing
resultIncorrectMaybe ResultCorrectUnconfirmed{} = Nothing
resultIncorrectMaybe ResultUnknown              = Nothing

isResultUnknown :: Result -> Bool
isResultUnknown ResultUnknown              = True
isResultUnknown ResultCorrect{}            = False
isResultUnknown ResultCorrectUnconfirmed{} = False
isResultUnknown ResultIncorrect{}          = False

data Category
  = CategoryCorrect
  | CategoryCorrectUnconfirmed
  | CategoryWrong
  | CategoryUnknown
  | CategoryError
  -- | CategoryMissing
  deriving stock (Eq, Show)

data Run = Run
  { runName            :: FilePath
  , runFile            :: FilePath
  , runPropertyFile    :: FilePath
  , runExpectedVerdict :: Verdict
  , runStatus          :: Verdict
  , runCategory        :: Category
  } deriving stock Show

data ValidationResult = ValidationResult
  { vrRun      :: Run
  , vrExitCode :: ExitCode
  } deriving stock Show

data CDataModel = ILP32 | LP64
 deriving stock (Eq, Show)

runFromElement_maybe :: Element -> Maybe Run
runFromElement_maybe e =
  let mbName            = firstAttrNamed "name" e
      mbFiles           = firstAttrNamed "files" e
      mbPropertyFile    = firstAttrNamed "propertyFile" e
      mbExpectedVerdict = firstAttrNamed "expectedVerdict" e
      mbStatus          = L.firstJust (firstColumnTitled "status") (elContent e)
      mbCategory        = L.firstJust (firstColumnTitled "category") (elContent e) in
  fmap (\(name, files, propertyFile, expectedVerdict, status, category) ->
          Run{ runName            = name
             , runFile            = parseSingleFile files
             , runPropertyFile    = propertyFile
             , runExpectedVerdict = parseVerdict expectedVerdict
             , runStatus          = parseVerdict status
             , runCategory        = parseCategory category
             })
       ((,,,,,) <$> mbName <*> mbFiles <*> mbPropertyFile <*> mbExpectedVerdict <*> mbStatus <*> mbCategory)
  where
    firstAttrNamed :: String -> Element -> Maybe String
    firstAttrNamed n el = L.firstJust (attrWithKey n) (elAttribs el)

    firstColumnTitled :: String -> Content -> Maybe String
    firstColumnTitled n c =
      case contentWithElName "column" c of
        Nothing  -> Nothing
        Just col -> L.firstJust (\a -> case liftA2 (,) (attrWithKey "title" a)
                                                       (L.firstJust (attrWithKey "value") (elAttribs col)) of
                                  Just (title, val) |  title == n
                                                    -> Just val
                                  _                 -> Nothing)
                                  (elAttribs col)

parseSingleFile :: String -> FilePath
parseSingleFile s =
  case parse parser "" s of
    Left err -> error $ show err
    Right fp -> fp
  where
    parser = char '[' *> manyTill anyChar (char ']')

parseVerdict :: String -> Verdict
parseVerdict "true"                         = VerdictTrue
parseVerdict "TIMEOUT"                      = VerdictUnknown
parseVerdict "OUT OF MEMORY"                = VerdictUnknown
parseVerdict s | "false"   `L.isPrefixOf` s = VerdictFalse
               | "unknown" `L.isPrefixOf` s = VerdictUnknown
               | "ERROR"   `L.isPrefixOf` s = VerdictUnknown
               | otherwise                  = error $ "Unrecognized verdict: " ++ s

parseCategory :: String -> Category
parseCategory "correct"             = CategoryCorrect
parseCategory "correct-unconfirmed" = CategoryCorrectUnconfirmed
parseCategory "wrong"               = CategoryWrong
parseCategory "unknown"             = CategoryUnknown
parseCategory "error"               = CategoryError
parseCategory s                     = error $ "Unrecognized category: " ++ s

countScoreXML :: Options -> [Content] -> IO ()
countScoreXML Options{setBlacklist} xml = do
  blacklistPatterns <- concat <$> traverse readBlacklistPatterns setBlacklist
  case fromForest xml >>= findRec (contentHasElName "systeminfo" . current) of
    Nothing -> fail "Unexpected XML"
    Just c  -> do
      let runs = filter (runNotInPatterns blacklistPatterns)
               $ mapMaybe runFromElement_maybe
               $ mapMaybe (contentWithElName "run")
               $ rights c
          results                   = map runResult runs
          correctResults            = mapMaybe resultCorrectMaybe results
          correctUnconfirmedResults = mapMaybe resultCorrectUnconfirmedMaybe results
          incorrectResults          = mapMaybe resultIncorrectMaybe results
          unknownResults            = filter isResultUnknown results
          totalScore                = foldl' (\s r -> s + resultScore r) 0 results
          maxScore                  = foldl' (\s r -> s + runMaxScore r) 0 runs

      putStrLn $ "Statistics:\t\t\t"                ++ show (length runs) ++ " Files"
      putStrLn $ "  correct:\t\t\t"                 ++ show (length correctResults)
      putStrLn $ "    correct true:\t\t"            ++ show (length $ filter id correctResults)
      putStrLn $ "    correct false:\t\t"           ++ show (length $ filter not correctResults)
      putStrLn $ "  correct-unconfirmed:\t\t"       ++ show (length correctUnconfirmedResults)
      putStrLn $ "    correct-unconfirmed true:\t"  ++ show (length $ filter id correctUnconfirmedResults)
      putStrLn $ "    correct-unconfirmed false:\t" ++ show (length $ filter not correctUnconfirmedResults)
      putStrLn $ "  incorrect:\t\t\t"               ++ show (length incorrectResults)
      putStrLn $ "    incorrect true:\t\t"          ++ show (length $ filter id incorrectResults)
      putStrLn $ "    incorrect false:\t\t"         ++ show (length $ filter not incorrectResults)
      putStrLn $ "  unknown:\t\t\t"                 ++ show (length unknownResults)
      putStrLn $ "Score:\t\t\t\t"                   ++ show totalScore ++ " (max: " ++ show maxScore ++ ")"
  where
    runNotInPatterns :: [Pattern] -> Run -> Bool
    runNotInPatterns ps Run{runName} = not $ any (`match` runName') ps
      where
        -- Unbelievably hacky
        runName' = L.dropPrefix "../../sv-benchmarks/c/" runName

    readBlacklistPatterns :: FilePath -> IO [Pattern]
    readBlacklistPatterns setFile = do
      setFileContents <- T.readFile $ ".." </> ".." </> "sv-benchmarks" </> "c" </> setFile
      pure $ map compile $ lines $ T.unpack setFileContents

    resultScore :: Result -> Int
    resultScore (ResultCorrect   True)       = 2
    resultScore (ResultCorrect   False)      = 1
    resultScore (ResultCorrectUnconfirmed _) = 0
    resultScore (ResultIncorrect True)       = -32
    resultScore (ResultIncorrect False)      = -16
    resultScore ResultUnknown                = 0

    runMaxScore :: Run -> Int
    runMaxScore Run{runExpectedVerdict} =
      case runExpectedVerdict of
        VerdictTrue    -> 2
        VerdictFalse   -> 1
        VerdictUnknown -> 0

    runResult :: Run -> Result
    runResult Run{runExpectedVerdict, runStatus, runCategory}
      | runStatus == VerdictUnknown
      = ResultUnknown
      | runCategory == CategoryCorrect
      , runExpectedVerdict == VerdictTrue
      , runStatus == VerdictTrue
      = ResultCorrect True
      | runCategory == CategoryCorrectUnconfirmed
      , runExpectedVerdict == VerdictTrue
      , runStatus == VerdictTrue
      = ResultCorrectUnconfirmed True
      | runCategory == CategoryWrong
      , runExpectedVerdict == VerdictTrue
      , runStatus == VerdictFalse
      = ResultIncorrect False
      | runCategory == CategoryCorrect
      , runExpectedVerdict == VerdictFalse
      , runStatus == VerdictFalse
      = ResultCorrect False
      | runCategory == CategoryCorrectUnconfirmed
      , runExpectedVerdict == VerdictFalse
      , runStatus == VerdictFalse
      = ResultCorrectUnconfirmed False
      | runCategory == CategoryWrong
      , runExpectedVerdict == VerdictFalse
      , runStatus == VerdictTrue
      = ResultIncorrect True
      | otherwise
      = error $ "Invalid combination: "
            ++ unwords [show runExpectedVerdict, show runStatus, show runCategory]

contentHasElName :: String -> Content -> Bool
contentHasElName n = isJust . contentWithElName n

contentWithElName :: String -> Content -> Maybe Element
contentWithElName n c = case c of
  Elem e |  qName (elName e) == n
         -> Just e
  _      -> Nothing

attrWithKey :: String -> Attr -> Maybe String
attrWithKey n a | qName (attrKey a) == n
                = Just (attrVal a)
                | otherwise
                = Nothing
