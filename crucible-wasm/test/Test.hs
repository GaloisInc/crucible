{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Exception ( SomeException, catches, try, Handler(..), IOException )
import           Control.Lens ( (^.), (^?), _Right, to )
import           Control.Monad ( unless, when )
import           Data.Bifunctor ( first )
import qualified Data.ByteString.Lazy as BSIO
import qualified Data.ByteString.Lazy.Char8 as BSC
import           Data.Char ( isLetter, isSpace )
import           Data.List.Extra ( isInfixOf, isPrefixOf, stripPrefix )
import           Data.Maybe ( catMaybes, fromMaybe, isJust )
import qualified Data.Text as T
import           Data.Versions ( Versioning, versioning, prettyV, major )
import qualified GHC.IO.Exception as GE
import           Numeric.Natural
import           System.Environment ( withArgs, lookupEnv )
import           System.Exit (ExitCode(..))
import           System.FilePath ( (-<.>) )
import qualified System.IO as IO

import qualified Test.Tasty as TT
import           Test.Tasty.HUnit ( testCase, assertFailure )
import qualified Test.Tasty.Sugar as TS

import qualified Crux

import qualified Lang.Crucible.Wasm.Main as C


cube :: TS.CUBE
cube =
  TS.mkCUBE
  { TS.inputDirs = ["test-data/"]
  , TS.rootName = "*.wat"
  , TS.separators = "."
  , TS.expectedSuffix = "good"
  , TS.validParams =
      [ ("solver", Just ["z3"])
      ]
  , TS.associatedNames =
      [ ("config", "config")
      , ("test-result", "result")
      , ("skip", "skip")   -- when present, test config is skipped
      ]
  }

main :: IO ()
main = do
  let cubes = [ cube { TS.rootName = rootName }
              | rootName <- ["*.wasm", "*.wast", "*.wat"]
              ]
  sweets <- concat <$> mapM TS.findSugar cubes
  tests <- TS.withSugarGroups sweets TT.testGroup mkTest
  let ingredients = TT.includingOptions TS.sugarOptions :
                    TS.sugarIngredients cubes <>
                    TT.defaultIngredients
  TT.defaultMainWithIngredients ingredients $
    TT.testGroup "crucible-wasm" tests

-- Taken from crux-llvm test suite
assertBSEq :: FilePath -> FilePath -> IO ()
assertBSEq expectedFile actualFile = do
  expected <- BSIO.readFile expectedFile
  actual <- BSIO.readFile actualFile
  let el = BSC.lines expected
      al = BSC.lines actual
  unless (el == al) $ do
    let dl (e,a) = if e == a then db e else de e <> da a
        db b = ["    F        |" <> b]
        de e = ["    F-expect>|" <> e]
        da a = ["    F-actual>|" <> a]
    let details = concat $
                  [ [ "MISMATCH for expected (" <> BSC.pack expectedFile <> ")"
                    , "           and actual (" <> BSC.pack actualFile <> ") output:"
                    ]
                    -- Highly simplistic "diff" output assumes
                    -- correlated lines: added or removed lines just
                    -- cause everything to shown as different from
                    -- that point forward.
                  , concatMap dl $ zip el al
                  , concatMap de $ drop (length al) el
                  , concatMap da $ drop (length el) al
                  ]
    assertFailure $ BSC.unpack (BSC.unlines details)


mkTest :: TS.Sweets -> Natural -> TS.Expectation -> IO [TT.TestTree]
mkTest sweet _ expct =
  let solver = maybe "z3"
               (\case
                 (TS.Explicit s) -> s
                 (TS.Assumed  s) -> s
                 TS.NotSpecified -> "z3")
               $ lookup "solver" (TS.expParamsMatch expct)
      outFile = TS.expectedFile expct -<.> "." <> solver <> ".out"
      tname = TS.rootBaseName sweet
      runCruxName = tname <> " crucible-wasm run"
      resFName = outFile -<.> ".result.out"

      runCrux = Just $ testCase runCruxName $ do
        let cfargs = catMaybes
                     [
                       ("--config=" <>) <$> lookup "config" (TS.associated expct)
                     , Just $ "--solver=" <> solver
                     , Just "--quiet"
                     ]
            failureMsg = let bss = BSIO.pack . fmap (toEnum . fromEnum) . show in \case
              Left e -> "***[test]*** crucible-wasm failed with exception: " <> bss (show (e :: SomeException)) <> "\n"
              Right (ExitFailure v) -> "***[test]*** crucible-wasm failed with non-zero result: " <> bss (show v) <> "\n"
              Right ExitSuccess -> ""
        r <- IO.withFile outFile IO.WriteMode $ \h ->
          (try $
            withArgs (cfargs <> [TS.rootFile sweet]) $
            let coloredOutput = False
            in (C.mainWithOutputConfig $ Crux.mkOutputConfig (h, coloredOutput) (h, coloredOutput) Crux.cruxLogMessageToSayWhat))
        BSIO.writeFile resFName $ failureMsg r

      checkResult =
        let runTest s = testCase (tname <> " crucible-wasm result") $
                        assertBSEq s resFName
        in runTest <$> lookup "test-result" (TS.associated expct)

      checkOutput = Just $ testCase (tname <> " crucible-wasm output") $
                    assertBSEq (TS.expectedFile expct) outFile

  in do
    -- Some tests take longer, so only run one of them in fast-test mode
    testLevel <- fromMaybe "0" <$> lookupEnv "CI_TEST_LEVEL"

    let longTests = False

    -- Presence of a .skip file means this test should be skipped.
    let skipTest = isJust $ lookup "skip" (TS.associated expct)
    if or [ skipTest, testLevel == "0" && longTests ]
      then do
        when (testLevel == "0" && longTests) $
          putStrLn "*** Longer running test skipped; set CI_TEST_LEVEL=1 env var to enable"
        return []
      else
        return
          [ TT.testGroup "tests"
            [ TT.testGroup (TS.rootBaseName sweet) $ catMaybes
              [ runCrux
              , TT.after TT.AllSucceed runCruxName <$> checkResult
              , TT.after TT.AllSucceed runCruxName <$> checkOutput
              ]
            ]
          ]
