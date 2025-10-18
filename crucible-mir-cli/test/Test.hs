{-# LANGUAGE ImportQualifiedPost #-}

module Main (main) where

import Data.List (sort)
import Data.Text.IO qualified as T
import System.FilePath
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import What4.Solver.Z3 (z3Options)

import Lang.Crucible.CLI (simulateProgramWithExtension)

import Lang.Crucible.MIR.CLI (withMirHooks)

main :: IO ()
main = do
  simTests <- findTests "MIR simulation" "test-data" testSimulator
  defaultMain (testGroup "crucible-mir-cli" [simTests])

findTests :: String -> FilePath -> (FilePath -> FilePath -> IO ()) -> IO TestTree
findTests groupName testDir testAction =
  do inputs <- findByExtension [".cbl"] testDir
     return $ testGroup groupName
       [ goldenFileTestCase input testAction
       | input <- sort inputs
       ]

goldenFileTestCase :: FilePath -> (FilePath -> FilePath -> IO ()) -> TestTree
goldenFileTestCase input testAction =
  goldenVsFileDiff
   (takeBaseName input) -- test name
   (\x y -> ["diff", "-u", x, y])
   goodFile -- golden file path
   outFile
   (testAction input outFile) -- action whose result is tested
  where
    outFile = replaceExtension input ".out"
    goodFile = replaceExtension input ".out.good"

testSimulator :: FilePath -> FilePath -> IO ()
testSimulator inFile outFile =
  do contents <- T.readFile inFile
     withFile outFile WriteMode $ \outh ->
       withMirHooks $ \ext hooks ->
         simulateProgramWithExtension ext inFile contents outh Nothing z3Options hooks False []
