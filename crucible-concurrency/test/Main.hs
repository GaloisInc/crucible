{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
module Main where

import Data.List
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath
import System.Directory
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden
import Test.Tasty.HUnit

import qualified Crux as Crux
import qualified Crux.Config.Common as Crux

import qualified Config
import qualified Config.Schema as Config

import Cruces.CrucesMain

main :: IO ()
main = do
  wd <- getCurrentDirectory
  examples <- findTests "Examples" "examples" testSimulator
  svtests <- findTests "SVComp" "sv-benchmarks" testSimulator
  let allTests = testGroup "Tests" [examples, svtests]
  defaultMain allTests

-- TODO: remove this - copy-pasted from Crux/Options.hs via crux-mir :)
defaultCruxOptions :: Crux.CruxOptions
defaultCruxOptions = case res of
    Left x -> error $ "failed to compute default crux options: " ++ show x
    Right x -> x
  where
    ss = Crux.cfgFile Crux.cruxOptions
    res = Config.loadValue (Config.sectionsSpec "crux" ss) (Config.Sections () [])

findTests :: String -> FilePath -> (FilePath -> FilePath -> IO ()) -> IO TestTree
findTests group_name test_dir test_action =
  do inputs <- findByExtension [".cbl"] test_dir
     let re = "== Explored .* executions =="
     return $ testGroup group_name
       [ goldenVsFileDiff
          (takeBaseName input) -- test name
          (\x y -> ["diff", "-I", re, "-u", x, y])
          goodFile -- golden file path
          outFile
          (test_action input outFile) -- action whose result is tested
       | input <- sort inputs
       , let outFile = replaceExtension input ".out"
       , let goodFile = replaceExtension input ".out.good"
       ]

testSimulator :: FilePath -> FilePath -> IO ()
testSimulator inFile outFile =
  do contents <- T.readFile inFile
     withFile outFile WriteMode $ \outh ->
       do let options = (defaultCruxOptions { Crux.inputFiles = [inFile],
                                              Crux.simVerbose = 0,
                                              Crux.globalTimeout = Just 600,
                                              Crux.goalTimeout = Just 600,
                                              Crux.solver = "yices",
                                              Crux.checkPathSat = True
                                            },
                         defaultCrucesOptions)
          let ?outputConfig = Crux.mkOutputConfig False outh outh
                                Crux.cruxLogMessageToSayWhat $ Just (fst options)
          run options
