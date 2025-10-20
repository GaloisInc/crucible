{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
module Main (main) where

import qualified Data.List as List
import System.FilePath
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import qualified Crux as Crux
import qualified Crux.Config.Common as Crux

import qualified Config
import qualified Config.Schema as Config

import Cruces.CrucesMain

main :: IO ()
main = do
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
       | input <- List.sort inputs
       , let outFile = replaceExtension input ".out"
       , let goodFile = replaceExtension input ".out.good"
       ]

testSimulator :: FilePath -> FilePath -> IO ()
testSimulator inFile outFile =
  do withFile outFile WriteMode $ \outh ->
       do let outOpts = (Crux.outputOptions defaultCruxOptions)
                          { Crux.simVerbose = 0
                          }
              options = (defaultCruxOptions { Crux.outputOptions = outOpts,
                                              Crux.inputFiles = [inFile],
                                              Crux.globalTimeout = Just 600,
                                              Crux.goalTimeout = Just 600,
                                              Crux.solver = "yices",
                                              Crux.checkPathSat = True
                                            },
                         defaultCrucesOptions)
          let ?outputConfig = Crux.mkOutputConfig (outh, False) (outh, False)
                                Crux.cruxLogMessageToSayWhat $ Just (Crux.outputOptions (fst options))
          run options
