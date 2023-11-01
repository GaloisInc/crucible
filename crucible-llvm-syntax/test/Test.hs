{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.List (sort)
import Data.Text.IO qualified as T
import System.FilePath
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Data.Parameterized.NatRepr (knownNat)

import Lang.Crucible.FunctionHandle (newHandleAllocator)

import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.MemModel (mkMemVar)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Prog (doParseCheck)

import Lang.Crucible.LLVM.Syntax (llvmParserHooks)

main :: IO ()
main = do
  parseTests <- findTests "Parse tests" "test-data" testParser
  defaultMain $ testGroup "Tests" [parseTests]

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

parserHooks :: IO (ParserHooks LLVM)
parserHooks = do
  halloc <- newHandleAllocator
  memVar <- mkMemVar "crucible-llvm-syntax-test-memory" halloc
  let ?ptrWidth = knownNat @64
  return (llvmParserHooks memVar)

testParser :: FilePath -> FilePath -> IO ()
testParser inFile outFile =
  do contents <- T.readFile inFile
     hooks <- parserHooks
     let ?parserHooks = hooks
     withFile outFile WriteMode $ doParseCheck inFile contents True

