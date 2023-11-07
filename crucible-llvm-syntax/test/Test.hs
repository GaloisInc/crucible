{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Control.Monad.IO.Class (liftIO)
import Data.List (sort)
import Data.Text.IO qualified as T
import System.FilePath
import System.IO

import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.Golden

import Data.Parameterized.NatRepr (knownNat)

import What4.Solver.Z3 (z3Options)

import Lang.Crucible.Simulator.OverrideSim (writeGlobal)
import Lang.Crucible.FunctionHandle (newHandleAllocator)

import Lang.Crucible.LLVM (llvmExtensionImpl)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.MemModel (defaultMemOptions, emptyMem, mkMemVar)

import Lang.Crucible.Syntax.Concrete (ParserHooks)
import Lang.Crucible.Syntax.Prog (SimulateProgramHooks(setupHook), defaultSimulateProgramHooks, doParseCheck, simulateProgramWithExtension)

import Lang.Crucible.LLVM.Syntax (emptyParserHooks, llvmParserHooks)
import Lang.Crucible.LLVM.Syntax.TypeAlias (typeAliasParserHooks, x86_64LinuxTypes)

main :: IO ()
main = do
  parseTests <- findTests "Parse tests" "test-data/parse" testParser
  simTests <- findTests "LLVM simulation" "test-data/simulate" testSimulator
  defaultMain $ testGroup "Tests" [parseTests, simTests]

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
  let hooks = typeAliasParserHooks x86_64LinuxTypes
  return (llvmParserHooks hooks memVar)

testParser :: FilePath -> FilePath -> IO ()
testParser inFile outFile =
  do contents <- T.readFile inFile
     hooks <- parserHooks
     let ?parserHooks = hooks
     withFile outFile WriteMode $ doParseCheck inFile contents True

testSimulator :: FilePath -> FilePath -> IO ()
testSimulator inFile outFile =
  do contents <- T.readFile inFile
     ha <- newHandleAllocator
     mvar <- mkMemVar "llvm_memory" ha
     let ?ptrWidth = knownNat @64
     let ?parserHooks = llvmParserHooks emptyParserHooks mvar
     withFile outFile WriteMode $ \outh -> do
       let ext _ =
             let ?recordLLVMAnnotation = \_ _ _ -> pure ()
             in llvmExtensionImpl defaultMemOptions
       simulateProgramWithExtension ext inFile contents outh Nothing z3Options $
         defaultSimulateProgramHooks
           { setupHook = \_sym _ha -> do
               mem <- liftIO (emptyMem LittleEndian)
               writeGlobal mvar mem
           }


