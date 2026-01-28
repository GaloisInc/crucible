{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module TestBehavior (behaviorTests) where

import           Control.Lens ( (^.) )
import           Control.Monad ( void, when )
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Context ( pattern Empty, pattern (:>) )
import           System.Directory ( removeFile, listDirectory )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>), takeFileName, takeExtension, (</>) )
import qualified Data.List as List
import qualified System.IO as IO
import qualified System.Process as Proc

import qualified Test.Tasty as T
import           Test.Tasty.HUnit ( testCase, (@=?) )

-- LLVM parsing
import qualified Text.LLVM.AST as L
import           Data.LLVM.BitCode ( parseBitCodeFromFileWithWarnings )

-- Crucible
import           Lang.Crucible.Backend ( backendGetSym, getProofObligations )
import qualified Lang.Crucible.Simulator as CS
import           Lang.Crucible.Simulator.ExecutionTree ( ExecResult(..) )
import qualified Lang.Crucible.CFG.Core as CC

-- LLVM
import           Lang.Crucible.LLVM ( registerLazyModule )
import qualified Lang.Crucible.LLVM as CL
import qualified Lang.Crucible.LLVM.Globals as LLVMG
import qualified Lang.Crucible.LLVM.Intrinsics as Intrinsics
import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import qualified Lang.Crucible.LLVM.SymIO as SymIO
import qualified Lang.Crucible.LLVM.Translation as Trans
import           What4.Interface ( bvZero )

-- Reuse from existing tests
import           MemSetup ( withTranslatedModule )


behaviorTests :: IO T.TestTree
behaviorTests = do
  let behaviorDir = "test/behavior"
  files <- listDirectory behaviorDir
  let cFiles = List.sort $ filter (\f -> takeExtension f == ".c") files
  let testTrees = map (\f -> testBehaviorFile (behaviorDir </> f)) cFiles
  return $ T.testGroup "Behavior Tests" testTrees


testBehaviorFile :: FilePath -> T.TestTree
testBehaviorFile cFile = testCase (takeFileName cFile) $ do
  exePath <- compileToExecutable cFile
  bcPath <- compileToBitcode cFile

  expectedOut <- extractExpectedOutput cFile
  nativeOut <- runNative exePath
  symbolicOut <- runSymbolic bcPath

  let outPath = bcPath -<.> ".out"
  removeFile exePath
  removeFile bcPath
  removeFile outPath

  nativeOut @=? symbolicOut
  nativeOut @=? expectedOut
  symbolicOut @=? expectedOut


-- | Compile a C file to a native executable
compileToExecutable :: FilePath -> IO FilePath
compileToExecutable cFile = do
  let exePath = cFile -<.> ".exe"
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode "clang"
    ["-O1", "-fsanitize=undefined", "-o", exePath, cFile] ""
  when (exitCode /= ExitSuccess) $ do
    putStrLn $ "Failed to compile " ++ cFile ++ " to executable"
    putStrLn stdout
    putStrLn stderr
    fail "Compilation to executable failed"
  return exePath


-- | Compile a C file to LLVM bitcode
compileToBitcode :: FilePath -> IO FilePath
compileToBitcode cFile = do
  let bcPath = cFile -<.> ".bc"
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode "clang"
    ["-O1", "-emit-llvm", "-fno-discard-value-names", "-c", "-o", bcPath, cFile] ""
  when (exitCode /= ExitSuccess) $ do
    putStrLn $ "Failed to compile " ++ cFile ++ " to bitcode"
    putStrLn stdout
    putStrLn stderr
    fail "Compilation to bitcode failed"
  return bcPath


-- | Run a native executable and capture stdout
runNative :: FilePath -> IO String
runNative exePath = do
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode exePath [] ""
  when (exitCode /= ExitSuccess) $ do
    putStrLn $ "Failed to execute " ++ exePath
    putStrLn stdout
    putStrLn stderr
    fail "Native execution failed"
  return stdout


-- | Extract expected output from /// comments in the C file
-- All lines starting with /// are concatenated to form expected output
extractExpectedOutput :: FilePath -> IO String
extractExpectedOutput cFile = do
  content <- readFile cFile
  let linesInput = lines content
  let expectedLines = extractComments linesInput
  return $ unlines expectedLines
  where
    extractComments [] = []
    extractComments (line:rest)
      | "///" `List.isInfixOf` line =
          let stripped = dropWhile (/= '/') line
          in if take 3 stripped == "///"
             then unwords (words (drop 3 stripped)) : extractComments rest
             else extractComments rest
      | otherwise = extractComments rest


-- | Parse an LLVM bitcode file
parseLLVM :: FilePath -> IO L.Module
parseLLVM file =
  parseBitCodeFromFileWithWarnings file >>= \case
    Left err -> fail $ "Couldn't parse LLVM bitcode from file " ++ file ++ "\n" ++ show err
    Right (m, _warnings) -> return m


-- | Symbolically execute an LLVM bitcode file and capture stdout
runSymbolic :: FilePath -> IO String
runSymbolic bcPath = do
  llvmMod <- parseLLVM bcPath

  let outPath = bcPath -<.> ".out"
  outHandle <- IO.openFile outPath IO.WriteMode
  IO.hSetBuffering outHandle IO.LineBuffering

  withTranslatedModule @() llvmMod $ \trans ctx halloc bak -> do
    let memVar = Trans.llvmMemVar ctx

    mbMainCfg <- Trans.getTranslatedCFG trans "main"
    (_, CC.AnyCFG mainCfg, _warns) <- case mbMainCfg of
      Nothing -> fail "Could not find 'main' function in module"
      Just result -> return result

    mem <- LLVMG.initializeAllMemory bak ctx llvmMod
    mem' <- LLVMG.populateAllGlobals bak (trans ^. Trans.globalInitMap) mem
    let globSt = CL.llvmGlobals memVar mem'

    let intrinsicTypes = MapF.union Intrinsics.llvmIntrinsicTypes SymIO.llvmSymIOIntrinsicTypes
    let fns = CS.fnBindingsFromList []
    let impl = CL.llvmExtensionImpl ?memOpts
    let simCtx = CS.initSimContext bak intrinsicTypes halloc outHandle fns impl ()

    (mainArgs, mainGlobSt) <- case CC.cfgArgTypes mainCfg of
      (Empty :> LLVMMem.LLVMPointerRepr w :> LLVMMem.PtrRepr) -> do
        let sym = backendGetSym bak

        argc <- LLVMMem.llvmPointer_bv sym =<< bvZero sym w
        argv <- LLVMMem.mkNullPointer sym LLVMMem.PtrWidth

        let args = CS.assignReg LLVMMem.PtrRepr argv $
                   CS.assignReg (LLVMMem.LLVMPointerRepr w) argc CS.emptyRegMap

        return (args, globSt)

      _ -> fail "Unsupported main function signature"

    let ?intrinsicsOpts = Intrinsics.defaultIntrinsicsOptions
    let retType = CC.cfgReturnType mainCfg
    let simSt = CS.InitialState simCtx mainGlobSt CS.defaultAbortHandler retType $
                  CS.runOverrideSim retType $ do
                    void $ Intrinsics.register_llvm_overrides llvmMod [] [] ctx
                    registerLazyModule (\_ -> return ()) trans
                    CS.regValue <$> CS.callCFG mainCfg mainArgs

    execResult <- CS.executeCrucible [] simSt
    case execResult of
      FinishedResult {} -> do
        obligations <- getProofObligations bak
        case obligations of
          Nothing -> return ()
          Just _ -> fail "Symbolic execution finished with pending proof obligations"
      AbortedResult _ _ -> fail "Symbolic execution aborted"
      TimeoutResult {} -> fail "Symbolic execution timed out"

  IO.hFlush outHandle
  IO.hClose outHandle

  readFile outPath
