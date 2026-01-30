-- | See @test/behavior/README.md@

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
import qualified Data.Vector as V
import           System.Directory ( listDirectory )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>), takeFileName, takeExtension, (</>) )
import qualified Data.List as List
import qualified System.IO as IO
import qualified System.Process as Proc
import           Data.Time.Clock ( NominalDiffTime )

import qualified Test.Tasty as T
import           Test.Tasty.HUnit ( testCase, (@=?) )

-- LLVM parsing
import qualified Text.LLVM.AST as L
import           Data.LLVM.BitCode ( parseBitCodeFromFileWithWarnings )

-- Crucible
import           Lang.Crucible.Backend ( backendGetSym, getProofObligations )
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Simulator as CS
import           Lang.Crucible.Simulator ( timeoutFeature, genericToExecutionFeature )
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
import           What4.Interface ( bvOne )

-- Reuse from existing tests
import           MemSetup ( withTranslatedModule )


behaviorTests :: IO T.TestTree
behaviorTests = do
  let behaviorDir = "test/behavior"
  files <- listDirectory behaviorDir
  let cFiles = List.sort $ filter (\f -> takeExtension f == ".c") files
  let testTrees = map (\f -> testBehaviorFile (behaviorDir </> f)) cFiles

  let gccDir = "test/behavior/gcc-c-torture"
  extFiles <- listDirectory gccDir
  let cExtFiles = List.sort $ filter (\f -> takeExtension f == ".c") extFiles
  let gccTests = map (\f -> testBehaviorFileExternal (gccDir </> f)) cExtFiles

  return $ T.testGroup "Behavior tests"
    [ T.testGroup "Manual tests" testTrees
    , T.testGroup "GCC tests" gccTests
    ]


testBehaviorFile :: FilePath -> T.TestTree
testBehaviorFile cFile = testCase (takeFileName cFile) $ do
  exePath <- compileExe cFile
  bcPath <- cimpileBc cFile

  expectedOut <- extractExpectedOutput cFile
  nativeOut <- runExe exePath
  symbolicOut <- runBc bcPath

  nativeOut @=? symbolicOut
  nativeOut @=? expectedOut
  -- by transitivity we have symbolicOut == expectedOut


-- | Test external test files that don't have expected output comments
-- Just verify that both native and symbolic execution succeed
testBehaviorFileExternal :: FilePath -> T.TestTree
testBehaviorFileExternal cFile = testCase (takeFileName cFile) $ do
  exePath <- compileExe cFile
  bcPath <- cimpileBc cFile
  _ <- runExe exePath
  _ <- runBc bcPath
  return ()

cflags :: [String]
cflags = ["-O1", "-Wno-implicit-function-declaration", "-Wno-implicit-int"]

compileFile :: String -> FilePath -> [String] -> IO FilePath
compileFile outputExt cFile additionalArgs = do
  let outPath = cFile -<.> outputExt
  let args = cflags ++ additionalArgs ++ ["-o", outPath, cFile]
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode "clang" args ""
  when (exitCode /= ExitSuccess) $
    fail $ unlines $
      [ "Compilation failed!"
      , "clang " ++ unwords args
      , "stdout:"
      , stdout
      , "stderr:"
      , stderr
      ]
  return outPath

compileExe :: FilePath -> IO FilePath
compileExe cFile =
  compileFile ".exe" cFile ["-fsanitize=undefined"]

cimpileBc :: FilePath -> IO FilePath
cimpileBc cFile =
  compileFile ".bc" cFile ["-emit-llvm", "-fno-discard-value-names", "-c"]

runExe :: FilePath -> IO String
runExe exePath = do
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode exePath [] ""
  when (exitCode /= ExitSuccess) $
    fail $ unlines $
      [ "Native execution failed!"
      , exePath
      , "stdout:"
      , stdout
      , "stderr:"
      , stderr
      ]
  return stdout


-- | Extract expected output from /// comments in the C file
-- All lines starting with /// are concatenated to form expected output
extractExpectedOutput :: FilePath -> IO String
extractExpectedOutput cFile = do
  content <- readFile cFile
  let expectedLines = extractComments (lines content)
  return $ unlines expectedLines
  where
    extractComments [] = []
    extractComments (line:rest)
      | "/// " `List.isInfixOf` line =
          let stripped = dropWhile (/= '/') line
          in if take 4 stripped == "/// "
             then drop 4 stripped : extractComments rest
             else extractComments rest
      | otherwise = extractComments rest


ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult ar = case ar of
  CS.AbortedExec reason _ -> show (CB.ppAbortExecReason reason)
  CS.AbortedExit code _ -> "exit " ++ show code
  CS.AbortedBranch _ _ res1 res2 ->
    unlines
    [ "branch:"
    , ppAbortedResult res1
    , ppAbortedResult res2
    ]

parseBc :: FilePath -> IO L.Module
parseBc file =
  parseBitCodeFromFileWithWarnings file >>= \case
    Left err -> fail $ "Couldn't parse LLVM bitcode from file " ++ file ++ "\n" ++ show err
    Right (m, _warnings) -> return m


-- | Symbolically execute an LLVM bitcode file and capture stdout
runBc :: FilePath -> IO String
runBc bcPath = do
  llvmMod <- parseBc bcPath

  let outPath = bcPath -<.> ".out"
  outHandle <- IO.openFile outPath IO.WriteMode
  IO.hSetBuffering outHandle IO.LineBuffering

  withTranslatedModule @() llvmMod $ \trans ctx halloc bak -> do
    let memVar = Trans.llvmMemVar ctx

    CC.AnyCFG mainCfg <-
      Trans.getTranslatedCFG trans "main" >>=
        \case
          Nothing -> fail "Could not find 'main' function in module"
          Just (_, cfg, _warns) -> return cfg

    mem <- LLVMG.initializeAllMemory bak ctx llvmMod
    mem' <- LLVMG.populateAllGlobals bak (trans ^. Trans.globalInitMap) mem

    let intrinsicTypes = MapF.union Intrinsics.llvmIntrinsicTypes SymIO.llvmSymIOIntrinsicTypes
    let fns = CS.fnBindingsFromList []
    let impl = CL.llvmExtensionImpl ?memOpts
    let simCtx = CS.initSimContext bak intrinsicTypes halloc outHandle fns impl ()

    mainArgs <-
      case CC.cfgArgTypes mainCfg of
        -- main(int argc, char** argv)
        (Empty :> LLVMMem.LLVMPointerRepr w :> LLVMMem.PtrRepr) -> do
          let sym = backendGetSym bak
          argc_ <- LLVMMem.llvmPointer_bv sym =<< bvOne sym w
          argv_ <- LLVMMem.mkNullPointer sym LLVMMem.PtrWidth
          let argc = CS.RegEntry (LLVMMem.LLVMPointerRepr w) argc_
          let argv = CS.RegEntry LLVMMem.PtrRepr argv_
          return (CS.RegMap (Empty :> argc :> argv))

        -- main(void)
        Empty -> return CS.emptyRegMap

        -- main() - technically varargs
        (Empty :> CC.VectorRepr elemTy) -> do
          let v = CS.RegEntry (CC.VectorRepr elemTy) V.empty
          return (CS.RegMap (Empty :> v))

        _ -> fail "Unsupported main function signature"

    let ?intrinsicsOpts = Intrinsics.defaultIntrinsicsOptions
    let retType = CC.cfgReturnType mainCfg
    let globSt = CL.llvmGlobals memVar mem'
    let simSt = CS.InitialState simCtx globSt CS.defaultAbortHandler retType $
                  CS.runOverrideSim retType $ do
                    void $ Intrinsics.register_llvm_overrides llvmMod [] [] ctx
                    registerLazyModule (\_ -> return ()) trans
                    CS.regValue <$> CS.callCFG mainCfg mainArgs

    timeoutFeat <- timeoutFeature (5 :: NominalDiffTime)
    let features = [genericToExecutionFeature timeoutFeat]

    execResult <- CS.executeCrucible features simSt
    case execResult of
      FinishedResult {} -> do
        obligations <- getProofObligations bak
        case obligations of
          Nothing -> return ()
          Just _ -> fail "Symbolic execution finished with pending proof obligations"
      AbortedResult _ abortResult -> do
        case abortResult of
          CS.AbortedExit ExitSuccess _ -> return ()
          CS.AbortedExec (CB.EarlyExit _) _ -> return ()  -- exit()
          _ -> fail (ppAbortedResult abortResult)
      TimeoutResult {} -> fail "Symbolic execution timed out"

  IO.hFlush outHandle
  IO.hClose outHandle
  readFile outPath
