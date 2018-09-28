{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ExplicitForAll   #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Monad.ST

-- Crucible
import           Lang.Crucible.FunctionHandle (newHandleAllocator, HandleAllocator)
import           Lang.Crucible.LLVM.MemType (i32)
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.NatRepr (knownNat)

-- LLVM
import qualified Text.LLVM.AST as L
import           Text.LLVM.AST     (Module)
import           Data.LLVM.BitCode (parseBitCodeFromFile)


-- Tasty
import Test.Tasty (defaultMain, TestTree, testGroup)
import Test.Tasty.HUnit

-- General
import qualified Data.Map.Strict as Map
import           Control.Monad (when, forM_)
import           Control.Monad.Except
import qualified System.Directory as Dir
import qualified System.Process   as Proc
import           System.Exit (exitFailure, ExitCode(..))

-- Modules being tested
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.LLVM.Translation.Constant (LLVMConst(..))

-- | Compile a C file with clang, returning the exit code
compile :: FilePath -> IO (Int, String, String)
compile !file = do
  (exitCode, stdout, stderr) <-
    Proc.readProcessWithExitCode
      "clang" ["-emit-llvm", "-g", "-O0", "-c", file] ""
  pure $ (exitCodeToInt exitCode, stdout, stderr)
  where exitCodeToInt ExitSuccess     = 0
        exitCodeToInt (ExitFailure i) = i

-- | Parse an LLVM bit-code file.
-- Mostly copied from crucible-c.
parseLLVM :: FilePath -> IO (Either String Module)
parseLLVM !file =
  parseBitCodeFromFile file >>=
    \case
      Left err -> pure $ Left $ "Couldn't parse LLVM bitcode from file"
                                ++ file ++ "\n" ++ show err
      Right m  -> pure $ Right m

main :: IO ()
main = do wd <- Dir.getCurrentDirectory
          putStrLn $ "Looking for tests in " ++ wd

          let prepend pr = map (\s -> pr ++ s)
          let files      = prepend "global" [ "-int", "-struct", "-uninitialized", "-extern" ]
          let append ext = map (\s -> s ++ ext)

          putStrLn "Compiling C code to LLVM bitcode with clang"
          forM_ (prepend "test/data/" $ append ".c" files) $ \file -> do
            (exitCode, stdout, stderr) <- compile file
            when (exitCode /= 0) $ do
              putStrLn $ "Failed to compile " ++ file
              putStrLn stdout
              putStrLn stderr
              exitFailure
            pure ()

          putStrLn "Parsing LLVM bitcode"
          -- parsed :: [Module]
          parsed <- forM (append ".bc" files) $ \file -> do
            parsed <- parseLLVM file
            case parsed of
              Left err -> do
                putStrLn $ "Failed to parse " ++ file
                putStrLn err
                exitFailure
              Right m  -> pure m

          putStrLn "Translating LLVM modules"
          halloc     <- newHandleAllocator
          -- translated :: [ModuleTranslation]
          translated <- stToIO $ traverse (translateModule halloc) parsed

          -- Run tests on the results
          case translated of
            [Some g1, Some g2, Some g3, Some g4] ->
              defaultMain (tests g1 g2 g3 g4)

tests :: ModuleTranslation arch1
      -> ModuleTranslation arch2
      -> ModuleTranslation arch3
      -> ModuleTranslation arch4
      -> TestTree
tests int struct uninitialized _ = do
  testGroup "Tests"
    [ testCase "int" $
        Map.singleton (L.Symbol "x") (Right $ IntConst (knownNat @32) 42) @=?
           Map.map snd (globalInitMap int)
    , testCase "struct" $
        IntConst (knownNat @32) 17 @=?
           case snd <$> Map.lookup (L.Symbol "z") (globalInitMap struct) of
             Just (Right (StructConst _ (x : _))) -> x
             _ -> IntConst (knownNat @1) 0
    , testCase "unitialized" $
        Map.singleton (L.Symbol "x") (Right $ ZeroConst i32) @=?
           Map.map snd (globalInitMap uninitialized)
    -- The actual value for this one contains the error message, so it's a pain
    -- to type out. Uncomment this test to take a look.
    -- , testCase "extern" $
    --     Map.singleton (L.Symbol "x") (Left $ "") @=?
    --        (globalMap extern)
    ]
