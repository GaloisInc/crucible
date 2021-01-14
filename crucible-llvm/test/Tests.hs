{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ExplicitForAll   #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

-- Crucible
import           Lang.Crucible.FunctionHandle ( newHandleAllocator )

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr

-- LLVM
import qualified Text.LLVM.AST as L
import           Text.LLVM.AST (Module)
import           Data.LLVM.BitCode

-- Tasty
import           Test.Tasty
import           Test.Tasty.HUnit
import qualified Test.Tasty.Options as TO
import qualified Test.Tasty.Runners as TR

-- General
import           Data.Foldable
import           Data.Proxy ( Proxy(..) )
import           Control.Monad
import qualified Data.Map.Strict as Map
import qualified System.Directory as Dir
import           System.Exit (exitFailure, ExitCode(..))
import qualified System.Process as Proc

-- Modules being tested
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation

import           TestFunctions
import           TestGlobals
import           TestMemory
import           TestTranslation


data LLVMAssembler = LLVMAssembler String
  deriving (Eq, Show)

instance TO.IsOption LLVMAssembler where
  defaultValue = LLVMAssembler "llvm-as"
  parseValue = Just . LLVMAssembler
  optionName = pure "llvm-assembler"
  optionHelp = pure "The LLVM assembler to use on .ll files"

data Clang = Clang String
  deriving (Eq, Show)

instance TO.IsOption Clang where
  defaultValue = Clang "clang"
  parseValue = Just . Clang
  optionName = pure "clang"
  optionHelp = pure "The clang binary to use to compile C files"

doProc :: String -> [String] -> IO (Int, String, String)
doProc !exe !args = do
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode exe args ""
  pure $ (exitCodeToInt exitCode, stdout, stderr)
  where exitCodeToInt ExitSuccess     = 0
        exitCodeToInt (ExitFailure i) = i


-- | Compile a C file with clang, returning the exit code
compile :: String -> FilePath -> IO (Int, String, String)
compile clang !file = doProc clang ["-emit-llvm", "-g", "-O0", "-c", file]

-- | Assemble a ll file with llvm-as, returning the exit code
assemble :: String -> FilePath -> FilePath -> IO (Int, String, String)
assemble llvm_as !inputFile !outputFile =
  doProc llvm_as ["-o", outputFile, inputFile]

-- | Parse an LLVM bit-code file.
-- Mostly copied from crucible-c.
parseLLVM :: FilePath -> IO (Either String Module)
parseLLVM !file =
  parseBitCodeFromFile file >>=
    \case
      Left err -> pure $ Left $ "Couldn't parse LLVM bitcode from file"
                                ++ file ++ "\n" ++ show err
      Right m  -> pure $ Right m

llvmTestIngredients :: [TR.Ingredient]
llvmTestIngredients = includingOptions [ TO.Option (Proxy @LLVMAssembler)
                                       , TO.Option (Proxy @Clang)
                                       ] : defaultIngredients

main :: IO ()
main = do
  -- Parse the command line options using Tasty's default settings; the normal
  -- 'askOption' combinators only work inside of the 'TestTree', which doesn't
  -- help for this setup code. We have to pass in some TestTree, but it doesn't
  -- really matter for this use case
  let emptyTestGroup = testGroup "emptyTestGroup" []
  opts <- TR.parseOptions llvmTestIngredients emptyTestGroup
  let LLVMAssembler llvm_as = TO.lookupOption @LLVMAssembler opts
  let Clang clang = TO.lookupOption @Clang opts

  wd <- Dir.getCurrentDirectory
  putStrLn $ "Looking for tests in " ++ wd

  let prepend pr = map (\s -> pr ++ s)
  let cfiles     = prepend "global" [ "-int", "-struct", "-uninitialized", "-extern" ]
  let llfiles    = ["lifetime"]
  let append ext = map (\s -> s ++ ext)
  let assertSuccess msg file (exitCode, stdout, stderr) = do
        when (exitCode /= 0) $ do
          putStrLn $ msg ++ " " ++ file
          putStrLn stdout
          putStrLn stderr
          exitFailure

  putStrLn ("Compiling C code to LLVM bitcode with " ++ clang)
  forM_ (prepend "test/c/" $ append ".c" cfiles) $ \file -> do
    assertSuccess "compile" file =<< compile clang file

  putStrLn ("Assembling LLVM assembly with " ++ llvm_as)
  forM_ (zip (prepend "test/ll/" $ append ".ll" llfiles)
             (append ".bc" llfiles)) $ \(inputFile, outputFile) -> do
    assertSuccess "assemble" inputFile =<< assemble llvm_as inputFile outputFile

  putStrLn "Parsing LLVM bitcode"
  -- parsed :: [Module]
  parsed <-
    forM (append ".bc" (cfiles ++ llfiles)) $ \file -> do
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
  let ?laxArith = False
  translated <- traverse (translateModule halloc) parsed

  -- Run tests on the results
  case translated of
    [Some g1, Some g2, Some g3, Some g4, Some l1] ->
      defaultMainWithIngredients llvmTestIngredients (tests g1 g2 g3 g4 l1)
    _ -> error "translation failure!"

tests :: ModuleTranslation arch1
      -> ModuleTranslation arch2
      -> ModuleTranslation arch3
      -> ModuleTranslation arch4
      -> ModuleTranslation arch5
      -> TestTree
tests int struct uninitialized _ lifetime = do
  testGroup "Tests" $ concat $
    [[ functionTests
     , globalTests
     , memoryTests
     , translationTests

     ]] <>
    [ [ testCase "int" $
          Map.singleton (L.Symbol "x") (Right $ (i32, Just $ IntConst (knownNat @32) (BV.mkBV knownNat 42))) @=?
             Map.map snd (globalInitMap int)
      , testCase "struct" $
          IntConst (knownNat @32) (BV.mkBV knownNat 17) @=?
             case snd <$> Map.lookup (L.Symbol "z") (globalInitMap struct) of
               Just (Right (_, Just (StructConst _ (x : _)))) -> x
               _ -> IntConst (knownNat @1) (BV.zero knownNat)
      , testCase "unitialized" $
          Map.singleton (L.Symbol "x") (Right $ (i32, Just $ ZeroConst i32)) @=?
             Map.map snd (globalInitMap uninitialized)
      -- The actual value for this one contains the error message, so it's a pain
      -- to type out. Uncomment this test to take a look.
      -- , testCase "extern" $
      --     Map.singleton (L.Symbol "x") (Left $ "") @=?
      --        (globalMap extern)

      -- We're really just checking that the translation succeeds without
      -- exceptions.
      , testCase "lifetime" $
          False @=? Map.null (cfgMap lifetime)
      ]


    ]
