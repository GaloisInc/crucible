{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams   #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

-- Crucible
import           Lang.Crucible.FunctionHandle ( newHandleAllocator )

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr
import           Data.Parameterized.SymbolRepr ( SomeSym(SomeSym) )

-- LLVM
import qualified Text.LLVM.AST as L
import           Text.LLVM.AST (Module)
import           Data.LLVM.BitCode

-- Tasty
import           Test.Tasty
import           Test.Tasty.HUnit
import qualified Test.Tasty.Options as TO
import qualified Test.Tasty.Runners as TR
import qualified Test.Tasty.Sugar as TS

-- General
import           Control.Monad
import           Data.Either ( fromRight )
import           Data.Maybe ( catMaybes )
import           GHC.TypeLits
import qualified Data.Map.Strict as Map
import           Data.Proxy ( Proxy(..) )
import qualified System.Directory as Dir
import           System.Environment ( lookupEnv )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>), splitExtension, splitFileName )
import qualified System.Process as Proc

-- Modules being tested
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.Translation

import           TestFunctions
import           TestGlobals
import           TestMemory
import           TestTranslation


data LLVMAssembler (source :: Symbol) = LLVMAssembler String
  deriving (Eq, Show)

instance TO.IsOption (SomeSym LLVMAssembler) where
  defaultValue = SomeSym $ LLVMAssembler @"default" "llvm-as"
  parseValue = Just . SomeSym . LLVMAssembler @ "option"
  optionName = pure "llvm-assembler"
  optionHelp = pure $ unwords ["The LLVM assembler to use on .ll files"
                              ,"(overrides the LLVM_AS environment variable,"
                              ,"default is \"llvm-as\")"]

data Clang (source :: Symbol) = Clang String
  deriving (Eq, Show)

instance TO.IsOption (SomeSym Clang) where
  defaultValue = SomeSym $ Clang @"default" "clang"
  parseValue = Just . SomeSym . Clang @"option"
  optionName = pure "clang"
  optionHelp = pure $ unwords ["The clang binary to use to compile C files"
                              ,"(overrides the CLANG environment variable,"
                              ,"default is \"clang\")"]

optionSource :: opt (source :: Symbol) -> Proxy source
optionSource _ = Proxy

doProc :: String -> [String] -> IO ProcResult
doProc !exe !args = do
  (exitCode, stdout, stderr) <- Proc.readProcessWithExitCode exe args ""
  pure $ (exitCodeToInt exitCode, stdout, stderr)
  where exitCodeToInt ExitSuccess     = 0
        exitCodeToInt (ExitFailure i) = i

type ProcResult = (Int, String, String)

assertProcSuccess :: String -> String -> ProcResult -> Assertion
assertProcSuccess msg file (exitCode, stdout, stderr) = do
  when (exitCode /= 0) $ do
    putStrLn $ msg ++ " " ++ file ++ " failure"
    putStrLn stdout
    putStrLn stderr
  exitCode == 0 @? msg ++ " " ++ file ++ " attempt failed with " ++ show exitCode


-- | Compile a C file with clang, returning the exit code
compile :: Clang "executable" -> FilePath -> IO ProcResult
compile (Clang clang) !file = doProc clang ["-emit-llvm", "-g", "-O0", "-c", file]

-- | Assemble a ll file with llvm-as, returning the exit code
assemble :: LLVMAssembler "executable" -> FilePath -> FilePath -> IO ProcResult
assemble (LLVMAssembler llvm_as) !inputFile !outputFile =
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
llvmTestIngredients = includingOptions [ TO.Option (Proxy @(SomeSym LLVMAssembler))
                                       , TO.Option (Proxy @(SomeSym Clang))
                                       ] :
                      includingOptions TS.sugarOptions :
                      TS.sugarIngredients [cCube, lCube] <>
                      defaultIngredients

cCube, lCube :: TS.CUBE
cCube = TS.mkCUBE { TS.inputDir = "test/c"
                  , TS.rootName = "*.c"
                  , TS.separators = "."
                  , TS.expectedSuffix = "checks"
                  }

lCube = cCube { TS.inputDir = "test/ll"
              , TS.rootName = "*.ll"
              }


main :: IO ()
main = do
    do testSweets <- concat <$> (mapM TS.findSugar [cCube, lCube])

       fileTests <- TS.withSugarGroups testSweets testGroup $
           \sweets _ expectation -> do
             -- The expected file contains a list of the tests to run
             -- on the LLVM translation.
             checklist <- lines <$> readFile (TS.expectedFile expectation)
             return $
               testBuildTranslation (TS.rootFile sweets) $
               (\getTrans -> testGroup "checks" $ map (transCheck getTrans) checklist)

       defaultMainWithIngredients llvmTestIngredients $
         testGroup "Tests"
         [ functionTests
         , globalTests
         , memoryTests
         , translationTests
         , testGroup "Input Files" $ fileTests
         ]



testBuildTranslation :: FilePath -> (IO (Some ModuleTranslation) -> TestTree) -> TestTree
testBuildTranslation srcPath llvmTransTests =
  -- n.b. srcPath may be a relative path
  let (dName, srcName) = splitFileName srcPath
      (fName, ext) = splitExtension srcName
      bcPath = srcPath -<.> ".bc"
      (_, bcName) = splitFileName bcPath

      genBCName = case ext of
                    ".c" -> "compile " <> fName
                    ".ll" -> "assemble " <> fName
                    _ -> error $ "Cannot build LLVM bitcode file from a " ++ ext ++ " file"
      parseBCName = "parse " ++ fName ++ " bitcode"
      translateName = "translate " ++ fName

      c_compile =
        if (ext == ".c")
        then
          Just $ askOption $ \(SomeSym clangOption :: SomeSym Clang) ->
          testCase genBCName $ do
          clang <-
            let src = optionSource clangOption in
            case sameSymbol src (Proxy :: Proxy "option") of
              Just Refl -> let Clang c = clangOption in return $ Clang c
              _ -> case sameSymbol src (Proxy :: Proxy "default") of
                Just Refl -> maybe (Clang "clang") Clang <$> lookupEnv "CLANG"
                _ -> error $ "Unknown Clang specification type: " <> symbolVal src
          assertProcSuccess "compile" srcPath =<<
              Dir.withCurrentDirectory dName (compile clang srcName)
        else Nothing

      llvm_assemble =
        if (ext == ".ll")
        then Just $ askOption $ \(SomeSym assemblerOption :: SomeSym LLVMAssembler) ->
          testCase genBCName $ do
          llvm_as <-
            let src = optionSource assemblerOption in
            case sameSymbol src (Proxy :: Proxy "option") of
              Just Refl -> let LLVMAssembler a = assemblerOption
                           in return $ LLVMAssembler a
              _ -> case sameSymbol src (Proxy :: Proxy "default") of
                Just Refl -> maybe (LLVMAssembler "llvm-as") LLVMAssembler <$>
                             lookupEnv "LLVM_AS"
                _ -> error $ "Unknown LLVM Assembler specification type: " <> symbolVal src

          assertProcSuccess "assemble" srcPath =<<
            Dir.withCurrentDirectory dName (assemble llvm_as srcName bcName)
        else Nothing

      parse_bitcode =
        testCase parseBCName $
        parseLLVM bcPath >>= \case
          Left err -> do
            putStrLn $ "Failed to parse " ++ bcPath
            putStrLn err
            err @?= ""
          Right _ -> pure ()

      trans = do halloc <- newHandleAllocator
                 let ?laxArith = False
                 translateModule halloc =<<
                   (fromRight (error "parsing was already verified") <$> parseLLVM bcPath)

      translate_bitcode =
        testCase translateName $ do
        trans >>= \(Some modTrans) ->
          not (Map.null $ cfgMap modTrans) @? "Translation of " ++ bcPath ++ " was empty (failed?)"


  in testGroup srcPath $ catMaybes
    [ c_compile
    , llvm_assemble
    , Just $ after AllSucceed genBCName     parse_bitcode
    , Just $ after AllSucceed parseBCName   translate_bitcode
    , Just $ after AllSucceed translateName (llvmTransTests trans)
    ]


transCheck :: IO (Some ModuleTranslation) -> String -> TestTree
transCheck getTrans = \case

  "extern_int" ->
    testCase "valid global extern variable reference" $ do
    Some t <- getTrans
    Map.singleton (L.Symbol "extern_int") (Right (i32, Nothing)) @=?
      Map.map snd (globalInitMap t)

  "x=42" ->
    testCase "valid global integer symbol reference" $ do
    Some t <- getTrans
    Map.singleton (L.Symbol "x") (Right $ (i32, Just $ IntConst (knownNat @32) (BV.mkBV knownNat 42))) @=?
      Map.map snd (globalInitMap t)

  "z.xx=17" ->
    testCase "valid global struct field symbol reference" $ do
    Some t <- getTrans
    IntConst (knownNat @32) (BV.mkBV knownNat 17) @=?
      case snd <$> Map.lookup (L.Symbol "z") (globalInitMap t) of
        Just (Right (_, Just (StructConst _ (x : _)))) -> x
        _ -> IntConst (knownNat @1) (BV.zero knownNat)

  "x uninitialized" ->
    testCase "valid global unitialized variable reference" $ do
    Some t <- getTrans
    Map.singleton (L.Symbol "x") (Right $ (i32, Just $ ZeroConst i32)) @=?
      Map.map snd (globalInitMap t)

  -- We're really just checking that the translation succeeds without
  -- exceptions.
  "" -> testCase "no additional checks" $ return ()

  other -> testCase other $ assertFailure $ "Unknown check: " <> other
