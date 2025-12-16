{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams   #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

-- Crucible
import           Lang.Crucible.FunctionHandle ( newHandleAllocator )

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.DecidableEq ( decEq )
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
import           Control.Lens (view)
import           Control.Monad
import           Data.Either ( fromRight )
import           Data.Functor.Classes ( Eq1(liftEq) )
import           Data.Functor.Identity ( Identity(..) )
import           Data.Maybe ( catMaybes )
import           GHC.TypeLits
import qualified Data.Map.Strict as Map
import           Data.Proxy ( Proxy(..) )
import qualified System.Directory as Dir
import           System.Environment ( lookupEnv )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>), splitExtension, splitFileName )
import qualified System.IO as IO
import qualified System.Process as Proc


import qualified What4.Internal as WInt

-- Modules being tested
import           Lang.Crucible.LLVM.Internal (assertionsEnabled)
import           Lang.Crucible.LLVM.MemModel ( mkMemVar )
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
  parseValue = Just . SomeSym . LLVMAssembler @"option"
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
  parseBitCodeFromFileWithWarnings file >>=
    \case
      Left err -> pure $ Left $ "Couldn't parse LLVM bitcode from file"
                                ++ file ++ "\n" ++ show err
      Right (m, warnings) -> do
        unless (null warnings) $
          IO.hPrint IO.stderr $ ppParseWarnings warnings
        pure $ Right m

llvmTestIngredients :: [TR.Ingredient]
llvmTestIngredients = includingOptions [ TO.Option (Proxy @(SomeSym LLVMAssembler))
                                       , TO.Option (Proxy @(SomeSym Clang))
                                       ] :
                      includingOptions TS.sugarOptions :
                      TS.sugarIngredients [cCube, lCube] <>
                      defaultIngredients

cCube, lCube :: TS.CUBE
cCube = TS.mkCUBE { TS.inputDirs = ["test/c"]
                  , TS.rootName = "*.c"
                  , TS.separators = "."
                  , TS.expectedSuffix = "checks"
                  }

lCube = cCube { TS.inputDirs = ["test/ll"]
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
         [ -- See Note [Asserts] in crucible-llvm
           testCase "assertions enabled" $ do
             assertsEnabled <- assertionsEnabled
             assertBool "assertions should be enabled" assertsEnabled
         , -- See Note [Asserts] in what4
           testCase "What4 assertions enabled" $ do
             assertsEnabled <- WInt.assertionsEnabled
             assertBool "What4 assertions should be enabled" assertsEnabled
         , functionTests
         , globalTests
         , memoryTests
         , translationTests
         , testGroup "Input Files" $ fileTests
         ]



testBuildTranslation :: FilePath -> (IO (Some ModuleTranslation) -> TestTree) -> [TestTree]
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
                 let ?transOpts = defaultTranslationOptions
                 memVar <- mkMemVar "buildTranslation_test_llvm_memory" halloc
                 m <- (translateModule halloc memVar =<<
                        (fromRight (error "parsing was already verified") <$> parseLLVM bcPath))
                 return m

      translate_bitcode =
        testCase translateName $ do
        trans >>= \(Some modTrans) ->
          not (null $ view modTransDefs modTrans) @? "Translation of " ++ bcPath ++ " was empty (failed?)"


  in catMaybes
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
    case snd <$> Map.lookup (L.Symbol "extern_int") (view globalInitMap t) of
      Just (Right (actualTy, actualMbConst)) -> do
        let expectedTy = i32
        let expectedMbConst = Nothing
        expectedTy @=? actualTy
        assertLiftEq llvmConstSyntacticEq expectedMbConst actualMbConst
      _ -> assertFailure "Could not look up extern_int"

  "x=42" ->
    testCase "valid global integer symbol reference" $ do
    Some t <- getTrans
    case snd <$> Map.lookup (L.Symbol "x") (view globalInitMap t) of
      Just (Right (actualTy, actualMbConst)) -> do
        let expectedTy = i32
        let expectedMbConst = Just $ IntConst (knownNat @32) (BV.mkBV knownNat 42)
        expectedTy @=? actualTy
        assertLiftEq llvmConstSyntacticEq expectedMbConst actualMbConst
      _ -> assertFailure "Could not look up x"

  "z.xx=17" ->
    testCase "valid global struct field symbol reference" $ do
    Some t <- getTrans
    case snd <$> Map.lookup (L.Symbol "z") (view globalInitMap t) of
      Just (Right (_, actualMbConst)) ->
        case actualMbConst of
          Just (StructConst _ (actualXField : _)) -> do
            let expectedXField = IntConst (knownNat @32) (BV.mkBV knownNat 17)
            assertLiftEq
              llvmConstSyntacticEq
              (Identity expectedXField)
              (Identity actualXField)
          _ -> assertFailure $
            "Expected x to be a struct with at least one field, " ++
            "but it was actually " ++ show actualMbConst
      _ -> assertFailure "Could not look up z"

  "x uninitialized" ->
    testCase "valid global unitialized variable reference" $ do
    Some t <- getTrans
    case snd <$> Map.lookup (L.Symbol "x") (view globalInitMap t) of
      Just (Right (actualTy, actualMbConst)) -> do
        let expectedTy = i32
        let expectedMbConst = Just $ ZeroConst i32
        expectedTy @=? actualTy
        assertLiftEq llvmConstSyntacticEq expectedMbConst actualMbConst
      _ -> assertFailure "Could not look up x"

  -- We're really just checking that the translation succeeds without
  -- exceptions.
  "" -> testCase "no additional checks" $ return ()

  other -> testCase other $ assertFailure $ "Unknown check: " <> other

-- | Helper, not exported
--
-- Compare two 'LLVMConst's for syntactic equality. This should not be confused
-- with the semantic notion of equality that LLVM typically uses. For instance,
-- this function considers two 'UndefConst's values to be syntactically equal,
-- but LLVM's semantic equality could deem two @undef@ values to be not equal.
llvmConstSyntacticEq :: LLVMConst -> LLVMConst -> Bool
llvmConstSyntacticEq (ZeroConst mem1) (ZeroConst mem2) =
  mem1 == mem2
llvmConstSyntacticEq (IntConst w1 x1) (IntConst w2 x2) =
  case decEq w1 w2 of
    Left Refl -> x1 == x2
    Right _   -> False
llvmConstSyntacticEq (FloatConst f1) (FloatConst f2) =
  f1 == f2
llvmConstSyntacticEq (DoubleConst d1) (DoubleConst d2) =
  d1 == d2
llvmConstSyntacticEq (LongDoubleConst ld1) (LongDoubleConst ld2) =
  ld1 == ld2
llvmConstSyntacticEq (StringConst s1) (StringConst s2) =
  s1 == s2
llvmConstSyntacticEq (ArrayConst mem1 a1) (ArrayConst mem2 a2) =
  mem1 == mem2 && liftEq llvmConstSyntacticEq a1 a2
llvmConstSyntacticEq (VectorConst mem1 v1) (VectorConst mem2 v2) =
  mem1 == mem2 && liftEq llvmConstSyntacticEq v1 v2
llvmConstSyntacticEq (StructConst si1 a1) (StructConst si2 a2) =
  si1 == si2 && liftEq llvmConstSyntacticEq a1 a2
llvmConstSyntacticEq (SymbolConst s1 x1) (SymbolConst s2 x2) =
  s1 == s2 && x1 == x2
llvmConstSyntacticEq (UndefConst tp1) (UndefConst tp2) =
  tp1 == tp2
llvmConstSyntacticEq (PoisonConst tp1) (PoisonConst tp2) =
  tp1 == tp2

llvmConstSyntacticEq (ZeroConst {}) _ =
  False
llvmConstSyntacticEq (IntConst {}) _ =
  False
llvmConstSyntacticEq (FloatConst {}) _ =
  False
llvmConstSyntacticEq (DoubleConst {}) _ =
  False
llvmConstSyntacticEq (LongDoubleConst {}) _ =
  False
llvmConstSyntacticEq (StringConst {}) _ =
  False
llvmConstSyntacticEq (ArrayConst {}) _ =
  False
llvmConstSyntacticEq (VectorConst {}) _ =
  False
llvmConstSyntacticEq (StructConst {}) _ =
  False
llvmConstSyntacticEq (SymbolConst {}) _ =
  False
llvmConstSyntacticEq (UndefConst {}) _ =
  False
llvmConstSyntacticEq (PoisonConst {}) _ =
  False

-- | Helper, not exported
--
-- Like 'assertEqual', but lifted to work over an 'Eq1' instance instead of an
-- 'Eq' instance. In addition, this allows the user to customize how to check
-- the underlying values (of type @expected@ and @actual@) for equality.
assertLiftEq ::
  (Eq1 f, Show (f expected), Show (f actual), HasCallStack) =>
  -- | How to check the underlying values for equality
  (expected -> actual -> Bool) ->
  -- | The expected value
  f expected ->
  -- | The actual value
  f actual ->
  Assertion
assertLiftEq eq expected actual =
  unless (liftEq eq expected actual) (assertFailure msg)
  where
    msg = "expected: " ++ show expected ++ "\n but got: " ++ show actual
