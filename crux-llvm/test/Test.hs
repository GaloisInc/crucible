{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Exception ( SomeException, try )
import qualified Data.ByteString.Lazy as BSIO
import           Data.Char ( isLetter )
import           Data.List ( isInfixOf )
import           Data.Maybe ( catMaybes, fromMaybe )
import           Numeric.Natural
import           System.Environment ( withArgs, lookupEnv )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>) )
import           System.IO
import           System.Process ( readProcess )

import qualified Test.Tasty as TT
import           Test.Tasty.HUnit ( (@=?), testCase )
import qualified Test.Tasty.Sugar as TS

import qualified Crux.Log as C
import qualified CruxLLVMMain as C


cCube, llCube :: TS.CUBE
cCube = TS.mkCUBE { TS.inputDir = "test-data/golden"
                  , TS.rootName = "*.c"
                  , TS.expectedSuffix = "good"
                  , TS.associatedNames = [ ("config", "config")
                                         , ("stdio",  "print")
                                         ]
                  }

llCube = cCube { TS.rootName = "*.ll" }

main :: IO ()
main = do sweets <- concat <$> mapM TS.findSugar [cCube, llCube]
          clangVer <- getClangVersion
          tests <- TS.withSugarGroups sweets TT.testGroup mkTest

          let ingredients = TT.includingOptions TS.sugarOptions :
                            TS.sugarIngredients [cCube, llCube] <>
                            TT.defaultIngredients
          TT.defaultMainWithIngredients ingredients $
            TT.testGroup "crux-llvm"
            [ TT.testGroup ("clang " <> clangVer) $ tests ]


getClangVersion :: IO String
getClangVersion = do
  -- Determine which version of clang will be used for these tests.
  -- An exception (E.g. in the readProcess if clang is not found) will
  -- result in termination (test failure).  Uses partial 'head' but
  -- this is just tests, and failure is captured.
  clangBin <- fromMaybe "clang" <$> lookupEnv "CLANG"
  let isVerLine = isInfixOf "clang version"
      dropLetter = dropWhile (all isLetter)
      getVer = head . dropLetter . words . head . filter isVerLine . lines
  getVer <$> readProcess clangBin [ "--version" ] ""


mkTest :: TS.Sweets -> Natural -> TS.Expectation -> IO TT.TestTree
mkTest sweet _ expct =
  let outFile = TS.expectedFile expct -<.> ".out"
      tname = TS.rootBaseName sweet
      runCruxName = tname <> " crux run"
      printFName = outFile -<.> ".print.out"

      runCrux = Just $ testCase runCruxName $ do
        let cfargs = maybe [] (\c -> ["--config=" <> c]) $
                     lookup "config" (TS.associated expct)
            failureMsg = let bss = BSIO.pack . fmap (toEnum . fromEnum) . show in \case
              Left e -> "*** Crux failed with exception: " <> bss (show (e :: SomeException)) <> "\n"
              Right (ExitFailure v) -> "*** Crux failed with non-zero result: " <> bss (show v) <> "\n"
              Right ExitSuccess -> ""
        r <- withFile outFile WriteMode $ \h ->
          failureMsg <$> (try $
                          withArgs (["--solver=z3", TS.rootFile sweet] ++ cfargs) $
                          -- Quiet mode, don't print colors
                          let quietMode = True in
                          C.mainWithOutputConfig (C.OutputConfig False h h quietMode))
        BSIO.writeFile printFName r

      checkPrint =
        let runTest s = testCase (tname <> " crux print") $
                        do r <- BSIO.readFile printFName
                           BSIO.readFile s >>= (@=? r)
        in runTest <$> lookup "stdio" (TS.associated expct)

      checkOutput = Just $ testCase (tname <> " crux output") $ do
        good <- BSIO.readFile (TS.expectedFile expct)
        (good @=?) =<< BSIO.readFile outFile

  in return $ TT.testGroup (TS.rootBaseName sweet) $ catMaybes
     [
       runCrux
     , TT.after TT.AllSucceed runCruxName <$> checkPrint
     , TT.after TT.AllSucceed runCruxName <$> checkOutput
     ]
