{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Exception ( SomeException, try )
import qualified Data.ByteString.Lazy as BSIO
import           Data.Char ( isLetter )
import           Data.List ( isInfixOf, isPrefixOf )
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
                  , TS.validParams = [ ("solver", Just ["z3", "yices", "cvc4" ]) ]
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

getZ3Version :: IO String
getZ3Version =
  let getVer inp = let w = words inp
                   in if and [ length w > 2, head w == "Z3" ]
                      then w !! 2 else "?"
      -- example inp: "Z3 version 4.8.7 - 64 bit"
  in getVer <$> readProcess "z3" [ "--version" ] ""

getYicesVersion :: IO String
getYicesVersion =
  let getVer inp = let w = words inp
                   in if and [ length w > 1, head w == "Yices" ]
                      then w !! 1 else "?"
      -- example inp: "Yices 2.6.1\nCopyright ..."
  in getVer <$> readProcess "yices" [ "--version" ] ""

getCVC4Version :: IO String
getCVC4Version =
  let getVer inp = let w = words inp
                   in if and [ length w > 4
                             , "This is CVC4 version" `isPrefixOf` inp
                             ]
                      then w !! 4 else "?"
      -- example inp: "This is CVC4 version 1.8\ncompiled ..."
  in getVer <$> readProcess "cvc4" [ "--version" ] ""

mkTest :: TS.Sweets -> Natural -> TS.Expectation -> IO TT.TestTree
mkTest sweet _ expct =
  let solver = maybe "z3"
               (\case
                 (TS.Explicit s) -> s
                 (TS.Assumed  s) -> s
                 TS.NotSpecified -> "z3")
               $ lookup "solver" (TS.expParamsMatch expct)
      outFile = TS.expectedFile expct -<.> ".out"
      tname = TS.rootBaseName sweet
      runCruxName = tname <> " crux run"
      printFName = outFile -<.> ".print.out"

      runCrux = Just $ testCase runCruxName $ do
        let cfargs = catMaybes
                     [
                       ("--config=" <>) <$> lookup "config" (TS.associated expct)
                     , Just $ "--solver=" <> solver
                     , Just $ "--timeout=3"  -- fail if crucible cannot find a solution in 3 seconds
                     , Just $ "--goal-timeout=4"  -- fail if solver cannot find a solution in 4 seconds
                     ]
            failureMsg = let bss = BSIO.pack . fmap (toEnum . fromEnum) . show in \case
              Left e -> "*** Crux failed with exception: " <> bss (show (e :: SomeException)) <> "\n"
              Right (ExitFailure v) -> "*** Crux failed with non-zero result: " <> bss (show v) <> "\n"
              Right ExitSuccess -> ""
        r <- withFile outFile WriteMode $ \h ->
          failureMsg <$> (try $
                          withArgs (cfargs <> [TS.rootFile sweet]) $
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

  in do
    solverVer <- case solver of
      "z3" -> ("z3-v" <>) <$> getZ3Version
      "yices" -> ("yices-v" <>) <$> getYicesVersion
      "cvc4" -> ("cvc4-v" <>) <$> getCVC4Version
      _ -> return "unknown-solver-for-version"

    return $
      TT.testGroup solverVer
      [ TT.testGroup (TS.rootBaseName sweet) $ catMaybes
        [
          runCrux
        , TT.after TT.AllSucceed runCruxName <$> checkPrint
        , TT.after TT.AllSucceed runCruxName <$> checkOutput
        ]
      ]
