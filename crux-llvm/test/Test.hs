{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Exception ( SomeException, catches, try, Handler(..), IOException )
import           Control.Monad ( unless )
import           Data.Bifunctor ( first )
import qualified Data.ByteString.Lazy as BSIO
import qualified Data.ByteString.Lazy.Char8 as BSC
import           Data.Char ( isLetter )
import           Data.List ( isInfixOf, isPrefixOf )
import           Data.Maybe ( catMaybes, fromMaybe, isJust )
import qualified Data.Text as T
import           Data.Versions ( Versioning, versioning, prettyV, major )
import qualified GHC.IO.Exception as GE
import           Lens.Micro ( (^.), to )
import           Numeric.Natural
import           System.Environment ( withArgs, lookupEnv )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>) )
import           System.IO
import           System.Process ( readProcess )

import qualified Test.Tasty as TT
import           Test.Tasty.HUnit ( testCase, assertFailure )
import qualified Test.Tasty.Sugar as TS

import qualified Crux.Log as C
import qualified CruxLLVMMain as C


cube :: TS.CUBE
cube = TS.mkCUBE { TS.inputDir = "test-data/golden"
                 , TS.rootName = "*.c"
                 , TS.separators = "."
                 , TS.expectedSuffix = "good"
                 , TS.validParams = [ ("solver", Just ["z3"])
                                    , ("loop-merging", Just ["loopmerge", "loop"])
                                    , ("clang-range", Just ["pre-clang11", "clang11", "clang12"])
                                    ]
                 , TS.associatedNames = [ ("config",      "config")
                                        , ("test-result", "result")
                                        , ("skip",        "skip")   -- when present, test config is skipped
                                        ]
                 }

main :: IO ()
main = do let cubes = [ cube { TS.inputDir = dir, TS.rootName = rootName }
                      | dir <- [ "test-data/golden"
                               , "test-data/golden/golden"
                               , "test-data/golden/golden-loop-merging"
                               ]
                      , rootName <- [ "*.c", "*.ll" ]
                      ]
          sweets <- concat <$> mapM TS.findSugar cubes
          clangVer <- getClangVersion
          tests <- TS.withSugarGroups sweets TT.testGroup (mkTest clangVer)

          let ingredients = TT.includingOptions TS.sugarOptions :
                            TS.sugarIngredients cubes <>
                            TT.defaultIngredients
          TT.defaultMainWithIngredients ingredients $
            TT.testGroup "crux-llvm"
            [ TT.testGroup (showVC clangVer) $ tests ]


-- lack of decipherable version is not fatal to running the tests
data VersionCheck = VC String (Either T.Text Versioning)

showVC :: VersionCheck -> String
showVC (VC nm v) = nm <> " " <> (T.unpack $ either id prettyV v)

vcTag :: VersionCheck -> String
vcTag v@(VC nm _) = nm <> vcMajor v

vcMajor :: VersionCheck -> String
vcMajor (VC _ v) = either T.unpack (^. major . to show) v

mkVC :: String -> String -> VersionCheck
mkVC nm raw = let r = T.pack raw in VC nm $ first (const r) $ versioning r

getClangVersion :: IO VersionCheck
getClangVersion = do
  -- Determine which version of clang will be used for these tests.
  -- An exception (E.g. in the readProcess if clang is not found) will
  -- result in termination (test failure).  Uses partial 'head' but
  -- this is just tests, and failure is captured.
  clangBin <- fromMaybe "clang" <$> lookupEnv "CLANG"
  let isVerLine = isInfixOf "clang version"
      dropLetter = dropWhile (all isLetter)
      getVer (Right inp) =
        -- example inp: "clang version 10.0.1"
        head $ dropLetter $ words $ head $ filter isVerLine $ lines inp
      getVer (Left full) = full
  mkVC "clang" . getVer <$> readProcessVersion clangBin

getZ3Version :: IO VersionCheck
getZ3Version =
  let getVer (Right inp) =
        -- example inp: "Z3 version 4.8.7 - 64 bit"
        let w = words inp
        in if and [ length w > 2, head w == "Z3" ]
           then w !! 2 else "?"
      getVer (Left full) = full
  in mkVC "z3" . getVer <$> readProcessVersion "z3"

getYicesVersion :: IO VersionCheck
getYicesVersion =
  let getVer (Right inp) =
        -- example inp: "Yices 2.6.1\nCopyright ..."
        let w = words inp
        in if and [ length w > 1, head w == "Yices" ]
           then w !! 1 else "?"
      getVer (Left full) = full
  in mkVC "yices" . getVer <$> readProcessVersion "yices"

getSTPVersion :: IO VersionCheck
getSTPVersion =
  let getVer (Right inp) =
        -- example inp: "STP version 2.3.3\n..."
        let w = words inp
        in if and [ length w > 2
                  , head w == "STP"
                  , w !! 1 == "version" ]
           then w !! 2 else "?"
      getVer (Left full) = full
  in mkVC "stp" . getVer <$> readProcessVersion "stp"

getCVC4Version :: IO VersionCheck
getCVC4Version =
  let getVer (Right inp) =
        -- example inp: "This is CVC4 version 1.8\ncompiled ..."
        let w = words inp
        in if and [ length w > 4
                  , "This is CVC4 version" `isPrefixOf` inp
                  ]
           then w !! 4 else "?"
      getVer (Left full) = full
  in mkVC "cvc4" . getVer <$> readProcessVersion "cvc4"

getBoolectorVersion :: IO VersionCheck
getBoolectorVersion =
  let getVer (Right inp) =
        -- example inp: "3.2.1"
        let w = words inp
        in if not (null w) then head w else "?"
      getVer (Left full) = full
  in mkVC "boolector" . getVer <$> readProcessVersion "boolector"

readProcessVersion :: String -> IO (Either String String)
readProcessVersion forTool =
  catches (Right <$> readProcess forTool [ "--version" ] "")
  [ Handler $ \(e :: IOException) ->
      if GE.ioe_type e == GE.NoSuchThing
      then return $ Left "[missing]" -- tool executable not found
      else do putStrLn $ "Warning: IO error attempting to determine " <> forTool <> " version:"
              putStrLn $ show e
              return $ Left "unknown"
  , Handler $ \(e :: SomeException) -> do
      putStrLn $ "Warning: error attempting to determine " <> forTool <> " version:"
      putStrLn $ show e
      return $ Left "??"
  ]

assertBSEq :: FilePath -> FilePath -> IO ()
assertBSEq expectedFile actualFile = do
  expected <- BSIO.readFile expectedFile
  actual <- BSIO.readFile actualFile
  let el = removeHashedLoc <$> BSC.lines expected
      al = removeHashedLoc <$> BSC.lines actual
      -- when a Callstack is reported in the result output, it contains like like:
      --
      -- >  error, called at src/foo.hs:369:3 in pkgname-1.0.3.5-{cabal-hash-loc}:Foo
      --
      -- and the problem is that {cabal-hash-loc} varies, so
      -- removeHashedLoc attempts to strip that portion from these
      -- lines.
      removeHashedLoc l =
        let w = BSC.words l
        in if take 3 w == ["error,", "called", "at"]
           then BSC.unwords $ take 4 w
           else l
  unless (el == al) $ do
    let dl (e,a) = if e == a then db e else de e <> da a
        db b = ["    F        |" <> b]
        de e = ["    F-expect>|" <> e]
        da a = ["    F-actual>|" <> a]
    let details = concat $
                  [ [ "MISMATCH for expected (" <> BSC.pack expectedFile <> ")"
                    , "           and actual (" <> BSC.pack actualFile <> ") output:"
                    ]
                    -- Highly simplistic "diff" output assumes
                    -- correlated lines: added or removed lines just
                    -- cause everything to shown as different from
                    -- that point forward.
                  , concatMap dl $ zip el al
                  , concatMap de $ drop (length al) el
                  , concatMap da $ drop (length el) al
                  ]
    assertFailure $ BSC.unpack (BSC.unlines details)


mkTest :: VersionCheck -> TS.Sweets -> Natural -> TS.Expectation -> IO [TT.TestTree]
mkTest clangVer sweet _ expct =
  let solver = maybe "z3"
               (\case
                 (TS.Explicit s) -> s
                 (TS.Assumed  s) -> s
                 TS.NotSpecified -> "z3")
               $ lookup "solver" (TS.expParamsMatch expct)
      outFile = TS.expectedFile expct -<.> "." <> solver <> ".out"
      tname = TS.rootBaseName sweet
      runCruxName = tname <> " crux run"
      resFName = outFile -<.> ".result.out"

      runCrux = Just $ testCase runCruxName $ do
        let cfargs = catMaybes
                     [
                       ("--config=" <>) <$> lookup "config" (TS.associated expct)
                     , Just $ "--solver=" <> solver
                     ]
            failureMsg = let bss = BSIO.pack . fmap (toEnum . fromEnum) . show in \case
              Left e -> "***[test]*** Crux failed with exception: " <> bss (show (e :: SomeException)) <> "\n"
              Right (ExitFailure v) -> "***[test]*** Crux failed with non-zero result: " <> bss (show v) <> "\n"
              Right ExitSuccess -> ""
        r <- withFile outFile WriteMode $ \h ->
          (try $
            withArgs (cfargs <> [TS.rootFile sweet]) $
            -- Quiet mode, don't print colors
            let quietMode = True in
              C.mainWithOutputConfig (C.OutputConfig False h h quietMode))
        BSIO.writeFile resFName $ failureMsg r

      checkResult =
        let runTest s = testCase (tname <> " crux result") $
                        assertBSEq s resFName
        in runTest <$> lookup "test-result" (TS.associated expct)

      checkOutput = Just $ testCase (tname <> " crux output") $
                    assertBSEq (TS.expectedFile expct) outFile

  in do
    solverVer <- showVC <$> case solver of
      "z3" -> getZ3Version
      "yices" -> getYicesVersion
      "stp" -> getSTPVersion
      "cvc4" -> getCVC4Version
      "boolector" -> getBoolectorVersion
      _ -> return $ VC solver $ Left "unknown-solver-for-version"

    -- Match any clang version range specification in the .good
    -- expected file against the current version of clang.  If the
    -- current clang version doesn't match, no test should be
    -- generated (i.e. only run tests for the version of clang
    -- available).
    let clangMatch =
          let specMatchesInstalled v =
                or [ v == vcTag clangVer
                   , and [ v == "pre-clang11"
                         , vcMajor clangVer `elem` (show <$> [3..10 :: Int])
                         ]
                   ]
          in case lookup "clang-range" (TS.expParamsMatch expct) of
               Just (TS.Explicit v) -> specMatchesInstalled v
               Just (TS.Assumed  v) -> specMatchesInstalled v
               _ -> error "clang-range unknown"

    -- Presence of a .skip file means this test should be skipped.

    let skipTest = isJust $ lookup "skip" (TS.associated expct)

    if or [ skipTest, not clangMatch ]
      then return []
      else do
        let isLoopMerge = TS.paramMatchVal "loopmerge" <$>
                        lookup "loop-merging" (TS.expParamsMatch expct)
            cfg = lookup "config" (TS.associated expct)
        case (isLoopMerge, cfg) of
          (Just True, Nothing) ->
            -- No config for loopmerge, so suppress identical run.
            -- This is an optimization: it would not be wrong to run
            -- these tests, but since the loopmerge and loop
            -- configurations are identical, extra tests are run that
            -- don't provide any additional information.
            return []
          _ -> return
               [
                 TT.testGroup solverVer
                 [ TT.testGroup (TS.rootBaseName sweet) $ catMaybes
                   [
                     runCrux
                   , TT.after TT.AllSucceed runCruxName <$> checkResult
                   , TT.after TT.AllSucceed runCruxName <$> checkOutput
                   ]
                 ]
               ]
