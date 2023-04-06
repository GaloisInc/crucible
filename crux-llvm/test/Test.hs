{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Exception ( SomeException, catches, try, Handler(..), IOException )
import           Control.Lens ( (^.), (^?), _Right, to )
import           Control.Monad ( guard, unless, when )
import           Data.Bifunctor ( first )
import qualified Data.ByteString.Lazy as BSIO
import qualified Data.ByteString.Lazy.Char8 as BSC
import           Data.Char ( isLetter, isSpace )
import           Data.List.Extra ( isInfixOf, isPrefixOf, stripPrefix )
import           Data.Maybe ( catMaybes, fromMaybe, mapMaybe )
import qualified Data.Set as Set
import           Data.Set ( Set )
import qualified Data.Text as T
import           Data.Versions ( Versioning, versioning, prettyV, major )
import qualified GHC.IO.Exception as GE
import           Numeric.Natural
import           System.Environment ( withArgs, lookupEnv )
import           System.Exit ( ExitCode(..) )
import           System.FilePath ( (-<.>), takeFileName )
import           System.IO
import           System.Process ( readProcess )
import           Text.Read ( readMaybe )

import qualified Test.Tasty as TT
import           Test.Tasty.HUnit ( testCase, assertFailure )
import qualified Test.Tasty.Sugar as TS

import qualified CruxLLVMMain as C


cube :: TS.CUBE
cube = TS.mkCUBE { TS.inputDirs = ["test-data/golden"]
                 , TS.rootName = "*.c"
                 , TS.separators = "."
                 , TS.expectedSuffix = "good"
                 , TS.validParams = [ ("solver", Just ["z3", "cvc5"])
                                    , ("loop-merging", Just ["loopmerge", "loop"])
                                    , ("clang-range", Just [ "recent-clang"
                                                           , "pre-clang11"
                                                           , "pre-clang12"
                                                           ])
                                    ]
                 , TS.associatedNames = [ ("config",      "config")
                                        , ("test-result", "result")
                                        ]
                 }

main :: IO ()
main = do let cubes = [ cube { TS.inputDirs = [dir], TS.rootName = rootName }
                      | dir <- [ "test-data/golden"
                               , "test-data/golden/golden"
                               , "test-data/golden/golden-loop-merging"
                               , "test-data/golden/stdio"
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

vcVersioning :: VersionCheck -> Either T.Text Versioning
vcVersioning (VC _ v) = v

mkVC :: String -> String -> VersionCheck
mkVC nm raw = let r = T.pack raw in VC nm $ first (const r) $ versioning r

-- Check if a VersionCheck version is less than the numeric value of another
-- version (represented as a Word).
vcLT :: VersionCheck -> Word -> Bool
vcLT vc verNum = (vcVersioning vc ^? (_Right . major)) < Just verNum

-- Check if a VersionCheck version is greater than or equal to the numeric
-- value of another version (represented as a Word).
vcGE :: VersionCheck -> Word -> Bool
vcGE vc verNum = (vcVersioning vc ^? (_Right . major)) >= Just verNum

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

getCVC5Version :: IO VersionCheck
getCVC5Version =
  let getVer (Right inp) =
        -- example inp: "This is cvc5 version 1.0.2\ncompiled ..."
        let w = words inp
        in if and [ length w > 4
                  , "This is cvc5 version" `isPrefixOf` inp
                  ]
           then w !! 4 else "?"
      getVer (Left full) = full
  in mkVC "cvc5" . getVer <$> readProcessVersion "cvc5"

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

sanitize :: [BSC.ByteString] -> [BSC.ByteString]
sanitize blines =
  let -- when a Callstack is reported in the result output, it contains lines like:
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
      -- If crux tries to generate and compile counter-examples, but
      -- the original source is incomplete (e.g. contains references
      -- to unresolved externals) then the crux attempt to link will
      -- fail.  The linking output generates lines like:
      --
      --   /absolute/path/of/ld: /absolute/path/for/ex3-undef-XXXXXX.o: in function `generate_value':
      --   /absolute/path/to/ex3-undef.c:11: undefined reference to `update_value'
      --
      -- Both of these outputs are problematic:
      --   1 - they contain absolute paths, which can change in different environments
      --       (the first one contains two absolute paths).
      --   2 - The XXXXXX portion is a mktemp file substitution value that will change
      --       each time the test is run.
      --
      -- The fix here is to remove the first word on the line
      -- (recursively) if it starts with a / character and ends with a
      -- : character.
      cleanLinkerOutput l =
        if BSC.null l then l
        else let (w1,rest) = BSC.break isSpace $ BSC.dropWhile isSpace l
             in if and [ "/" == BSC.take 1 w1
                       , ":" == (BSC.take 1 $ BSC.reverse w1)
                       ]
                then cleanLinkerOutput rest
                else l
  in cleanLinkerOutput . removeHashedLoc <$> blines

assertBSEq :: FilePath -> FilePath -> IO ()
assertBSEq expectedFile actualFile = do
  expected <- BSIO.readFile expectedFile
  actual <- BSIO.readFile actualFile
  let el = sanitize $ BSC.lines expected
      al = sanitize $ BSC.lines actual
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
                     , Just "--quiet"
                     ]
            failureMsg = let bss = BSIO.pack . fmap (toEnum . fromEnum) . show in \case
              Left e -> "***[test]*** Crux failed with exception: " <> bss (show (e :: SomeException)) <> "\n"
              Right (ExitFailure v) -> "***[test]*** Crux failed with non-zero result: " <> bss (show v) <> "\n"
              Right ExitSuccess -> ""
        r <- withFile outFile WriteMode $ \h ->
          (try $
            withArgs (cfargs <> [TS.rootFile sweet]) $
            let coloredOutput = False
            in (C.mainWithOutputConfig $ C.mkOutputConfig (h, coloredOutput) (h, coloredOutput) C.cruxLLVMLoggingToSayWhat))
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
      "cvc5" -> getCVC5Version
      "boolector" -> getBoolectorVersion
      _ -> return $ VC solver $ Left "unknown-solver-for-version"

    -- Match any clang version range specification in the .good
    -- expected file against the current version of clang. This implements a
    -- combination of Case 3 and Case 3a from this tasty-sugar document:
    -- https://github.com/kquick/tasty-sugar/blob/1fc06bee124e02f49f6478bc1e1df13704cc4916/Ranges.org#case-3---explicit-and-a-weaker-match
    -- In particular, we use `recent-clang` as an explicit super-supremum (as in
    -- Case 3a), but we also consult the set of Expectations in the full Sweets
    -- value to avoid generating duplicate tests for `recent-clang` (as
    -- described in Case 3).
    let clangMatch =
          let allMatchingExpectations =
                filter
                  (\e -> (tname ++ ".") `isPrefixOf` takeFileName (TS.expectedFile e))
                  (TS.expected sweet)

              supportedPreClangs :: Set Word
              supportedPreClangs =
                Set.fromList $
                mapMaybe
                  (\e -> do
                    TS.Explicit v <- lookup "clang-range" (TS.expParamsMatch e)
                    verStr <- stripPrefix "pre-clang" v
                    ver <- readMaybe verStr
                    guard $ vcLT clangVer ver
                    pure ver)
                  allMatchingExpectations

              -- Implement the "check" step described in Case 3/3a of the
              -- tasty-sugar document linked above.
              specMatchesInstalled v =
                or [ case stripPrefix "pre-clang" v of
                       Nothing -> False
                       Just verStr
                         |  Just ver <- readMaybe verStr
                         -- Check that the current Clang version is less than
                         -- the <ver> in the `pre-clang<ver>` file...
                         ,  vcLT clangVer ver
                         -- ...moreover, also check that <ver> is the closest
                         -- `pre-clang` version (without going over). For
                         -- instance, if the current Clang version is 10 and
                         -- there are both `pre-clang11` and `pre-clang12`
                         -- `.good` files, we only want to run with the
                         -- `pre-clang11` configuration to avoid duplicate
                         -- tests.
                         ,  Just closestPreClang <- Set.lookupMin supportedPreClangs
                         -> ver == closestPreClang
                         |  otherwise
                         -> False
                     -- as a fallback, if the testing code here is
                     -- unable to determine the version, run all
                     -- tests.  This is likely to cause a failure, but
                     -- is preferable to running no tests, which
                     -- results in a success report without having
                     -- done anything.
                   , vcMajor clangVer == "[missing]"
                   ]
          in -- Implement the "filter" step described in Case 3/3a of the
             -- tasty-sugar document linked above.
             case lookup "clang-range" (TS.expParamsMatch expct) of
               Just (TS.Explicit v)
                 -- Explicit matches are always allowed.
                 -> specMatchesInstalled v
               Just (TS.Assumed  v)
                 -- The only allowable Assumed match is for `recent-clang`, the
                 -- super-supremum value...
                 |  v == "recent-clang"
                 -> case Set.lookupMax supportedPreClangs of
                      -- ...if there are no `pre-clang` .good files, then allow
                      -- it...
                      Nothing -> True
                      -- ...otherwise, check that the current Clang version is
                      -- larger than anything specified by a `pre-clang` .good
                      -- file.
                      Just largestPreClang -> vcGE clangVer largestPreClang
                 |  otherwise
                 -> False
               _ -> error "clang-range unknown"

    -- Some tests take longer, so only run one of them in fast-test mode

    testLevel <- fromMaybe "0" <$> lookupEnv "CI_TEST_LEVEL"

    -- Allow issue_478_unsafe/loop-merging to always run, but identify
    -- all other tests taking 20s or greater as longTests.

    let longTests = or [ and [ TS.rootBaseName sweet == "issue_478_unsafe"
                             , fromMaybe True
                               (TS.paramMatchVal "loop" <$>
                                lookup "loop-merging" (TS.expParamsMatch expct))
                             ]
                       , TS.rootBaseName sweet == "nested"
                       , TS.rootBaseName sweet == "nested_unsafe"
                       ]

    -- If a .good file begins with SKIP_TEST, skip that test entirely. For test
    -- cases that require a minimum Clang version, this technique is used to
    -- prevent running the test on older Clang versions.

    skipTest <- ("SKIP_TEST" `BSIO.isPrefixOf`) <$> BSIO.readFile (TS.expectedFile expct)

    if or [ skipTest, not clangMatch, testLevel == "0" && longTests ]
      then do
        when (testLevel == "0" && longTests) $
          putStrLn "*** Longer running test skipped; set CI_TEST_LEVEL=1 env var to enable"
        return []
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
