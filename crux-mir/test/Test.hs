{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# Language ScopedTypeVariables #-}
module Main (main) where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.UTF8 as BS8
import           Data.Char (isSpace)
import           Data.List (dropWhileEnd, isPrefixOf, sort)
import           Data.Maybe (catMaybes)
import           System.Directory (listDirectory, doesDirectoryExist, doesFileExist, removeFile)
import           System.Exit (ExitCode(..))
import           System.FilePath
    ((<.>), (</>), takeBaseName, takeExtension, replaceExtension, takeFileName, takeDirectory)
import           System.IO (IOMode(..), Handle, withFile, hClose, hGetContents, hGetLine, openFile)
import           System.IO.Temp (withSystemTempFile)

import qualified System.Process as Proc

import           Test.Tasty (defaultMain, testGroup, TestTree)
import           Test.Tasty.HUnit (Assertion, testCaseSteps, assertBool, assertFailure)
import           Test.Tasty.Golden (findByExtension)
import           Test.Tasty.Golden.Advanced (goldenTest)
import           Test.Tasty.ExpectedFailure (expectFailBecause)
import           Text.Regex.Base ( makeRegex, matchM )
import           Text.Regex.Posix.ByteString.Lazy ( Regex )

import           Mir.Defaults (defaultRustEditionFlag)
import qualified Mir.Language as Mir
import qualified Mir.Options as MirOpts

import qualified Crux as Crux
import qualified Crux.Config.Common as Crux

import qualified Config
import qualified Config.Schema as Config

type OracleTest = FilePath -> String -> (String -> IO ()) -> Assertion


-- | Check whether an input file is expected to fail based on a comment in the first line.
expectedFail :: FilePath -> IO (Maybe String)
expectedFail fn =
  withFile fn ReadMode $ \h ->
  do firstLine <- hGetLine h
     return $
       if failMarker `isPrefixOf` firstLine
         then Just (drop (length failMarker) firstLine)
         else Nothing
  where failMarker = "// FAIL: "


-- TODO: remove this - copy-pasted from Crux/Options.hs for compatibility with
-- old mainline crucible
defaultCruxOptions :: Crux.CruxOptions
defaultCruxOptions = case res of
    Left x -> error $ "failed to compute default crux options: " ++ show x
    Right x -> x
  where
    ss = Crux.cfgFile Crux.cruxOptions
    res = Config.loadValue (Config.sectionsSpec "crux" ss) (Config.Sections () [])

data RunCruxMode = RcmConcrete | RcmSymbolic | RcmCoverage
  deriving (Show, Eq)

runCrux :: FilePath -> Handle -> RunCruxMode -> IO ()
runCrux rustFile outHandle mode =
  Mir.withMirLogging $
  do
    -- goalTimeout is bumped from 60 to 180 because scalar.rs symbolic
    -- verification runs close to the timeout, causing flaky results
    -- (especially in CI).
    --
    -- The timeout is temporarily increased even further due to a performance
    -- regression (#627).  This keeps CI from breaking while we investigate.
    -- TODO: revert the timeout to 180 once performance is fixed
    let quiet = False
    let outOpts = (Crux.outputOptions defaultCruxOptions)
                    { Crux.simVerbose = 0
                    , Crux.quietMode = quiet
                    }
    let options = (defaultCruxOptions { Crux.outputOptions = outOpts,
                                        Crux.inputFiles = [rustFile],
                                        Crux.globalTimeout = Just 600,
                                        Crux.goalTimeout = Just 600,
                                        Crux.solver = "z3",
                                        Crux.checkPathSat = (mode == RcmCoverage),
                                        Crux.outDir = case mode of
                                            RcmCoverage -> getOutputDir rustFile
                                            _ -> "",
                                        Crux.branchCoverage = (mode == RcmCoverage) } ,
                   MirOpts.defaultMirOptions { MirOpts.printResultOnly = (mode == RcmConcrete) })
    let ?outputConfig = Crux.mkOutputConfig (outHandle, False) (outHandle, False) Mir.mirLoggingToSayWhat $
                        Just (Crux.outputOptions (fst options))
    _exitCode <- Mir.runTests options
    return ()

getOutputDir :: FilePath -> FilePath
getOutputDir rustFile = takeDirectory rustFile </> "out"

cruxOracleTest :: FilePath -> String -> (String -> IO ()) -> Assertion
cruxOracleTest dir name step = do

  step "Compiling and running oracle program"
  oracleOut <- compileAndRun dir name >>= \case
    Nothing -> assertFailure "failed to compile and run"
    Just out -> return out

  let orOut = dropWhileEnd isSpace oracleOut
  step ("Oracle output: " ++ orOut)

  let rustFile = dir </> name <.> "rs"

  cruxOut <- withSystemTempFile name $ \tempName h -> do
    runCrux rustFile h RcmConcrete
    hClose h
    h' <- openFile tempName ReadMode
    out <- hGetContents h'
    length out `seq` hClose h'
    return $ dropWhileEnd isSpace out

  step ("Crux output: " ++ cruxOut ++ "\n")
  assertBool "crux doesn't match oracle" (orOut == cruxOut)


symbTest :: FilePath -> IO TestTree
symbTest dir =
  do rustFiles <- findByExtension [".rs"] dir
     return $
       testGroup "Output testing"
         [ doGoldenTest (takeBaseName rustFile) goodFile outFile $
           do withFile outFile WriteMode $ \h ->
                runCrux rustFile h RcmSymbolic
              sanitizeGoldenOutputFile outFile
         | rustFile <- rustFiles
         -- Skip hidden files, such as editor swap files
         , not $ "." `isPrefixOf` takeFileName rustFile
         , let goodFile = replaceExtension rustFile ".good"
         , let outFile = replaceExtension rustFile ".out"
         ]

coverageTests :: FilePath -> IO TestTree
coverageTests dir = do
    rustFiles <- findByExtension [".rs"] dir
    return $ testGroup "Output testing"
        [ doGoldenTest rustFile goodFile outFile (doTest rustFile outFile)
        | rustFile <- rustFiles
        -- Skip hidden files, such as editor swap files
        , not $ "." `isPrefixOf` takeFileName rustFile
        , let goodFile = replaceExtension rustFile ".good"
        , let outFile = replaceExtension rustFile ".out"
        ]

  where
    doTest rustFile outFile = do
        let logFile = replaceExtension rustFile ".crux.log"
        withFile logFile WriteMode $ \h -> runCrux rustFile h RcmCoverage
        let reportDir = getOutputDir rustFile </> takeBaseName rustFile
        reportFiles <- findByExtension [".js"] reportDir
        out <- Proc.readProcess "cargo"
            (["run", "--manifest-path", "report-coverage/Cargo.toml", "--quiet",
                "--", "--no-color"] ++ reportFiles) ""
        writeFile outFile out



doGoldenTest :: FilePath -> FilePath -> FilePath -> IO () -> TestTree
doGoldenTest rustFile goodFile outFile act = goldenTest (takeBaseName rustFile)
    (BS.readFile goodFile)
    (act >> BS.readFile outFile)
    (\good out -> return $ if good == out then Nothing else
      let el = BSC.lines good
          al = BSC.lines out in

      let dl (e,a) = if e == a then db e else de e <> da a
          db b = ["    F        |" <> b]
          de e = ["    F-expect>|" <> e]
          da a = ["    F-actual>|" <> a] in

      let details = concat $
                    [ [ "MISMATCH for expected (" <> BS8.fromString goodFile <> ")"
                      , "           and actual (" <> BS8.fromString outFile <> ") output:"
                      ]
                      -- Highly simplistic "diff" output assumes
                      -- correlated lines: added or removed lines just
                      -- cause everything to shown as different from
                      -- that point forward.
                    , concatMap dl $ zip el al
                    , concatMap de $ drop (length al) el
                    , concatMap da $ drop (length el) al
                    ] in
      Just $ BS8.toString (BSC.unlines details))
    (\out -> BS.writeFile goodFile out)

-- | Sanitize the golden output in a file.
sanitizeGoldenOutputFile :: FilePath -> IO ()
sanitizeGoldenOutputFile file = do
  out <- BS.readFile file
  BS.writeFile file $ sanitizeGoldenTestOutput out

-- | Replace occurrences of crate disambiguators (which are highly sensitive to
-- the contents of crates' source code) with more stable output to reduce churn
-- in the golden tests.
sanitizeGoldenTestOutput :: BS.ByteString -> BS.ByteString
sanitizeGoldenTestOutput = go
  where
    go :: BS.ByteString -> BS.ByteString
    go out
      | Just (before, _matched :: BS.ByteString, after, [preDisamb])
          <- matchM disambRE out
      = before <> preDisamb <> "<DISAMB>::" <> go after
      | otherwise
      = out

    disambRE :: Regex
    disambRE = makeRegex disambBS

    -- A disambiguator looks something like foo/a1b4j89a, i.e., an alphanumeric
    -- string that starts with an alphabetic character, followed by a forward
    -- slash, followed by eight alphanumeric characters. To reduce the rate of
    -- false positives, we also match two trailing colons, which would be
    -- present when printing out a full DefId (e.g., foo/a1b4j89a::Bar::Baz).
    disambBS :: BS.ByteString
    disambBS = "([A-Za-z_]" <> alphaNum <> "*/)" <> mconcat (replicate 8 alphaNum) <> "::"

    alphaNum :: BS.ByteString
    alphaNum = "[A-Za-z0-9_]"

main :: IO ()
main = defaultMain =<< suite

suite :: IO TestTree
suite = do
  let ?debug = 0 :: Int
  let ?assertFalseOnError = True
  let ?printCrucible = False
  trees <- sequence
           [ testGroup "crux concrete" <$> sequence [ testDir cruxOracleTest "test/conc_eval/" ]
           , testGroup "crux symbolic" <$> sequence [ symbTest "test/symb_eval" ]
           , testGroup "crux coverage" <$> sequence [ coverageTests "test/coverage" ]
           ]
  return $ testGroup "crux-mir" trees





-- | Compile using 'rustc' and run executable
compileAndRun :: FilePath -> String -> IO (Maybe String)
compileAndRun dir name = do
  (ec, _, err) <- Proc.readProcessWithExitCode "rustc"
    [dir </> name <.> "rs", defaultRustEditionFlag, "--cfg", "with_main"
    , "--extern", "byteorder=rlibs_native/libbyteorder.rlib"
    , "--extern", "bytes=rlibs_native/libbytes.rlib"] ""
  case ec of
    ExitFailure _ -> do
      putStrLn $ "rustc compilation failed for " ++ name
      putStrLn "error output:"
      putStrLn err
      return Nothing
    ExitSuccess -> do
      let execFile = "." </> name
      (ec', out, _) <- Proc.readProcessWithExitCode execFile [] ""
      doesFileExist execFile >>= \case
        True -> removeFile execFile
        False -> return ()
      case ec' of
        ExitFailure _ -> do
          putStrLn $ "non-zero exit code for test executable " ++ name
          return Nothing
        ExitSuccess -> return $ Just out


testDir :: OracleTest -> FilePath -> IO TestTree
testDir oracleTest dir = do
  let gen f | "." `isPrefixOf` takeBaseName f = return Nothing
      gen f | takeExtension f == ".rs" = do
                shouldFail <- expectedFail (dir </> f)
                case shouldFail of
                  Nothing -> return (Just (testCaseSteps name (oracleTest dir name)))
                  Just why -> return (Just (expectFailBecause why (testCaseSteps name (oracleTest dir name))))
        where name = takeBaseName f
      gen f = doesDirectoryExist (dir </> f) >>= \case
        False -> return Nothing
        True -> Just <$> testDir oracleTest (dir </> f)
  -- This `sort` is not technically necessary, it just ensures that test cases
  -- will be performed in a stable ordering, since `listDirectory` doesn't
  -- guarantee such an ordering.
  fs <- sort <$> listDirectory dir
  tcs <- mapM gen fs
  return (testGroup (takeBaseName dir) (catMaybes tcs))
