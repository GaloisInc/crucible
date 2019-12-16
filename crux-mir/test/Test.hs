{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# Language OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -fno-warn-unused-top-binds #-}

import           Control.Monad.ST
import           Control.Monad.IO.Class
import           Data.Char (isSpace)
import           Data.Functor(($>))
import           Data.List (dropWhileEnd, isPrefixOf)
import qualified Data.Map as Map
import           Data.Maybe (catMaybes)
import           System.Directory (listDirectory, doesDirectoryExist, doesFileExist, removeFile)
import           System.Exit (ExitCode(..))
import           System.FilePath ((<.>), (</>), takeBaseName, takeExtension, replaceExtension)
import           System.IO (IOMode(..), Handle, withFile, hClose, hGetContents, hGetLine, openFile)
import           System.IO.Temp (withSystemTempFile)

import qualified System.Process as Proc
import           Text.Parsec (parse, (<|>), (<?>), string, many1, digit)
import           Text.Parsec.String (Parser)

import qualified Verifier.SAW.FiniteValue as FV
import qualified Verifier.SAW.Prelude as SC
import qualified Verifier.SAW.SCTypeCheck as SC
import qualified Verifier.SAW.SharedTerm as SC
import qualified Verifier.SAW.Typechecker as SC
import qualified Verifier.SAW.Simulator.Concrete as Conc

import           Test.Tasty (defaultMain, testGroup, TestTree)
import           Test.Tasty.HUnit (Assertion, testCaseSteps, assertBool, assertFailure)
import           Test.Tasty.Golden (goldenVsFile, findByExtension)
import           Test.Tasty.ExpectedFailure (expectFailBecause)

import qualified Mir.Language as Mir

import qualified Lang.Crucible.FunctionHandle as C

import qualified Crux as Crux
import qualified Crux.Config as Crux
import qualified Crux.Config.Common as Crux
import qualified Crux.Log as Crux

import qualified Data.AIG.Interface as AIG

import qualified Config
import qualified Config.Schema as Config
import qualified Config.Schema.Load as Config
import qualified Config.Schema.Spec as Config

type OracleTest = FilePath -> String -> (String -> IO ()) -> Assertion


-- Don't show any debug output when testing (SAWInterface)
debugLevel :: Int
debugLevel = 0


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

runCrux :: FilePath -> Handle -> IO ()
runCrux rustFile outHandle = do
    -- goalTimeout is bumped from 60 to 120 because scalar.rs symbolic
    -- verification runs close to the timeout, causing flaky results.
    let options = (defaultCruxOptions { Crux.inputFiles = [rustFile],
                                        Crux.simVerbose = 0,
                                        Crux.globalTimeout = Just 120,
                                        Crux.goalTimeout = Just 120,
                                        Crux.solver = "z3" } ,
                   Mir.defaultMirOptions)
    let language = Mir.mirLanguage { Crux.initialize = \_ -> return options }
    let outputConfig = Crux.OutputConfig False outHandle outHandle
    Crux.mainWithOutputConfig outputConfig language

cruxOracleTest :: FilePath -> String -> (String -> IO ()) -> Assertion
cruxOracleTest dir name step = do

  step "Compiling and running oracle program"
  oracleOut <- compileAndRun dir name >>= \case
    Nothing -> assertFailure "failed to compile and run"
    Just out -> return out

  let orOut = dropWhileEnd isSpace oracleOut
  step ("Oracle output: " ++ orOut)

  let rustFile = dir </> name <.> "rs"
  
  cruxOutFull <- withSystemTempFile name $ \tempName h -> do
    runCrux rustFile h
    hClose h
    h' <- openFile tempName ReadMode
    out <- hGetContents h'
    length out `seq` hClose h'
    return out

  let cruxOut = filterCruxOut cruxOutFull
  step ("Crux output: " ++ cruxOut ++ "\n")
  assertBool "crux doesn't match oracle" (orOut == cruxOut)

filterCruxOut x =
    dropWhileEnd isSpace $
    unlines $
    filter (\l -> not $ "[Crux]" `isPrefixOf` l) $
    lines x


symbTest :: FilePath -> IO TestTree
symbTest dir =
  do rustFiles <- findByExtension [".rs"] dir
     return $
       testGroup "Output testing"
         [ goldenVsFile (takeBaseName rustFile) goodFile outFile $
           withFile outFile WriteMode $ \h ->
           runCrux rustFile h
         | rustFile <- rustFiles
         , notHidden rustFile
         , let goodFile = replaceExtension rustFile ".good"
         , let outFile = replaceExtension rustFile ".out"
         ]
 where
   notHidden "" = True
   notHidden ('.' : _) = False
   notHidden _ = True

main :: IO ()
main = defaultMain =<< suite

suite :: IO TestTree
suite = do
  let ?debug = 0
  let ?assertFalseOnError = True
  let ?printCrucible = False
  trees <- sequence 
           [ testGroup "crux concrete" <$> sequence [ testDir cruxOracleTest "test/conc_eval/" ]
           , testGroup "crux symbolic" <$> sequence [ symbTest "test/symb_eval" ]
           ]
  return $ testGroup "mir-verifier" trees





-- For newSAWCoreBackend
proxy :: AIG.Proxy AIG.BasicLit AIG.BasicGraph
proxy = AIG.basicProxy

-- | Compile using 'rustc' and run executable
compileAndRun :: FilePath -> String -> IO (Maybe String)
compileAndRun dir name = do
  (ec, _, err) <- Proc.readProcessWithExitCode "rustc"
    [dir </> name <.> "rs", "--cfg", "with_main"
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
  fs <- listDirectory dir
  tcs <- mapM gen fs
  return (testGroup (takeBaseName dir) (catMaybes tcs))

-- | Parse the Rust program output into a finite value at a given type
parseRustFV :: FV.FiniteType -> Parser (Maybe FV.FiniteValue)
parseRustFV ft = panic <|> (Just <$> p)
  where
    panic = string "<<PANIC>>" $> Nothing
    p = case ft of
          FV.FTBit ->
                string "true"  $> FV.FVBit True
            <|> string "false" $> FV.FVBit False
            <?> "boolean"
          FV.FTVec w FV.FTBit -> do
            i <- read <$> many1 digit
            return (FV.FVWord w i)
          FV.FTVec _n _elt -> error "unimplemented"
          FV.FTTuple _elts -> error "unimplemented"
          FV.FTRec _fields -> error "unimplemented"
