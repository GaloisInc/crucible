{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
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

import           Mir.Generate(loadPrims)
import           Mir.SAWInterface (translateMIR, extractMIR, loadMIR)
import qualified Mir.Language as Mir

import qualified Lang.Crucible.FunctionHandle as C

import qualified Crux.Options as CruxOpts
import qualified Crux.CruxMain as Crux
import qualified Crux.Log as Crux

import qualified Data.AIG.Interface as AIG

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


runCrux :: Mir.CachedStdLib -> FilePath -> Handle -> IO ()
runCrux cachedLib rustFile outHandle = do
    -- goalTimeout is bumped from 60 to 120 because scalar.rs symbolic
    -- verification runs close to the timeout, causing flaky results.
    let options = (CruxOpts.defaultCruxOptions { CruxOpts.inputFile = rustFile,
                                                 CruxOpts.simVerbose = 0,
                                                 CruxOpts.goalTimeout = 120 } ,
                   Mir.defaultMirOptions { Mir.cachedStdLib = Nothing -- Just cachedLib
                                         , Mir.useStdLib = True } )
    let ?outputConfig = Crux.OutputConfig False outHandle outHandle
    Crux.check options

cruxOracleTest :: Mir.CachedStdLib -> FilePath -> String -> (String -> IO ()) -> Assertion
cruxOracleTest cachedLib dir name step = do

  step "Compiling and running oracle program"
  oracleOut <- compileAndRun dir name >>= \case
    Nothing -> assertFailure "failed to compile and run"
    Just out -> return out

  let orOut = dropWhileEnd isSpace oracleOut
  step ("Oracle output: " ++ orOut)

  let rustFile = dir </> name <.> "rs"
  
  cruxOutFull <- withSystemTempFile name $ \tempName h -> do
    runCrux cachedLib rustFile h
    hClose h
    h' <- openFile tempName ReadMode
    out <- hGetContents h'
    length out `seq` hClose h'
    return out

  let cruxOut = dropWhileEnd isSpace cruxOutFull
  step ("Crux output: " ++ cruxOut ++ "\n")
  assertBool "crux doesn't match oracle" (orOut == cruxOut)


sawOracleTest :: FilePath -> String -> (String -> IO ()) -> Assertion
sawOracleTest dir name step = do
  sc <- SC.mkSharedContext
  step "Initializing saw-core Prelude"
  SC.tcInsertModule sc SC.preludeModule

  step "Compiling and running oracle program"
  oracleOut <- compileAndRun dir name >>= \case
    Nothing -> assertFailure "failed to compile and run"
    Just out -> return out

  step $ "Oracle output: " ++ dropWhileEnd isSpace oracleOut

  step "Generating MIR JSON"


  step "Translating MIR to Crucible"
  mir <- loadMIR sc name
  
  step "Extracting function f"
  f <- extractMIR proxy sc mir "f"
  step "Extracting argument ARG"
  arg <- extractMIR proxy sc mir "ARG"
  step "Typechecking f(ARG)"
  app <- SC.scApply sc f arg
  rty <- SC.scTypeCheck sc Nothing app >>= \case
    Left e -> assertFailure $ "ill-typed result: " ++ unwords (SC.prettyTCError e)
    Right rty -> return rty
  ty <- FV.asFiniteType sc rty

  step "Parsing oracle output at inferred type"
  oracle <- case parse (parseRustFV ty) "oracleOut" oracleOut of
    Left e -> error $ "error parsing Rust output: " ++ show e
    Right (Just fv) -> FV.scFiniteValue sc fv
    Right Nothing -> assertFailure "panics not yet handled"

  step "Comparing oracle output"
  eq <- SC.scEq sc oracle app
  mm <- SC.scGetModuleMap sc
  assertBool "oracle output mismatch"
    (Conc.toBool (Conc.evalSharedTerm mm Map.empty eq))


symbTest :: Mir.CachedStdLib -> FilePath -> IO TestTree
symbTest cachedLib dir =
  do rustFiles <- findByExtension [".rs"] dir
     return $
       testGroup "Output testing"
         [ goldenVsFile (takeBaseName rustFile) goodFile outFile $
           withFile outFile WriteMode $ \h ->
           runCrux cachedLib rustFile h
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
  halloc <- C.newHandleAllocator
  prims  <- liftIO $ loadPrims True
  pmir   <- stToIO $ translateMIR mempty prims halloc
  let cachedLib = Mir.CachedStdLib pmir halloc
  trees <- sequence 
           [ --testGroup "saw"  <$> sequence [testDir sawOracleTest "test/conc_eval"  ]
             testGroup "crux concrete" <$> sequence [ testDir (cruxOracleTest cachedLib) "test/conc_eval/" ]
           , testGroup "crux symbolic" <$> sequence [ symbTest cachedLib "test/symb_eval" ]
           ]
  return $ testGroup "mir-verifier" trees





-- For newSAWCoreBackend
proxy :: AIG.Proxy AIG.BasicLit AIG.BasicGraph
proxy = AIG.basicProxy

-- | Compile using 'rustc' and run executable
compileAndRun :: FilePath -> String -> IO (Maybe String)
compileAndRun dir name = do
  (ec, _, err) <- Proc.readProcessWithExitCode "rustc" [dir </> name <.> "rs", "--cfg", "with_main"] ""
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
