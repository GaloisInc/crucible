module Main where

import Control.Monad
import qualified Data.Map as M
import Data.List

import System.IO
import System.Console.GetOpt
import System.Environment
import System.FilePath

import qualified Verifier.SAW.ParserUtils as SC
import Verifier.SAW.Prelude (preludeModule)

import SAWScript.AST
import SAWScript.BuildModule as BM
import SAWScript.Compiler
import SAWScript.Execution
import SAWScript.Import
import SAWScript.MGU (checkModule)
import SAWScript.Options
import SAWScript.RenameRefs as RR
import SAWScript.ResolveSyns
import SAWScript.ToSAWCore

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
    (_, [], [])       -> putStrLn (usageInfo header options)
    (opts, files, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      processFiles opts'' files
    (_, _, errs)      ->
      hPutStrLn stderr (concat errs ++ usageInfo header options)
  where header = "Usage: saw [OPTION...] files..."

processFiles :: Options -> [FilePath] -> IO ()
processFiles opts = mapM_ (processFile opts)

processFile :: Options -> FilePath -> IO ()
processFile opts file | takeExtensions file == ".sawcore" = do
  sawScriptPrelude <- SC.readModuleFromFile [preludeModule] "examples/prelude.sawcore"
  m <- SC.readModuleFromFile [preludeModule, sawScriptPrelude] file
  execSAWCore opts m
processFile opts file | takeExtensions file == ".saw" = do
  loadAll opts file (mapM_ processModule . M.toList . modules)
processFile _ file = putStrLn $ "Don't know how to handle file " ++ file

processModule :: (Name, [TopStmtSimple RawT]) -> IO ()
processModule (name, ss) =
  runCompiler (buildModule >=> resolveSyns >=> renameRefs) im $ \m -> do
    case checkModule m of
      Left err -> mapM_ putStrLn err
      Right cm -> print cm
  where im = (ModuleName [] name, ss)

-- | Wrapper around compiler function to format the result or error
runCompiler :: (Show b) => Compiler a b -> a -> (b -> IO ()) -> IO ()
runCompiler f a k = do
  runE (f a)
    (putStrLn . ("Error\n" ++) . indent 2)  -- failure
    k -- continuation

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines

