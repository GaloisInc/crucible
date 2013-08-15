module Main where

import Control.Applicative
import Control.Monad
import qualified Data.Map      as M
import qualified Data.Foldable as F
import qualified Data.Set      as S
import Data.List

import System.IO
import System.Console.GetOpt
import System.Environment
import System.FilePath

import SAWScript.AST
import SAWScript.BuildModules as BM
import SAWScript.Compiler
import SAWScript.Import
import SAWScript.Interpreter
import SAWScript.MGU (checkModule)
import SAWScript.Options
import SAWScript.RenameRefs as RR
import SAWScript.ResolveSyns

main :: IO ()
main = do
  argv <- getArgs
  case getOpt Permute options argv of
    (_, [], [])       -> putStrLn (usageInfo header options)
    (opts, file:_, []) -> do
      let opts' = foldl' (flip id) defaultOptions opts
      opts'' <- processEnv opts'
      processFile opts'' file
    (_, _, errs)      ->
      hPutStrLn stderr (concat errs ++ usageInfo header options)
  where header = "Usage: saw [OPTION...] files..."



processFile :: Options -> FilePath -> IO ()

processFile opts file | takeExtensions file == ".saw" = do
  when (verbLevel opts > 0) $ putStrLn $ "Processing SAWScript file " ++ file
  {-
  loadPrelude opts $ \lms -> do
    processModule opts lms (ModuleName [] "Prelude")
  -}
  loadWithPrelude opts file $ \loadedModules -> do
    let modName = moduleNameFromPath file
    processModule opts loadedModules modName

processFile _ file = putStrLn $ "Don't know how to handle file " ++ file



processModule :: Options -> LoadedModules -> ModuleName -> IO ()
processModule opts lms modName =
  -- TODO: merge the two representations of the prelude into one
  --  that both the renamer and the type checker can understand.
  runCompiler comp lms (interpretMain opts)
  where
  comp =     buildModules
         >=> F.foldrM checkModuleWithDeps M.empty
         >=> (\cms -> case M.lookup modName cms of
               Just cm -> return cm
               Nothing -> fail $ "Module " ++ show modName ++
                                 " not found in environment of checkedModules:" ++
                                 show (M.keys cms))


checkModuleWithDeps :: BM.ModuleParts (ExprSimple RawT)
  -> M.Map ModuleName ValidModule
  -> Err (M.Map ModuleName ValidModule)
checkModuleWithDeps (BM.ModuleParts mn ee pe te ds) cms =
  mod >>=
  resolveSyns >>=
  renameRefs  >>=
  checkModule >>= \cm -> return $ M.insert mn cm cms
  where
  deps :: Err (M.Map ModuleName ValidModule)
  deps = fmap M.fromList $ forM (S.toList ds) $ \n ->
           case M.lookup n cms of
             Nothing -> fail $ "Tried to compile module " ++ show mn ++
                               " before compiling its dependency, " ++ show n
             Just m  -> return (n,m)
  mod  = Module mn ee pe te <$> deps

