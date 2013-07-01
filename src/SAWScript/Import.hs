{-# LANGUAGE CPP #-}
module SAWScript.Import
  ( loadWithPrelude
  , loadPrelude
  , loadModule
  , findAndLoadModule
  , emptyLoadedModules
  , LoadedModules(..)
  ) where

import Control.Monad
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Lexer
import SAWScript.Options
import SAWScript.Parser

import System.Directory
import System.FilePath

import Debug.Trace

loadPrelude :: Options -> (LoadedModules -> IO ()) -> IO ()
loadPrelude opts k = do
  let preludePath = "/home/kcarter/work/Verifier/SAWScript/src/SAWScript/Prelude.saw"
  loadModule opts preludePath emptyLoadedModules k

loadWithPrelude :: Options -> FilePath -> (LoadedModules -> IO ()) -> IO ()
loadWithPrelude opts fname k = do
  let preludePath = "/home/kcarter/work/Verifier/SAWScript/src/SAWScript/Prelude.saw"
  loadModule opts preludePath emptyLoadedModules $ \lms ->
    loadModule opts fname lms k

loadModule :: Options -> FilePath -> LoadedModules
  -> (LoadedModules -> IO ()) -> IO ()
loadModule opts fname ms k = do
  let mn = moduleNameFromPath $ dropExtension (takeFileName fname)
  when (verbLevel opts > 0) $ putStrLn $ "Loading Module " ++ show (renderModuleName mn)
  ftext <- readFile fname
  runCompiler (formModule fname) ftext $ \m -> do
    loadRest (mapMaybe getImport m)
             (ms { modules = Map.insert mn m (modules ms) })
  where loadRest [] ms' = k ms' 
        loadRest (imp:imps) ms' =
          findAndLoadModule opts imp ms' (loadRest imps)



data LoadedModules = LoadedModules
  { modules    :: ModuleEnv [TopStmtSimple RawT]
  } deriving (Show)

emptyLoadedModules :: LoadedModules
emptyLoadedModules = LoadedModules Map.empty



formModule :: FilePath -> Compiler String [TopStmtSimple RawT]
formModule f = scan f >=> parseModule

findAndLoadModule :: Options -> ModuleName -> LoadedModules
  -> (LoadedModules -> IO ()) -> IO ()
findAndLoadModule opts name ms k = do
  let mn    = renderModuleName name
  let fp    = moduleNameFilePath name <.> "saw"
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find module " ++ show mn
        , "  Searched for file: " ++ show fp
        , "  In directories:"
        ] ++ map ("    " ++) paths
    Just fname -> loadModule opts fname ms k

findModule :: [FilePath] -> Name -> IO (Maybe FilePath)
findModule ps name = findFile ps (name <.> "saw")

#if __GLASGOW_HASKELL__ < 706
findFile :: [FilePath] -> String -> IO (Maybe FilePath)
findFile paths fileName = search paths
  where
    search :: [FilePath] -> IO (Maybe FilePath)
    search [] = return Nothing
    search (d:ds) = do
        let path = d </> fileName
        b <- doesFileExist path
        if b then return (Just path)
             else search ds
#endif
  
getImport :: TopStmtSimple a -> Maybe ModuleName
getImport (Import mn _ _) = Just mn
getImport _ = Nothing

