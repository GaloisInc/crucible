{-# LANGUAGE CPP #-}
module SAWScript.Import
  ( loadAll
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

data LoadedModules =
  LoadedModules {
    modules :: Map Name [TopStmtSimple RawT]
  }

emptyLoadedModules :: LoadedModules
emptyLoadedModules = LoadedModules { modules = Map.empty }

formModule :: FilePath -> Compiler String [TopStmtSimple RawT]
formModule f = scan f >=> parseModule

findAndLoadModule :: Options -> LoadedModules -> Name -> (LoadedModules -> IO ())
                  -> IO ()
findAndLoadModule opts ms name k = do
  mfname <- findModule (importPath opts) name
  case mfname of
    Nothing -> putStrLn $ "Can't find module " ++ name
    Just fname -> loadModule opts ms fname k

loadAll :: Options -> FilePath -> (LoadedModules -> IO ())
loadAll opts = loadModule opts emptyLoadedModules

loadModule :: Options -> LoadedModules -> FilePath -> (LoadedModules -> IO ())
           -> IO ()
loadModule opts ms fname k = do
  ftext <- readFile fname
  let name = dropExtension (takeFileName fname)
  runE (formModule fname ftext)
       (putStrLn . ("Error\n" ++) . indent 2)
       (\m -> loadRest
              (mapMaybe getImport m)
              (ms { modules = Map.insert name m (modules ms) }))
    where loadRest [] ms' = k ms' 
          loadRest (imp:imps) ms' =
            findAndLoadModule opts ms' imp (loadRest imps)

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
  
getImport :: TopStmtSimple a -> Maybe Name
getImport (Import mn _ _) = Just $ moduleNameFilePath mn
getImport _ = Nothing

indent :: Int -> String -> String
indent n = unlines . map (replicate n ' ' ++) . lines
