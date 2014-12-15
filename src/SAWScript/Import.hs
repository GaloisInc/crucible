{-# LANGUAGE CPP #-}
module SAWScript.Import
  ( loadModule
  , emptyLoadedModules
  , LoadedModules(..)
  ) where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import qualified Text.PrettyPrint.Leijen as PP

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Lexer
import SAWScript.Options
import SAWScript.Parser

import System.Directory

loadModule :: Options -> FilePath -> LoadedModules -> IO LoadedModules
loadModule opts fname ms = do
  when (verbLevel opts > 0) $ putStrLn $ "Loading file " ++ show fname
  ftext <- readFile fname
  m <- reportErrT (formModule fname ftext)
  loadRest (mapMaybe getImport m) (ms { modules = Map.insert fname m (modules ms) })
  where loadRest [] ms' = return ms'
        loadRest (imp:imps) ms' =
          findAndLoadFile opts imp ms' >>= loadRest imps



data LoadedModules = LoadedModules
  { modules :: Map.Map FilePath [TopStmt]
  } deriving (Show)

instance PrettyPrint LoadedModules where
  pretty _ lm =
    PP.brackets $ commaSepAll $ fmap PP.text $ Map.keys $ modules lm

emptyLoadedModules :: LoadedModules
emptyLoadedModules = LoadedModules Map.empty

formModule :: FilePath -> Compiler String [TopStmt]
formModule f = scan f >=> liftParser parseModule

findAndLoadFile :: Options -> FilePath -> LoadedModules -> IO LoadedModules
findAndLoadFile opts fp ms = do
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find file: " ++ show fp
        , "  Searched in directories:"
        ] ++ map ("    " ++) paths
    Just fname -> loadModule opts fname ms

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

getImport :: TopStmt -> Maybe FilePath
getImport (TopImport path) = Just path
getImport _ = Nothing
