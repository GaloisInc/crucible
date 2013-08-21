{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
module SAWScript.Import
  ( loadWithPrelude
  , loadModule
  , findAndLoadModule
  , emptyLoadedModules
  , preludeLoadedModules
  , LoadedModules(..)
  ) where

import Control.Monad
import qualified Data.Map as Map
import Data.Maybe
import qualified Text.PrettyPrint.HughesPJ as PP

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.FileQuote (litFile)
import SAWScript.Lexer
import SAWScript.Options
import SAWScript.Parser

import System.Directory
import System.FilePath

preludePath :: FilePath
preludePath = "prelude/Prelude.saw"

preludeLoadedModules :: IO LoadedModules
preludeLoadedModules =
  runErr (formModule preludePath [litFile|prelude/Prelude.saw|]) error
         (\m -> return $ ms { modules = Map.insert mn m (modules ms) })
  where
    ms = emptyLoadedModules
    mn = moduleNameFromPath preludePath

loadWithPrelude :: Options -> FilePath -> (LoadedModules -> IO ()) -> IO ()
loadWithPrelude opts fname k = do
  loaded <- preludeLoadedModules
  loadModule opts fname loaded k

loadModule :: Options -> FilePath -> LoadedModules
  -> (LoadedModules -> IO ()) -> IO ()
loadModule opts fname ms k = do
  let mn = moduleNameFromPath $ dropExtension (takeFileName fname)
  when (verbLevel opts > 0) $ putStrLn $ "Loading Module " ++ show (renderModuleName mn)
  ftext <- readFile fname
  runCompiler (formModule fname) ftext $ \m -> do
    loadRest mn (mapMaybe getImport m)
             (ms { modules = Map.insert mn m (modules ms) })
  where loadRest mn [] ms' = do
          k ms' 
        loadRest mn (imp:imps) ms' = do
          findAndLoadModule opts imp ms' (loadRest mn imps)



data LoadedModules = LoadedModules
  { modules    :: ModuleEnv [TopStmtSimple RawT]
  } deriving (Show)

instance PrettyPrint LoadedModules where
  pretty _ lm =
    PP.brackets $ commaSepAll $ fmap (pretty False) $ Map.keys $ modules lm

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

