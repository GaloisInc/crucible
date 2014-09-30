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
import qualified Text.PrettyPrint.Leijen as PP

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
preludeLoadedModules = do
  result <- runErr (formModule preludePath [litFile|prelude/Prelude.saw|])
  case result of
    Left msg -> fail msg
    Right m  -> return $ ms { modules = Map.insert mn m (modules ms) }
  where
    ms = emptyLoadedModules
    mn = "Prelude"

loadWithPrelude :: Options -> FilePath -> IO LoadedModules
loadWithPrelude opts fname = do
  loaded <- preludeLoadedModules
  loadModule opts fname loaded

loadModule :: Options -> FilePath -> LoadedModules -> IO LoadedModules
loadModule opts fname ms = do
  let mn = moduleNameFromPath $ dropExtension (takeFileName fname)
  when (verbLevel opts > 0) $ putStrLn $ "Loading Module " ++ show mn
  ftext <- readFile fname
  m <- reportErrT (formModule fname ftext)
  loadRest mn (mapMaybe getImport m) (ms { modules = Map.insert mn m (modules ms) })
  where loadRest _mn [] ms' = return ms'
        loadRest mn (imp:imps) ms' =
          findAndLoadModule opts imp ms' >>= loadRest mn imps



data LoadedModules = LoadedModules
  { modules    :: ModuleEnv [TopStmt]
  } deriving (Show)

instance PrettyPrint LoadedModules where
  pretty _ lm =
    PP.brackets $ commaSepAll $ fmap prettyModuleName $ Map.keys $ modules lm

emptyLoadedModules :: LoadedModules
emptyLoadedModules = LoadedModules Map.empty

formModule :: FilePath -> Compiler String [TopStmt]
formModule f = scan f >=> liftParser parseModule

findAndLoadModule :: Options -> ModuleName -> LoadedModules -> IO LoadedModules
findAndLoadModule opts name ms = do
  let mn    = name
  let fp    = name <.> "saw"
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find module " ++ show mn
        , "  Searched for file: " ++ show fp
        , "  In directories:"
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
  
getImport :: TopStmt -> Maybe ModuleName
getImport (Import mn _ _) = Just mn
getImport _ = Nothing

