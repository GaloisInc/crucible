{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.Import
  ( loadWithPrelude
  , loadModuleFromFile
  , loadModuleFromString
  , findAndLoadModule
  , emptyLoadedModules
  , preludeLoadedModules
  , LoadedModules(..)
  ) where

import Control.Monad
import Control.Monad.IO.Class (MonadIO(liftIO))
import qualified Data.Map as Map
import Data.Maybe

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
  loadModuleFromFile opts fname loaded k

loadModuleFromFile :: (MonadIO io)
                      => Options -> FilePath -> LoadedModules
                      -> (LoadedModules -> io ()) -> io ()
loadModuleFromFile opts fname ms k = do
  let mn = moduleNameFromPath $ dropExtension (takeFileName fname)
  when (verbLevel opts > 0) $ liftIO $ putStrLn $ "Loading Module " ++ show (renderModuleName mn)
  ftext <- liftIO $ readFile fname
  loadModuleFromString opts fname ftext ms k

loadModuleFromString :: forall io. (MonadIO io)
                        => Options
                        -> String -- file name (used in, e.g., error messages)
                        -> String -- file contents
                        -> LoadedModules
                        -> (LoadedModules -> io ())
                        -> io ()
loadModuleFromString opts fname ftext ms k = do
  let mn = moduleNameFromPath $ dropExtension (takeFileName fname)
  runCompiler (mapErrT liftIO . formModule fname) ftext $ \m -> do
    loadRest (mapMaybe getImport m)
             (ms { modules = Map.insert mn m (modules ms) })
  where loadRest :: [ModuleName] -> LoadedModules -> io ()
        loadRest [] ms' = k ms' 
        loadRest (imp:imps) ms' =
          findAndLoadModule opts imp ms' (loadRest imps)



data LoadedModules = LoadedModules
  { modules    :: ModuleEnv [TopStmtSimple RawT]
  } deriving (Show)

emptyLoadedModules :: LoadedModules
emptyLoadedModules = LoadedModules Map.empty



formModule :: FilePath -> Compiler String [TopStmtSimple RawT]
formModule f = scan f >=> parseModule

findAndLoadModule :: (MonadIO io)
                     => Options -> ModuleName -> LoadedModules
                     -> (LoadedModules -> io ()) -> io ()
findAndLoadModule opts name ms k = do
  let mn    = renderModuleName name
  let fp    = moduleNameFilePath name <.> "saw"
  let paths = importPath opts
  mfname <- liftIO $ findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find module " ++ show mn
        , "  Searched for file: " ++ show fp
        , "  In directories:"
        ] ++ map ("    " ++) paths
    Just fname -> loadModuleFromFile opts fname ms k

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

