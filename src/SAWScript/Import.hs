{-# LANGUAGE CPP #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.Import
  ( loadFile
  , findAndLoadFile
  ) where

import Control.Monad ((>=>), when)

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Lexer
import SAWScript.Options
import SAWScript.Parser

import System.Directory

loadFile :: Options -> FilePath -> IO [Stmt]
loadFile opts fname = do
  when (verbLevel opts > 0) $ putStrLn $ "Loading file " ++ show fname
  ftext <- readFile fname
  reportErrT (parseFile fname ftext)

parseFile :: FilePath -> Compiler String [Stmt]
parseFile fname = scan fname >=> liftParser parseModule

findAndLoadFile :: Options -> FilePath -> IO [Stmt]
findAndLoadFile opts fp = do
  let paths = importPath opts
  mfname <- findFile paths fp
  case mfname of
    Nothing -> fail $ unlines $
        [ "Couldn't find file: " ++ show fp
        , "  Searched in directories:"
        ] ++ map ("    " ++) paths
    Just fname -> loadFile opts fname

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
