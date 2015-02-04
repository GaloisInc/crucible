{-# LANGUAGE CPP #-}
module SAWScript.Import
  ( loadFile
  , findAndLoadFile
  ) where

import Control.Monad ((>=>), when)
import Control.Applicative ((<$>))

import SAWScript.AST
import SAWScript.Compiler
import SAWScript.Lexer
import SAWScript.Options
import SAWScript.Parser

import System.Directory

loadFile :: Options -> FilePath -> IO [TopStmt]
loadFile opts fname = do
  when (verbLevel opts > 0) $ putStrLn $ "Loading file " ++ show fname
  ftext <- readFile fname
  reportErrT (parseFile fname ftext)

parseFile :: FilePath -> Compiler String [TopStmt]
parseFile fname = scan fname >=> liftParser parseModule >=> combineTopTypeDecl

findAndLoadFile :: Options -> FilePath -> IO [TopStmt]
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

-- | Combine every top-level type signature with the immediately
-- following value binding. The final result contains no occurrences
-- of TopTypeDecl.
combineTopTypeDecl :: [TopStmt] -> Err [TopStmt]
combineTopTypeDecl [] = return []
combineTopTypeDecl (TopTypeDecl name ty : TopBind (Decl name' _ e) : stmts)
  | name == name' = (:) (TopBind (Decl name' (Just ty) e)) <$> combineTopTypeDecl stmts
combineTopTypeDecl (TopTypeDecl name _ : _) = noBindingErr name
combineTopTypeDecl (stmt : stmts) = (:) stmt <$> combineTopTypeDecl stmts

noBindingErr :: LName -> Err a
noBindingErr n = fail ("The type signature for '" ++ getVal n ++ "' lacks an accompanying binding at " ++ show (getPos n))
