{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL where

import Control.Monad.IO.Class (liftIO)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldrM)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (ModuleName(ModuleName),
                      Module(..), ValidModule,
                      Expr(Block),
                      BlockStmt,
                      UnresolvedName, ResolvedName,
                      RawT, ResolvedT)
import SAWScript.BuildModules (buildModules)
import SAWScript.Compiler (Compiler, runCompiler, compiler,
                           ErrT, mapErrT)
import SAWScript.Import (preludeLoadedModules)
import SAWScript.Lexer (scan)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.ProcessFile (checkModuleWithDeps)
import SAWScript.RenameRefs (renameRefs)
import SAWScript.ResolveSyns (resolveBlockStmtSyns)

run :: IO ()
run = runInputT Haskeline.defaultSettings loop
  where loop :: InputT IO ()
        loop = do
          line <- Haskeline.getInputLine "Prelude> "
          case line of
            Nothing -> return ()
            Just instruction -> do
              runCompiler evaluate instruction $ \r -> do
                Haskeline.outputStrLn $ showResult r
              loop

evaluate :: String -> ErrT (InputT IO) (BlockStmt ResolvedName ResolvedT)
evaluate line = do
  -- Lex and parse.
  tokens <- mapErrT liftIO $ scan replFileName line
  ast :: BlockStmt UnresolvedName RawT
      <- mapErrT liftIO $ parseBlockStmt tokens
  {- Resolve type synonyms, abstract types, etc.  They're not supported by the
  REPL, so there never are any. -}
  synsResolved :: BlockStmt UnresolvedName ResolvedT
               <- mapErrT liftIO $ resolveBlockStmtSyns Map.empty ast
  -- Rename references.
  modsInScope :: Map ModuleName ValidModule
              <-
    liftIO preludeLoadedModules >>=
    mapErrT liftIO . buildModules >>=
    mapErrT liftIO . foldrM checkModuleWithDeps Map.empty
  renamed :: BlockStmt ResolvedName ResolvedT
          <- mapErrT liftIO $ renameBStmtRefs modsInScope synsResolved
  -- All done.
  return renamed

-- Analogue of 'RenameRefs.renameRefs', but for a single 'BlockStmt'.
renameBStmtRefs :: Map ModuleName ValidModule -- ^ modules in scope
                   -> Compiler (BlockStmt UnresolvedName ResolvedT)
                               (BlockStmt ResolvedName ResolvedT)
renameBStmtRefs modsInScope = compiler "RenameBStmtRefs" $ \stmt -> do
  {- Given the amount of metadata needed to perform a proper renaming, it seems
  totally reasonable to couple the renamer with the SAWScript module system,
  and indeed, this is the approach 'RenameRefs' takes.  This function collects
  all the metadata about the single line we're trying to interpret and packages
  them into a fake module for 'RenameRefs' to work on.  While this may seem
  somewhat ugly, it's really not--even without the spurious module data
  structure, I'd still need to collect all the metadata and pipe it along to
  the renamer. -}
  renamed <- renameRefs $
             Module { moduleName = replModuleName
                      {- The expression environment simply maps @it@ to the
                      statement.  Statements aren't expressions, so I wrap it
                      up in a block (with an unspecified return type). -}
                    , moduleExprEnv = Map.singleton "it"
                                                    (Block [stmt] Nothing)
                    , modulePrimEnv = Map.empty -- no 'Prim's in the REPL
                    , moduleTypeEnv = Map.empty -- no type synonyms in the REPL
                    , moduleDependencies = modsInScope }
  case Map.lookup "it" $ moduleExprEnv renamed of
    Just (Block [renamedStmt] _) -> return renamedStmt
    _ -> fail "Unable to rename references"

showResult :: Show a => a -> String
showResult = show


---------------------------------- Metadata -----------------------------------

-- The name of the REPL, as it should be reported in error messages
replFileName :: String
replFileName = "<stdin>"

-- The name of the REPL as a 'ModuleName'
replModuleName :: ModuleName
replModuleName = ModuleName [] replFileName
