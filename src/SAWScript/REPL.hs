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
                      RawT, ResolvedT, Schema)
import SAWScript.BuildModules (buildModules)
import SAWScript.Compiler (Compiler, runCompiler, compiler,
                           ErrT, mapErrT)
import SAWScript.Import (preludeLoadedModules)
import SAWScript.Lexer (scan)
import SAWScript.MGU (checkModule)
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

evaluate :: String -> ErrT (InputT IO) (BlockStmt ResolvedName Schema)
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
          <- mapErrT liftIO $ moduleOp modsInScope renameRefs synsResolved
  -- Infer and check types.
  checked :: BlockStmt ResolvedName Schema
          <- mapErrT liftIO $ moduleOp modsInScope checkModule renamed
  -- All done.
  return checked

-- "Lowers" a module-level operation to work on single 'BlockStmt's.
moduleOp :: Monad m
            => Map ModuleName ValidModule -- ^ modules in scope
            -> (Module refT ResolvedT ResolvedT
                -> m (Module refT' exprT' typeT'))
            -> (BlockStmt refT ResolvedT
                -> m (BlockStmt refT' exprT'))
moduleOp modsInScope f = \stmt -> do
  resultMod <-
    f $ Module { moduleName = replModuleName
                 {- The expression environment simply maps @it@ to the
                 statement.  Statements aren't expressions, so I wrap it up in
                 a block (with an unspecified return type). -}
               , moduleExprEnv = Map.singleton "it"
                                               (Block [stmt] Nothing)
               , modulePrimEnv = Map.empty -- no 'Prim's in the REPL
               , moduleTypeEnv = Map.empty -- no type synonyms in the REPL
               , moduleDependencies = modsInScope }
  case Map.lookup "it" $ moduleExprEnv resultMod of
    Just (Block [renamedStmt] _) -> return renamedStmt
    _ -> fail "Unable to lower module operation to block level"

showResult :: Show a => a -> String
showResult = show


---------------------------------- Metadata -----------------------------------

-- The name of the REPL, as it should be reported in error messages
replFileName :: String
replFileName = "<stdin>"

-- The name of the REPL as a 'ModuleName'
replModuleName :: ModuleName
replModuleName = ModuleName [] replFileName
