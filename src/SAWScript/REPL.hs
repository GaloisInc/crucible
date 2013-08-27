{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL where

import Control.Monad.IO.Class (MonadIO, liftIO)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldrM)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline
import System.Directory (createDirectoryIfMissing)
import qualified System.Environment.XDG.BaseDir as XDG
import System.FilePath ((</>))

import SAWScript.AST (ModuleName(ModuleName),
                      Module(..), ValidModule,
                      Expr(Block),
                      BlockStmt,
                      UnresolvedName, ResolvedName,
                      RawT, ResolvedT, Schema,
                      Name)
import SAWScript.BuildModules (buildModules)
import SAWScript.Compiler (runCompiler,
                           ErrT, mapErrT)
import SAWScript.Import (preludeLoadedModules)
import SAWScript.Interpreter (Value, interpretEntry)
import SAWScript.Lexer (scan)
import SAWScript.MGU (checkModule)
import SAWScript.Options (Options)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.ProcessFile (checkModuleWithDeps)
import SAWScript.RenameRefs (renameRefs)
import SAWScript.ResolveSyns (resolveBlockStmtSyns)

run :: Options -> IO ()
run opts = do
  settings <- replSettings
  runInputT settings loop
  where loop :: InputT IO ()
        loop = do
          line <- Haskeline.getInputLine "Prelude> "
          case line of
            Nothing -> return ()
            Just instruction -> do
              runCompiler (evaluate opts) instruction $ \r -> do
                Haskeline.outputStrLn $ showResult r
              loop

replSettings :: MonadIO m => IO (Haskeline.Settings m)
replSettings = do
  dataHome <- XDG.getUserDataDir "sawscript"
  createDirectoryIfMissing True dataHome
  return $ Haskeline.setComplete Haskeline.noCompletion $
             Haskeline.defaultSettings
               { Haskeline.historyFile = Just (dataHome </> "repl_history") }

evaluate :: Options -> String -> ErrT (InputT IO) (Value s)
evaluate opts line = do
  -- Lex and parse.
  tokens <- mapErrT liftIO $ scan replFileName line
  ast :: BlockStmt UnresolvedName RawT
      <- mapErrT liftIO $ parseBlockStmt tokens
  {- Resolve type synonyms, abstract types, etc.  They're not supported by the
  REPL, so there never are any. -}
  synsResolved :: BlockStmt UnresolvedName ResolvedT
               <- mapErrT liftIO $ resolveBlockStmtSyns Map.empty ast
  {- From here on, the compiler pipeline needs to carry around a lot of
  metadata about the code it's compiling.  The metadata is related to the
  module system, so instead of creating some extra data structure to hold the
  metadata, the compiler pipeline simply zooms out and starts working at the
  module granularity. -}
  modsInScope :: Map ModuleName ValidModule
              <- liftIO preludeLoadedModules >>=
                 mapErrT liftIO . buildModules >>=
                 mapErrT liftIO . foldrM checkModuleWithDeps Map.empty
  let synsResolved' :: Module UnresolvedName ResolvedT ResolvedT
      synsResolved' = wrapBStmt modsInScope "it" synsResolved
  -- Rename references.
  renamed :: Module ResolvedName ResolvedT ResolvedT
          <- mapErrT liftIO $ renameRefs synsResolved'
  -- Infer and check types.
  typechecked :: Module ResolvedName Schema ResolvedT
              <- mapErrT liftIO $ checkModule renamed
  -- Interpret the statement.
  liftIO $ interpretEntry "it" opts typechecked

wrapBStmt :: Map ModuleName ValidModule
             -> Name
             -> BlockStmt refT ResolvedT
             -> Module refT ResolvedT ResolvedT
wrapBStmt modsInScope stmtName stmt =
  Module { moduleName = replModuleName
           {- The expression environment simply maps @it@ to the statement.
           Statements aren't expressions, so I wrap it up in a block (with an
           unspecified return type). -}
         , moduleExprEnv = Map.singleton stmtName (Block [stmt] Nothing)
         , modulePrimEnv = Map.empty -- no 'Prim's in the REPL
         , moduleTypeEnv = Map.empty -- no type synonyms in the REPL
         , moduleDependencies = modsInScope }

showResult :: Show a => a -> String
showResult = show


---------------------------------- Metadata -----------------------------------

-- The name of the REPL, as it should be reported in error messages
replFileName :: String
replFileName = "<stdin>"

-- The name of the REPL as a 'ModuleName'
replModuleName :: ModuleName
replModuleName = ModuleName [] replFileName
