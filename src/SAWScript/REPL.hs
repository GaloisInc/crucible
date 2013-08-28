{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL where

import Prelude hiding (print, read)

import Control.Monad.Trans (MonadIO)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldrM)
import qualified System.Console.Haskeline as Haskeline
import System.Directory (createDirectoryIfMissing)
import qualified System.Environment.XDG.BaseDir as XDG
import System.FilePath ((</>))

import SAWScript.AST (ModuleName(ModuleName),
                      Module(..), ValidModule,
                      Expr(Block),
                      BlockStmt(Bind),
                      UnresolvedName, ResolvedName,
                      RawT, ResolvedT, Schema,
                      Name,
                      topLevelContext)
import SAWScript.BuildModules (buildModules)
import SAWScript.Import (preludeLoadedModules)
import SAWScript.Interpreter (Value, interpretEntry)
import SAWScript.Lexer (scan)
import SAWScript.MGU (checkModule)
import SAWScript.Options (Options)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.ProcessFile (checkModuleWithDeps)
import SAWScript.RenameRefs (renameRefs)
import SAWScript.REPL.Monad (REPLState, emptyState,
                             REP, runREP,
                             REPResult(..))
import qualified SAWScript.REPL.Monad as REP
import SAWScript.ResolveSyns (resolveBlockStmtSyns)

run :: Options -> IO ()
run opts = do
  settings <- replSettings
  loop settings emptyState
  where loop :: Haskeline.Settings IO -> REPLState -> IO ()
        loop settings state = do
          result <- runREP settings state (read >>= evaluate opts >>= print)
          case result of
            Success state' -> loop settings state'
            SuccessExit -> return ()
            Failure -> loop settings state

replSettings :: MonadIO m => IO (Haskeline.Settings m)
replSettings = do
  dataHome <- XDG.getUserDataDir "sawscript"
  createDirectoryIfMissing True dataHome
  return $ Haskeline.setComplete Haskeline.noCompletion $
             Haskeline.defaultSettings
               { Haskeline.historyFile = Just (dataHome </> "repl_history") }

-- The name of the REPL, as it should be reported in error messages
replFileName :: String
replFileName = "<stdin>"

-- The name of the REPL as a 'ModuleName'
replModuleName :: ModuleName
replModuleName = ModuleName [] replFileName


------------------------------------ Read -------------------------------------

read :: REP (BlockStmt UnresolvedName RawT)
read = do
  line <- REP.haskeline $ Haskeline.getInputLine "Prelude> "
  case line of
    Nothing -> REP.successExit
    Just sawScriptStr -> do
      -- Lex and parse.
      tokens <- REP.err $ scan replFileName sawScriptStr
      REP.err $ parseBlockStmt tokens


---------------------------------- Evaluate -----------------------------------

evaluate :: Options
            -> BlockStmt UnresolvedName RawT
            -> REP (Value s)
evaluate opts ast = do
  {- Set the context (i.e., the monad) for the statement.  For the REPL, this
  will always be 'TopLevelContext'. -}
  let ast' :: BlockStmt UnresolvedName RawT
      ast' = case ast of
        Bind maybeVar _ctx expr -> Bind maybeVar (Just topLevelContext) expr
        stmt -> stmt
  {- Resolve type synonyms, abstract types, etc.  They're not supported by the
  REPL, so there never are any. -}
  synsResolved :: BlockStmt UnresolvedName ResolvedT
               <- REP.err $ resolveBlockStmtSyns Map.empty ast'
  {- From here on, the compiler pipeline needs to carry around a lot of
  metadata about the code it's compiling.  The metadata is related to the
  module system, so instead of creating some extra data structure to hold the
  metadata, the compiler pipeline simply zooms out and starts working at the
  module granularity. -}
  modsInScope :: Map ModuleName ValidModule
              <- REP.io    preludeLoadedModules >>=
                 REP.err . buildModules >>=
                 REP.err . foldrM checkModuleWithDeps Map.empty
  let synsResolved' :: Module UnresolvedName ResolvedT ResolvedT
      synsResolved' = wrapBStmt modsInScope "it" synsResolved
  -- Rename references.
  renamed :: Module ResolvedName ResolvedT ResolvedT
          <- REP.err $ renameRefs synsResolved'
  -- Infer and check types.
  typechecked :: Module ResolvedName Schema ResolvedT
              <- REP.err $ checkModule renamed
  -- Interpret the statement.
  REP.io $ interpretEntry "it" opts typechecked

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


------------------------------------ Print ------------------------------------

print :: Show a => a -> REP ()
print = REP.haskeline . Haskeline.outputStrLn . show
