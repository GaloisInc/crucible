{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL where

import Prelude hiding (print, read)

import Control.Monad.Trans (MonadIO)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified System.Console.Haskeline as Haskeline
import System.Directory (createDirectoryIfMissing)
import qualified System.Environment.XDG.BaseDir as XDG
import System.FilePath ((</>))

import SAWScript.AST (ModuleName,
                      Module(..), ValidModule,
                      BlockStmt(Bind),
                      UnresolvedName, ResolvedName,
                      RawT, ResolvedT, Schema,
                      topLevelContext)
import SAWScript.Interpreter (Value, interpretModuleAtEntry)
import SAWScript.Lexer (scan)
import SAWScript.MGU (checkModule)
import SAWScript.Options (Options)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.RenameRefs (renameRefs)
import SAWScript.REPL.GenerateModule (replFileName, wrapBStmt)
import SAWScript.REPL.Monad (REPLState, withInitialState,
                             REP, runREP,
                             REPResult(..),
                             getModulesInScope, getSharedContext, getEnvironment,
                             putEnvironment)
import qualified SAWScript.REPL.Monad as REP
import SAWScript.ResolveSyns (resolveBlockStmtSyns)

run :: Options -> IO ()
run opts = do
  settings <- replSettings
  withInitialState opts $ loop settings
  where loop :: Haskeline.Settings IO -> REPLState s -> IO ()
        loop settings state = do
          result <- runREP settings state (read >>= evaluate >>= print)
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


------------------------------------ Read -------------------------------------

read :: REP s (BlockStmt UnresolvedName RawT)
read = do
  line <- REP.haskeline $ Haskeline.getInputLine "Prelude> "
  case line of
    Nothing -> REP.successExit
    Just sawScriptStr -> do
      -- Lex and parse.
      tokens <- REP.err $ scan replFileName sawScriptStr
      REP.err $ parseBlockStmt tokens


---------------------------------- Evaluate -----------------------------------

evaluate :: BlockStmt UnresolvedName RawT
            -> REP s (Value s)
evaluate ast = do
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
              <- getModulesInScope
  let synsResolved' :: Module UnresolvedName ResolvedT ResolvedT
      synsResolved' = wrapBStmt modsInScope "it" synsResolved
  -- Rename references.
  renamed :: Module ResolvedName ResolvedT ResolvedT
          <- REP.err $ renameRefs synsResolved'
  -- Infer and check types.
  typechecked :: Module ResolvedName Schema ResolvedT
              <- REP.err $ checkModule renamed
  -- Interpret the statement.
  ctx <- getSharedContext
  env <- getEnvironment
  (result, env') <- REP.io $ interpretModuleAtEntry "it" ctx env typechecked
  -- Update the environment and return the result.
  putEnvironment env'
  return result


------------------------------------ Print ------------------------------------

print :: Show a => a -> REP s ()
print = REP.haskeline . Haskeline.outputStrLn . show
