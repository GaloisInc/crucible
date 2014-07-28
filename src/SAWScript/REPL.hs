{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.REPL (run) where

import Prelude hiding (print, read)

import Control.Applicative ((<$>))
import Control.Monad.Trans (MonadIO)
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified System.Console.Haskeline as Haskeline
import System.Directory (createDirectoryIfMissing)
import qualified System.Environment.XDG.BaseDir as XDG
import System.FilePath ((</>))

import SAWScript.AST (ModuleName, renderModuleName,
                      Module(..), ValidModule,
                      BlockStmt(Bind),
                      Name, LName, Located(..), UnresolvedName,
                      ResolvedName(..),
                      RawT, ResolvedT, Schema, rewindSchema,
                      topLevelContext)
import qualified SAWScript.AST as AST
import SAWScript.Interpreter (Value, isVUnit,
                              interpretModuleAtEntry,
                              interpretEnvValues, interpretEnvTypes)
import SAWScript.Lexer (scan)
import SAWScript.MGU (checkModule)
import SAWScript.Options (Options)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.RenameRefs (renameRefs)
import SAWScript.REPL.Logo (displayLogo)
import SAWScript.REPL.GenerateModule (replFileName, replModuleName, wrapBStmt)
import SAWScript.REPL.Haskeline (repl)
import SAWScript.REPL.Monad (REPLState, withInitialState,
                             REPL,
{-
                             REP, runREP,
                             REPResult(..),
-}
                             getModulesInScope, getNamesInScope,
                               getSharedContext, getEnvironment,
                             putEnvironment,
                             modifyNamesInScope, modifyEnvironment)
import qualified SAWScript.REPL.Monad as REP
import SAWScript.ResolveSyns (resolveSyns)
import SAWScript.Utils (SAWCtx, Pos(..))

-- | Main function
run :: Options -> IO ()
run opts = do
  -- settings <- replSettings
  displayLogo True
  withInitialState opts $ \initialState -> do
    repl Nothing opts (return ())
{-
  withInitialState opts $ loop settings
  where loop :: Haskeline.Settings IO -> REPLState -> IO ()
        loop settings state = do
          result <- runREP settings state (read >>= evaluate >>= print)
          case result of
            Success state' -> loop settings state'
            SuccessExit -> return ()
            Failure -> loop settings state
-}

replSettings :: MonadIO m => IO (Haskeline.Settings m)
replSettings = do
  dataHome <- XDG.getUserDataDir "sawscript"
  createDirectoryIfMissing True dataHome
  return $ Haskeline.setComplete Haskeline.noCompletion $
             Haskeline.defaultSettings
               { Haskeline.historyFile = Just (dataHome </> "repl_history") }


------------------------------------ Read -------------------------------------

{-
read :: REP (BlockStmt UnresolvedName RawT)
read = do
  promptString <- buildPromptString
  line <- REP.haskeline $ Haskeline.getInputLine promptString
  case line of
    Nothing -> REP.successExit
    Just sawScriptStr -> do
      -- Lex and parse.
      tokens <- REP.err $ scan replFileName sawScriptStr
      REP.err $ parseBlockStmt tokens

buildPromptString :: REP String
buildPromptString = do
  modsInScope <- getModulesInScope
  let moduleNames = map renderModuleName $ Map.keys modsInScope
  return $ intercalate " " moduleNames ++ "> "
-}


---------------------------------- Evaluate -----------------------------------

