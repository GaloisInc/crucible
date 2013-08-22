{-# LANGUAGE ScopedTypeVariables #-}
module SAWScript.REPL where

import Control.Monad.IO.Class (liftIO)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (foldrM)
import System.Console.Haskeline (InputT, runInputT)
import qualified System.Console.Haskeline as Haskeline

import SAWScript.AST (ModuleName,
                      Module(moduleTypeEnv), ValidModule,
                      BlockStmt,
                      UnresolvedName, ResolvedName,
                      RawT, ResolvedT)
import SAWScript.BuildModules (buildModules, preludeName)
import SAWScript.Compiler (runCompiler, ErrT, mapErrT)
import SAWScript.Import (preludeLoadedModules)
import SAWScript.Lexer (scan)
import SAWScript.Parser (parseBlockStmt)
import SAWScript.ProcessFile (checkModuleWithDeps)
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

evaluate :: String -> ErrT (InputT IO) (BlockStmt UnresolvedName ResolvedT)
evaluate line = do
  -- Load all the modules that should be in scope when evaluating this line.
  modsInScope :: Map ModuleName ValidModule
              <-
    liftIO preludeLoadedModules >>=
    mapErrT liftIO . buildModules >>=
    mapErrT liftIO . foldrM checkModuleWithDeps Map.empty
  -- Lex and parse.
  tokens <- mapErrT liftIO $ scan "<stdin>" line
  ast :: BlockStmt UnresolvedName RawT
      <- mapErrT liftIO $ parseBlockStmt tokens
  {- Resolve type synonyms, abstract types, etc.  They're not supported by the
  REPL, so there never are any. -}
  synsResolved :: BlockStmt UnresolvedName ResolvedT
               <- mapErrT liftIO $ resolveBlockStmtSyns Map.empty ast
  -- All done.
  return synsResolved

showResult :: Show a => a -> String
showResult = show
