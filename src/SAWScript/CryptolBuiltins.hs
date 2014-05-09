module SAWScript.CryptolBuiltins where

import qualified Verifier.SAW.Cryptol as C
import Verifier.SAW

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import Cryptol.TypeCheck.AST

import qualified Data.Map as Map

extractCryptol :: SharedContext s -> FilePath -> String -> IO (SharedTerm s)
extractCryptol sc filepath name = do
  (result, warnings) <- M.loadModuleByPath filepath
  mapM_ print warnings
  (m, modEnv) <-
    case result of
      Left err -> fail (show err)
      Right x -> return x
  let declGroups = concatMap mDecls (M.loadedModules modEnv)
  env <- C.importDeclGroups sc C.emptyEnv declGroups
  let env' = C.envE env
  let qname = QName (Just (mName m)) (Name name)
  case Map.lookup qname env' of
    Nothing -> fail "Name not found in this module"
    Just t -> return t
