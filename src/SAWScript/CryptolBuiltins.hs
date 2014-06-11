module SAWScript.CryptolBuiltins where

import Control.Applicative
import Control.Monad.State

import qualified Verifier.SAW.Cryptol as C
import Verifier.SAW
import Verifier.SAW.Prelude

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.Parser as P
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP

loadCryptol :: FilePath -> IO M.ModuleEnv
loadCryptol filepath = do
  (result, warnings) <- M.loadModuleByPath filepath
  mapM_ (print . pp) warnings
  (_m, modEnv) <-
    case result of
      Left err -> fail (show (pp err))
      Right x -> return x
  return modEnv

extractCryptol :: SharedContext s -> M.ModuleEnv -> String -> IO (SharedTerm s)
extractCryptol sc modEnv input = do
  let declGroups = concatMap T.mDecls (M.loadedModules modEnv)
  env <- C.importDeclGroups sc C.emptyEnv declGroups
  pexpr <-
    case P.parseExpr input of
      Left err -> fail (show (pp err))
      Right x -> return x
  (exprResult, exprWarnings) <- M.checkExpr pexpr modEnv
  mapM_ (print . pp) exprWarnings
  ((expr, _schema), _modEnv') <-
    case exprResult of
      Left err -> fail (show (pp err))
      Right x -> return x
  C.importExpr sc env expr
