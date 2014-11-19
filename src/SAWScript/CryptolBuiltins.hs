module SAWScript.CryptolBuiltins where

import qualified Verifier.SAW.Cryptol as C
import Verifier.SAW

import qualified Cryptol.ModuleSystem as M
import qualified Cryptol.ModuleSystem.Env as M
import qualified Cryptol.Parser as P
import qualified Cryptol.TypeCheck.AST as T
import Cryptol.Utils.PP

import SAWScript.TypedTerm

typeNoUser :: T.Type -> T.Type
typeNoUser t =
  case t of
    T.TCon tc ts   -> T.TCon tc (map typeNoUser ts)
    T.TVar {}      -> t
    T.TUser _ _ ty -> typeNoUser ty
    T.TRec fields  -> T.TRec [ (n, typeNoUser ty) | (n, ty) <- fields ]

schemaNoUser :: T.Schema -> T.Schema
schemaNoUser (T.Forall params props ty) = T.Forall params props (typeNoUser ty)

loadCryptol :: FilePath -> IO M.ModuleEnv
loadCryptol filepath = do
  (result, warnings) <- M.loadModuleByPath filepath
  mapM_ (print . pp) warnings
  (_m, modEnv) <-
    case result of
      Left err -> fail (show (pp err))
      Right x -> return x
  return modEnv

extractCryptol :: SharedContext s -> M.ModuleEnv -> String -> IO (TypedTerm s)
extractCryptol sc modEnv input = do
  let declGroups = concatMap T.mDecls (M.loadedModules modEnv)
  env <- C.importDeclGroups sc C.emptyEnv declGroups
  pexpr <-
    case P.parseExpr input of
      Left err -> fail (show (pp err))
      Right x -> return x
  (exprResult, exprWarnings) <- M.checkExpr pexpr modEnv
  mapM_ (print . pp) exprWarnings
  ((expr, schema), _modEnv') <-
    case exprResult of
      Left err -> fail (show (pp err))
      Right x -> return x
  t <- C.importExpr sc env expr
  return $ TypedTerm (schemaNoUser schema) t
