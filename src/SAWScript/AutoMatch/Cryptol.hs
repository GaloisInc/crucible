{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module SAWScript.AutoMatch.Cryptol where

import SAWScript.AutoMatch.Declaration hiding (Name)
import SAWScript.AutoMatch.Util
import SAWScript.AutoMatch.Interaction

import Control.Monad
import Control.Monad.Free
import Data.List hiding (sort)
import Data.Maybe
import Data.Ord

import qualified Cryptol.ModuleSystem as M
import Cryptol.ModuleSystem.Name
import qualified Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.PP

getDeclsCryptol :: FilePath -> IO (Interaction (Maybe [Decl]))
getDeclsCryptol path = do
   (result, warnings) <- M.loadModuleByPath path =<< M.initialModuleEnv
   return $ do
      forM_ warnings $ liftF . flip Warning () . pretty
      case result of
         Left err -> liftF $ Failure True (pretty err) Nothing
         Right (AST.Module{mDecls}, _) ->
            let stdDecls = catMaybes . for (concatMap flattenDeclGroup mDecls) $
                  \(AST.Decl{dName, dSignature, dDefinition}) -> do
                     funcName <- sourceName dName
                     argNames <- mapM sourceName =<< tupleLambdaBindings =<< declDefExpr dDefinition
                     (argTypes, retType) <- tupleFunctionType (AST.sType dSignature)
                     return $ Decl funcName retType (zipWith Arg argNames argTypes)
            in return $ Just (stdDecls :: [Decl])

flattenDeclGroup :: AST.DeclGroup -> [AST.Decl]
flattenDeclGroup (AST.Recursive decls)   = decls
flattenDeclGroup (AST.NonRecursive decl) = [decl]

tupleSelInfo :: AST.Expr -> Maybe (AST.QName, Int)
tupleSelInfo (AST.ESel (AST.EVar name) (AST.TupleSel i _)) = return (name, i)
tupleSelInfo _                                             = Nothing

whereBindings :: AST.Expr -> Maybe [AST.Decl]
whereBindings (AST.EWhere _ bindings) = return $ concatMap flattenDeclGroup bindings
whereBindings _                       = Nothing

declDefExpr :: AST.DeclDef -> Maybe AST.Expr
declDefExpr = \case
   AST.DPrim      -> Nothing
   AST.DExpr expr -> Just expr

tupleLambdaBindings :: AST.Expr -> Maybe [AST.QName]
tupleLambdaBindings (AST.EAbs tupleName _ whereClause) = do
   bindings <- whereBindings whereClause
   return . map snd . sortBy (comparing fst) . catMaybes . for bindings $
      \AST.Decl{dDefinition, dName} -> do
         (from, index) <- tupleSelInfo =<< declDefExpr dDefinition
         guard (from == tupleName)
         return (index, dName)
tupleLambdaBindings (AST.ETAbs _ expr)     = tupleLambdaBindings expr   --   \
tupleLambdaBindings (AST.EProofAbs _ expr) = tupleLambdaBindings expr   --    >- drill down past casts & type abstractions
tupleLambdaBindings (AST.ECast expr _)     = tupleLambdaBindings expr   --   /
tupleLambdaBindings _ = Nothing

tupleFunctionType :: AST.Type -> Maybe ([AST.Type], AST.Type)
tupleFunctionType (AST.TCon (AST.TC AST.TCFun) [AST.TCon (AST.TC (AST.TCTuple _)) inputs, output]) = return (inputs, output)
tupleFunctionType _                                                                                = Nothing

sourceName :: QName -> Maybe String
sourceName (unqual -> Name string) = Just string
sourceName _                       = Nothing
