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
import Cryptol.Utils.Ident (unpackIdent)
import qualified Cryptol.TypeCheck.AST as AST
import Cryptol.Utils.PP

-- | Parse a Cryptol module into a list of declarations
--   Yields an Interaction so that we can talk to the user about what went wrong
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

-- All this is just sifting through the Cryptol typechecker's AST to get the information we want:

-- Things will break if Cryptol's internals shift the way they desugar tuple bindings in declarations:
-- Currently, a declaration like @foo (a,b,c) = ...@ turns into something
-- like @foo = \x -> ... where a = x.0.; b = x.1; c = x.2@
-- We rely on this behavior to parse out the information we need.

-- | We don't care about recursive bindings, so we flatten them out
flattenDeclGroup :: AST.DeclGroup -> [AST.Decl]
flattenDeclGroup (AST.Recursive decls)   = decls
flattenDeclGroup (AST.NonRecursive decl) = [decl]

-- | If the expression is a tuple projection, get the name of the tuple and the index projected
tupleSelInfo :: AST.Expr -> Maybe (AST.Name, Int)
tupleSelInfo (AST.ESel (AST.EVar name) (AST.TupleSel i _)) = return (name, i)
tupleSelInfo _                                             = Nothing

-- | If an expression is a where binding, get all its local declarations
whereBindings :: AST.Expr -> Maybe [AST.Decl]
whereBindings (AST.EWhere _ bindings) = return $ concatMap flattenDeclGroup bindings
whereBindings _                       = Nothing

-- | Find the expression inside a definition
--   We can't handle primitives currently
declDefExpr :: AST.DeclDef -> Maybe AST.Expr
declDefExpr = \case
   AST.DPrim      -> Nothing
   AST.DExpr expr -> Just expr

-- | If a lambda is of the form @\(a,b,...,z) -> ...)@ then give the list of names bound in the tuple
tupleLambdaBindings :: AST.Expr -> Maybe [AST.Name]
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

-- | If the type given is of the form @(a,b,...,y) -> z@ then give the pair of arguments and result
tupleFunctionType :: AST.Type -> Maybe ([AST.Type], AST.Type)
tupleFunctionType (AST.TCon (AST.TC AST.TCFun) [AST.TCon (AST.TC (AST.TCTuple _)) inputs, output]) = return (inputs, output)
tupleFunctionType _                                                                                = Nothing

-- | Find the name from the source if one exists
sourceName :: Name -> Maybe String
sourceName nm = Just (unpackIdent (nameIdent nm))
