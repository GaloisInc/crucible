{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAWScript.AutoMatch.Cryptol where

--import SAWScript.CryptolEnv
--import SAWScript.TypedTerm
--import Verifier.SAW.SharedTerm
--import Verifier.SAW.TypedAST

import SAWScript.AutoMatch.Declaration hiding (Name)
import SAWScript.AutoMatch.Util

--import qualified Data.Map as Map
--import           Data.Map   (Map)

--import System.FilePath

import Control.Monad
--import Control.Arrow
import Data.List hiding (sort)
import Data.Maybe
import Data.Ord

import qualified Cryptol.ModuleSystem as M
import Cryptol.ModuleSystem.Name
--import Cryptol.Parser.Position
import qualified Cryptol.TypeCheck.AST as AST

import Cryptol.Utils.PP
--import Text.Show.Pretty (ppShow)

getDeclsCryptol :: FilePath -> IO (String,[Decl])
getDeclsCryptol path = do
   (result, warnings) <- M.loadModuleByPath path =<< M.initialModuleEnv
   forM_ warnings $ print . pp
   (AST.Module{mName = ModName mName, mDecls}, _modEnv) <- either (fail . show . pp) return result
   let stdDecls = catMaybes . for (concatMap flattenDeclGroup mDecls) $
         \(AST.Decl{dName, dSignature, dDefinition}) -> do
            funcName <- sourceName dName
            argNames <- mapM sourceName =<< tupleLambdaBindings dDefinition
            (argTypes, retType) <- tupleFunctionType (AST.sType dSignature)
            return $ Decl funcName retType (zipWith Arg argNames argTypes)
   return (intercalate "." mName, stdDecls :: [Decl])

flattenDeclGroup :: AST.DeclGroup -> [AST.Decl]
flattenDeclGroup (AST.Recursive decls)   = decls
flattenDeclGroup (AST.NonRecursive decl) = [decl]

tupleSelInfo :: AST.Expr -> Maybe (AST.QName, Int)
tupleSelInfo (AST.ESel (AST.EVar name) (AST.TupleSel i _)) = return (name, i)
tupleSelInfo _                                             = Nothing

whereBindings :: AST.Expr -> Maybe [AST.Decl]
whereBindings (AST.EWhere _ bindings) = return $ concatMap flattenDeclGroup bindings
whereBindings _                       = Nothing

tupleLambdaBindings :: AST.Expr -> Maybe [AST.QName]
tupleLambdaBindings (AST.EAbs tupleName _ whereClause) = do
   bindings <- whereBindings whereClause
   return . map snd . sortBy (comparing fst) . catMaybes . for bindings $
      \AST.Decl{dDefinition, dName} -> do
         (from, index) <- tupleSelInfo dDefinition
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
