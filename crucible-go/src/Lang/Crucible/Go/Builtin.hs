{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
module Lang.Crucible.Go.Builtin (translateBuiltin) where

import           Control.Monad.State

import           Data.Functor.Product
import           Data.Text as T hiding (foldl, length, zip)

import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))

import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Generator as Gen

import           What4.Utils.StringLiteral

import           Language.Go.AST
import           Language.Go.Rec
import           Language.Go.Types
import           Lang.Crucible.Go.Encodings
import           Lang.Crucible.Go.TransUtil
import           Lang.Crucible.Go.Types

translateBuiltin :: Show a
                 => Ident
                 -> Ident
                 -> [Product (Node a) TranslateM Expr]
                 -> TranslateM' (Translated Expr)
translateBuiltin _qual ident@(Ident _k name) args = do
  Some retRepr <- gets retRepr
  translated_args <- mapM runTranslated args
  return $ mkTranslatedExpr retRepr $ do
    case name of
      "len" -> do
        args' <- forM translated_args $ runTranslatedExpr retRepr
        case args' of
          [Some (GoExpr _loc arg)] ->
            tryAsArray arg
            (\arrRepr arr -> do
                vec <- Gen.readRef arr
                return $ mkSomeGoExpr $ natToBV64 $ Gen.App $ C.VectorSize vec
            ) $
            tryAsSlice arg
            (\sliceRepr slice -> do
                end <- sliceEnd slice
                begin <- sliceBegin slice
                return $ mkSomeGoExpr $ natToBV64 $ Gen.App $ C.NatSub end begin
            ) $
            tryAsString arg
            (\si str ->
               return $ mkSomeGoExpr $ natToBV64 $ Gen.App $ C.StringLength str
            ) $
            fail $ "translateBuiltin: invalid argument for 'len': " ++ show arg
          _args ->
            fail $ "translateBuiltin: expected exactly one argument to\
                   \ 'len', got " ++ show args'
      "make" -> undefined -- TODO
      "new" -> case zip args translated_args of
        [(Pair arg_node _argM, TranslatedType (Some repr))] -> do
          zero <- zeroValue' (typeOf' arg_node) repr
          ptr <- newRefPointer zero
          return $ mkSomeGoExpr ptr
        _args ->
          fail $ "translateBuiltin: expected exactly one type argument to\
                 \ 'new', got " ++ show (proj1 <$> args)
      "panic" -> do
        args' <- forM translated_args $ runTranslatedExpr retRepr
        Gen.reportError $ Gen.App $ C.StringLit $
          UnicodeLiteral $ T.pack $ "panic: " ++ show args'
      "print" -> do
        args' <- forM translated_args $ runTranslatedExpr retRepr
        Gen.addPrintStmt $ Gen.App $ C.StringLit $
          UnicodeLiteral $ T.pack $ show args'
        return $ mkSomeGoExpr' $ C.MkStruct Ctx.empty Ctx.empty
      -- TODO: more
      _nm ->
        fail $ "translateBuiltin: unknown identifier: " ++ show ident
