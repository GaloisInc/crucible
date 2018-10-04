{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Types
-- Description      : Translation of LLVM AST into Crucible control-flow graph
-- Copyright        : (c) Galois, Inc 2014-2015
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
--
-- This module defines the translation from LLVM types to Crucible types.
--
-- The translation of the LLVM types themselves is not so difficult;
-- however, navigating the fact that Crucible expressions are strongly
-- typed at the Haskell level, whereas the LLVM types are not makes for
-- some slightly strange programming idioms.  In particular, all the
-- functions that do the type translation are written in a polymorphic
-- continuation-passing style.
----------------------------------------------------------------------

module Lang.Crucible.LLVM.Translation.Types
( VarArgs
, varArgsRepr
, llvmTypesAsCtx
, llvmTypeAsRepr
, llvmRetTypeAsRepr
, llvmDeclToFunHandleRepr
, LLVMPointerType
, pattern PtrWidth
, pattern LLVMPointerRepr
, declareFromDefine
, allModuleDeclares
, liftMemType
, liftRetType
, liftDeclare
) where

import           Data.Foldable

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some

import           Lang.Crucible.Types

import           Lang.Crucible.LLVM.MemModel.Pointer
import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.TypeContext as TyCtx


type VarArgs   = VectorType AnyType

varArgsRepr :: TypeRepr VarArgs
varArgsRepr = VectorRepr AnyRepr

------------------------------------------------------------------------
-- LLVM AST utilities

declareFromDefine :: L.Define -> L.Declare
declareFromDefine d =
  L.Declare { L.decRetType = L.defRetType d
            , L.decName = L.defName d
            , L.decArgs = L.typedType <$> L.defArgs d
            , L.decVarArgs = L.defVarArgs d
            , L.decAttrs   = L.defAttrs d
            , L.decComdat  = mempty
            }

-- | Return all declarations derived from both external symbols and
-- internal definitions.
allModuleDeclares :: L.Module -> [L.Declare]
allModuleDeclares m = L.modDeclares m ++ def_decls
  where def_decls = declareFromDefine <$> L.modDefines m

-----------------------------------------------------------------------------------------
-- Type translations

-- | Translate a list of LLVM expressions into a crucible type context,
--   which is passed into the given continuation.
llvmTypesAsCtx :: forall a wptr
                . (?lc :: TypeContext, HasPtrWidth wptr)
               => [MemType]
               -> (forall ctx. CtxRepr ctx -> a)
               -> a
llvmTypesAsCtx xs f = go (concatMap llvmTypeToRepr xs) Ctx.empty
 where go :: forall ctx. [Some TypeRepr] -> CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)

-- | Translate an LLVM type into a crucible type, which is passed into
--   the given continuation
llvmTypeAsRepr :: forall a wptr
                . (?lc :: TypeContext, HasPtrWidth wptr)
               => MemType
               -> (forall tp. TypeRepr tp -> a)
               -> a
llvmTypeAsRepr xs f = go (llvmTypeToRepr xs)
 where go :: [Some TypeRepr] -> a
       go []       = f UnitRepr
       go [Some x] = f x

       go _ = error $ unwords ["llvmTypesAsRepr: expected a single value type", show xs]

-- | Translate an LLVM return type into a crucible type, which is passed into
--   the given continuation
llvmRetTypeAsRepr :: forall a wptr
                   . (?lc :: TypeContext, HasPtrWidth wptr)
                  => Maybe MemType
                  -> (forall tp. TypeRepr tp -> a)
                  -> a
llvmRetTypeAsRepr Nothing   f = f UnitRepr
llvmRetTypeAsRepr (Just tp) f = llvmTypeAsRepr tp f

-- | Actually perform the type translation
llvmTypeToRepr :: (HasPtrWidth wptr, ?lc :: TypeContext) => MemType -> [Some TypeRepr]
llvmTypeToRepr (ArrayType _ tp)  = [llvmTypeAsRepr tp (\t -> Some (VectorRepr t))]
llvmTypeToRepr (VecType _ tp)    = [llvmTypeAsRepr tp (\t-> Some (VectorRepr t))]
llvmTypeToRepr (StructType si)   = [llvmTypesAsCtx tps (\ts -> Some (StructRepr ts))]
  where tps = map fiType $ toList $ siFields si
llvmTypeToRepr (PtrType _)  = [Some (LLVMPointerRepr PtrWidth)]
llvmTypeToRepr FloatType    = [Some (FloatRepr SingleFloatRepr)]
llvmTypeToRepr DoubleType   = [Some (FloatRepr DoubleFloatRepr)]
llvmTypeToRepr MetadataType = []
llvmTypeToRepr (IntType n) =
   case someNat (fromIntegral n) of
      Just (Some w) | Just LeqProof <- isPosNat w -> [Some (LLVMPointerRepr w)]
      _ -> error $ unwords ["invalid integer width",show n]

-- | Compute the function Crucible function signature
--   that corresponds to the given LLVM function declaration.
llvmDeclToFunHandleRepr
   :: (?lc :: TypeContext, HasPtrWidth wptr)
   => FunDecl
   -> (forall args ret. CtxRepr args -> TypeRepr ret -> a)
   -> a
llvmDeclToFunHandleRepr decl k =
  llvmTypesAsCtx (fdArgTypes decl) $ \args ->
    llvmRetTypeAsRepr (fdRetType decl) $ \ret ->
      if fdVarArgs decl then
        k (args Ctx.:> varArgsRepr) ret
      else
        k args ret



