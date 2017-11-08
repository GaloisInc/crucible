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

{-# OPTIONS_GHC -fno-warn-orphans #-}
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
, PtrWidth
, ptrWidth
, LLVMPointerType
, llvmPointerRepr
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

import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import           Lang.Crucible.LLVM.MemType



type VarArgs   = VectorType AnyType

varArgsRepr :: TypeRepr VarArgs
varArgsRepr = VectorRepr AnyRepr


type PtrWidth = 64
ptrWidth :: NatRepr PtrWidth
ptrWidth = knownNat

type LLVMPointerType = RecursiveType "LLVM_pointer"
llvmPointerRepr :: TypeRepr LLVMPointerType
llvmPointerRepr = knownRepr

instance IsRecursiveType "LLVM_pointer" where
  type UnrollType "LLVM_pointer" =
     VariantType (EmptyCtx ::>
       BVType PtrWidth ::>
       StructType (EmptyCtx ::> NatType ::> BVType PtrWidth ::> BVType PtrWidth))
  unrollType _ =
     VariantRepr (Ctx.empty Ctx.:>
       BVRepr ptrWidth Ctx.:>
       StructRepr (Ctx.empty Ctx.:>NatRepr Ctx.:> BVRepr ptrWidth Ctx.:> BVRepr ptrWidth))


pattern LLVMPointerRepr :: () => (ty ~ LLVMPointerType) => TypeRepr ty
pattern LLVMPointerRepr <- RecursiveRepr (testEquality (knownSymbol :: SymbolRepr "LLVM_pointer") -> Just Refl)
  where
    LLVMPointerRepr = llvmPointerRepr


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



liftRetType :: (?lc :: TyCtx.LLVMContext, Monad m)
            => L.Type
            -> m (Maybe MemType)
liftRetType t =
  case TyCtx.liftRetType t of
    Just mt -> return mt
    Nothing -> fail $ unwords ["Expected return type: ", show t]


liftMemType :: (?lc :: TyCtx.LLVMContext, Monad m)
            => L.Type
            -> m MemType
liftMemType t =
  case TyCtx.liftMemType t of
    Just mt -> return mt
    Nothing -> fail $ unwords ["Expected memory type: ", show t]


liftDeclare :: (?lc::TyCtx.LLVMContext, Monad m) => L.Declare -> m FunDecl
liftDeclare decl =
  do args <- traverse liftMemType (L.decArgs decl)
     ret  <- liftRetType (L.decRetType decl)
     return $ FunDecl
              { fdRetType  = ret
              , fdArgTypes = args
              , fdVarArgs  = L.decVarArgs decl
              }

-----------------------------------------------------------------------------------------
-- Type translations

-- | Translate a list of LLVM expressions into a crucible type context,
--   which is passed into the given continuation.
llvmTypesAsCtx :: forall a
                . (?lc :: TyCtx.LLVMContext)
               => [MemType]
               -> (forall ctx. CtxRepr ctx -> a)
               -> a
llvmTypesAsCtx xs f = go (concatMap llvmTypeToRepr xs) Ctx.empty
 where go :: forall ctx. [Some TypeRepr] -> CtxRepr ctx -> a
       go []       ctx      = f ctx
       go (Some tp:tps) ctx = go tps (ctx Ctx.:> tp)

-- | Translate an LLVM type into a crucible type, which is passed into
--   the given continuation
llvmTypeAsRepr :: forall a
                . (?lc :: TyCtx.LLVMContext)
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
llvmRetTypeAsRepr :: forall a
                   . (?lc :: TyCtx.LLVMContext)
                  => Maybe MemType
                  -> (forall tp. TypeRepr tp -> a)
                  -> a
llvmRetTypeAsRepr Nothing   f = f UnitRepr
llvmRetTypeAsRepr (Just tp) f = llvmTypeAsRepr tp f

-- | Actually perform the type translation
llvmTypeToRepr :: (?lc :: TyCtx.LLVMContext) => MemType -> [Some TypeRepr]
llvmTypeToRepr (ArrayType _ tp)  = [llvmTypeAsRepr tp (\t -> Some (VectorRepr t))]
llvmTypeToRepr (VecType _ tp)    = [llvmTypeAsRepr tp (\t-> Some (VectorRepr t))]
llvmTypeToRepr (StructType si)   = [llvmTypesAsCtx tps (\ts -> Some (StructRepr ts))]
  where tps = map fiType $ toList $ siFields si
llvmTypeToRepr (PtrType _)   = [Some LLVMPointerRepr]
llvmTypeToRepr FloatType     = [Some RealValRepr]
llvmTypeToRepr DoubleType    = [Some RealValRepr]
--llvmTypeToRepr FloatType   = [Some (FloatRepr SingleFloatRepr)]
--llvmTypeToRepr DoubleType  = [Some (FloatRepr DoubleFloatRepr)]
llvmTypeToRepr MetadataType = []
llvmTypeToRepr (IntType n) =
   case someNat (fromIntegral n) of
      -- NB! Special case! All integer types that are the same width as pointers are
      -- interpreted as pointer types!  The LLVMPointer Crucible type is a disjoint
      -- union of raw bitvectors and actual pointers.
      Just (Some w) | Just Refl <- testEquality w ptrWidth -> [Some LLVMPointerRepr]

      Just (Some w) | Just LeqProof <- isPosNat w -> [Some (BVRepr w)]

      _ -> error $ unwords ["invalid integer width",show n]

llvmDeclToFunHandleRepr
   :: (?lc :: TyCtx.LLVMContext)
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
