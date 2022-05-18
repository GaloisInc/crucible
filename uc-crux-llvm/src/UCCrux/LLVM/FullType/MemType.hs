{-
Module           : UCCrux.LLVM.FullType.MemType
Description      : Interop between 'FullType' and 'MemType' and 'SymType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

These functions are in their own module (instead of in
"UCCrux.LLVM.FullType.PP.Type") to ensure only a small amount of code has access
to the constructors of 'PartTypeRepr', which can be used to violate its
invariant.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module UCCrux.LLVM.FullType.MemType
  ( toMemType,
    toSymType
  )
where

{- ORMOLU_DISABLE -}
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (natValue)
import           Data.Parameterized.TraversableFC (toListFC)

import qualified What4.InterpretedFloatingPoint as W4IFP

import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..), FunDecl(..), mkStructInfo)

import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), PartTypeRepr, aliasOrFullType, DataLayout, crucibleDataLayout, structPackedReprToBool)
import           UCCrux.LLVM.FullType.VarArgs (varArgsReprToBool)
{- ORMOLU_ENABLE -}

-- | Postcondition: The returned 'MemType' will not be a metadata type.
--
-- @toStorageType@ depends on this.
toMemType :: forall m ft. DataLayout m -> FullTypeRepr m ft -> MemType
toMemType dl =
  \case
    FTIntRepr natRepr -> IntType (natValue natRepr)
    FTPtrRepr ptRepr -> PtrType (toSymType dl ptRepr)
    FTFloatRepr W4IFP.SingleFloatRepr -> FloatType
    FTFloatRepr W4IFP.DoubleFloatRepr -> DoubleType
    FTFloatRepr W4IFP.X86_80FloatRepr -> X86_FP80Type
    FTFloatRepr floatInfo -> panic "toMemType" ["Illegal float type: ", show floatInfo]
    FTVoidFuncPtrRepr varArgs argsRepr ->
      funType Nothing argsRepr (varArgsReprToBool varArgs)
    FTNonVoidFuncPtrRepr varArgs retRepr argsRepr ->
      funType (Just retRepr) argsRepr (varArgsReprToBool varArgs)
    FTOpaquePtrRepr _ident -> PtrType OpaqueType
    FTArrayRepr natRepr fullTypeRepr -> ArrayType (natValue natRepr) (toMemType dl fullTypeRepr)
    FTUnboundedArrayRepr fullTypeRepr -> ArrayType 0 (toMemType dl fullTypeRepr)
    FTStructRepr sp fields ->
      let cdl = crucibleDataLayout dl
          memFields = toListFC (toMemType dl) fields
      in StructType (mkStructInfo cdl (structPackedReprToBool sp) memFields)
  where
    funType ::
      forall ft' argTypes.
      Maybe (FullTypeRepr m ft') ->
      Ctx.Assignment (FullTypeRepr m) argTypes ->
      Bool ->
      MemType
    funType maybeRetRepr argsRepr isVarArgs =
      PtrType
        ( FunType
            ( FunDecl
                (toMemType dl <$> maybeRetRepr)
                (toListFC (toMemType dl) argsRepr)
                isVarArgs
            )
        )

toSymType :: DataLayout m -> PartTypeRepr m ft -> SymType
toSymType dl ptRepr =
  case aliasOrFullType ptRepr of
    Left ident -> Alias ident
    Right ftRepr -> MemType (toMemType dl ftRepr)
