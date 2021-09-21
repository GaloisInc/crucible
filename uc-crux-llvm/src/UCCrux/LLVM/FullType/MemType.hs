{-
Module           : UCCrux.LLVM.FullType.MemType
Description      : Interop between 'FullType' and 'MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.FullType.MemType
  ( toMemType,
  )
where

{- ORMOLU_DISABLE -}
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (natValue)
import           Data.Parameterized.TraversableFC (toListFC)

import qualified What4.InterpretedFloatingPoint as W4IFP

import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..), FunDecl(..))

import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), aliasOrFullType)
import           UCCrux.LLVM.FullType.VarArgs (varArgsReprToBool)
{- ORMOLU_ENABLE -}

-- | Postcondition: The returned 'MemType' will not be a metadata type.
--
-- @toStorageType@ depends on this.
toMemType :: FullTypeRepr m ft -> MemType
toMemType =
  \case
    FTIntRepr natRepr -> IntType (natValue natRepr)
    FTPtrRepr ptRepr ->
      case aliasOrFullType ptRepr of
        Left ident -> PtrType (Alias ident)
        Right ftRepr -> PtrType (MemType (toMemType ftRepr))
    FTFloatRepr W4IFP.SingleFloatRepr -> FloatType
    FTFloatRepr W4IFP.DoubleFloatRepr -> DoubleType
    FTFloatRepr W4IFP.X86_80FloatRepr -> X86_FP80Type
    FTFloatRepr floatInfo -> panic "toMemType" ["Illegal float type: ", show floatInfo]
    FTVoidFuncPtrRepr varArgs argsRepr ->
      funType Nothing argsRepr (varArgsReprToBool varArgs)
    FTNonVoidFuncPtrRepr varArgs retRepr argsRepr ->
      funType (Just retRepr) argsRepr (varArgsReprToBool varArgs)
    FTOpaquePtrRepr _ident -> PtrType OpaqueType
    FTArrayRepr natRepr fullTypeRepr -> ArrayType (natValue natRepr) (toMemType fullTypeRepr)
    FTUnboundedArrayRepr fullTypeRepr -> ArrayType 0 (toMemType fullTypeRepr)
    FTStructRepr structInfo _ -> StructType structInfo
  where
    funType :: Maybe (FullTypeRepr m ft) -> Ctx.Assignment (FullTypeRepr m) argTypes -> Bool -> MemType
    funType maybeRetRepr argsRepr isVarArgs =
      PtrType
        ( FunType
            ( FunDecl
                (toMemType <$> maybeRetRepr)
                (toListFC toMemType argsRepr)
                isVarArgs
            )
        )
