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
{-# LANGUAGE ImplicitParams #-}
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
{- ORMOLU_ENABLE -}

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
    FTVoidFuncPtrRepr argsRepr -> funType Nothing argsRepr
    FTNonVoidFuncPtrRepr retRepr argsRepr -> funType (Just retRepr) argsRepr
    FTOpaquePtrRepr _ident -> PtrType OpaqueType
    FTArrayRepr natRepr fullTypeRepr -> ArrayType (natValue natRepr) (toMemType fullTypeRepr)
    FTStructRepr structInfo _ -> StructType structInfo
  where
    funType :: Maybe (FullTypeRepr m ft) -> Ctx.Assignment (FullTypeRepr m) argTypes -> MemType
    funType maybeRetRepr argsRepr =
      PtrType
        ( FunType
            ( FunDecl
                (toMemType <$> maybeRetRepr)
                (toListFC toMemType argsRepr)
                False
            )
        )
