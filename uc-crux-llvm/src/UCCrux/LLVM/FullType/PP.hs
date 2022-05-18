{-
Module           : UCCrux.LLVM.FullType.PP
Description      : Pretty-printing 'FullTypeRepr'
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

These functions are in their own module (instead of in
"UCCrux.LLVM.FullType.PP.Type") to ensure only a small amount of code has access
to the constructors of 'PartTypeRepr', which can be used to violate its
invariant.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}

module UCCrux.LLVM.FullType.PP
  ( ppFullTypeRepr,
    ppPartTypeRepr
  )
where

import           Numeric.Natural (Natural)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import           Data.Parameterized.TraversableFC (toListFC)
import           Data.Parameterized.NatRepr (natValue)
import           Data.Parameterized.SymbolRepr (symbolRepr)

import           What4.InterpretedFloatingPoint (FloatInfoRepr(..))

import qualified Lang.Crucible.LLVM.PrettyPrint as CruPP

import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), PartTypeRepr, aliasOrFullType, structPackedReprToBool)
import           UCCrux.LLVM.FullType.VarArgs (varArgsReprToBool)

-- | c.f. "Lang.Crucible.LLVM.MemModel.Type.ppType". We don't reuse that
-- function in order to avoid the need for a @DataLayout@ argument.
ppFullTypeRepr :: FullTypeRepr m ft -> Doc ann
ppFullTypeRepr =
  \case
    FTIntRepr width -> CruPP.ppIntType (natValue width :: Natural)
    FTPtrRepr ptRep -> CruPP.ppPtrType (ppPartTypeRepr ptRep)
    FTFloatRepr HalfFloatRepr -> "half"
    FTFloatRepr SingleFloatRepr -> "float"
    FTFloatRepr DoubleFloatRepr -> "double"
    FTFloatRepr QuadFloatRepr -> "quad float"
    FTFloatRepr X86_80FloatRepr -> "x86_FP80"
    FTFloatRepr DoubleDoubleFloatRepr -> "double double"
    FTArrayRepr size elemTy ->
      CruPP.ppArrayType (natValue size) (ppFullTypeRepr elemTy)
    FTUnboundedArrayRepr elemTy ->
      CruPP.ppArrayType 0 (ppFullTypeRepr elemTy)
    FTStructRepr sp fields ->
      (if structPackedReprToBool sp then PP.angles else id)
        (PP.brackets (PP.hsep (PP.punctuate "," (toListFC ppFullTypeRepr fields))))
    FTVoidFuncPtrRepr va args ->
      PP.hsep
        [ ppFuncArgs va args
        , "-> ()"
        ]
    FTNonVoidFuncPtrRepr va ret args ->
      PP.hsep
        [ ppFuncArgs va args
        , "-> "
        , ppFullTypeRepr ret
        ]
    FTOpaquePtrRepr symb -> PP.pretty (symbolRepr symb)
  where
    ppFuncArgs va args =
      PP.hsep (PP.punctuate " ->" (toListFC ppFullTypeRepr args))
        <> if varArgsReprToBool va then "..." else mempty

ppPartTypeRepr :: PartTypeRepr m ft -> Doc ann
ppPartTypeRepr ptRepr =
  case aliasOrFullType ptRepr of
    Left (L.Ident iden) -> PP.pretty iden
    Right ft -> ppFullTypeRepr ft
