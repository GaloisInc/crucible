{-
Module           : UCCrux.LLVM.View.FullType
Description      : See "UCCrux.LLVM.View".
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.View.FullType
  ( VarArgsReprView(..),
    varArgsReprView,
    viewVarArgsRepr,
    StructPackedReprView(..),
    structPackedReprView,
    viewStructPackedRepr,
    FloatInfoReprView(..),
    floatInfoReprView,
    viewFloatInfoRepr,
    FullTypeReprViewError,
    ppFullTypeReprViewError,
    FullTypeReprView(..),
    fullTypeReprView,
    viewFullTypeRepr,
    PartTypeReprView(..),
    partTypeReprView,
    viewPartTypeRepr,
  )
where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import qualified Data.Text as Text
import           GHC.Generics (Generic)
import           Numeric.Natural (Natural)

import           Prettyprinter (Doc)
import qualified Prettyprinter as PP

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.TraversableFC (toListFC)
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.SymbolRepr (someSymbol, SymbolRepr (symbolRepr))

import qualified What4.InterpretedFloatingPoint as W4IFP
import           What4.InterpretedFloatingPoint (FloatInfoRepr)

import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), PartTypeRepr, aliasOrFullType, ModuleTypes, toPartType, makePartTypeRepr, StructPackedRepr(PackedStructRepr, UnpackedStructRepr))
import           UCCrux.LLVM.View.Util (TypeName(..), Width (Width))
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr(IsVarArgsRepr, NotVarArgsRepr))

data VarArgsReprView
  = IsVarArgsReprView
  | NotVarArgsReprView
  deriving (Eq, Ord, Show, Generic)

varArgsReprView :: VarArgsRepr va -> VarArgsReprView
varArgsReprView =
  \case
    IsVarArgsRepr -> IsVarArgsReprView
    NotVarArgsRepr -> NotVarArgsReprView

viewVarArgsRepr :: VarArgsReprView -> Some VarArgsRepr
viewVarArgsRepr =
  \case
    IsVarArgsReprView -> Some IsVarArgsRepr
    NotVarArgsReprView -> Some NotVarArgsRepr

data StructPackedReprView
  = PackedStructReprView
  | UnpackedStructReprView
  deriving (Eq, Ord, Show, Generic)

structPackedReprView :: StructPackedRepr va -> StructPackedReprView
structPackedReprView =
  \case
    PackedStructRepr -> PackedStructReprView
    UnpackedStructRepr -> UnpackedStructReprView

viewStructPackedRepr :: StructPackedReprView -> Some StructPackedRepr
viewStructPackedRepr =
  \case
    PackedStructReprView -> Some PackedStructRepr
    UnpackedStructReprView -> Some UnpackedStructRepr

data FloatInfoReprView
  = VHalfFloatRepr
  | VSingleFloatRepr
  | VDoubleFloatRepr
  | VQuadFloatRepr
  | VX86_80FloatRepr
  | VDoubleDoubleFloatRepr
  deriving (Eq, Ord, Show, Generic)

floatInfoReprView :: FloatInfoRepr fi -> FloatInfoReprView
floatInfoReprView =
  \case
    W4IFP.HalfFloatRepr -> VHalfFloatRepr
    W4IFP.SingleFloatRepr -> VSingleFloatRepr
    W4IFP.DoubleFloatRepr -> VDoubleFloatRepr
    W4IFP.QuadFloatRepr -> VQuadFloatRepr
    W4IFP.X86_80FloatRepr -> VX86_80FloatRepr
    W4IFP.DoubleDoubleFloatRepr -> VDoubleDoubleFloatRepr

viewFloatInfoRepr :: FloatInfoReprView -> Some FloatInfoRepr
viewFloatInfoRepr =
  \case
    VHalfFloatRepr -> Some W4IFP.HalfFloatRepr
    VSingleFloatRepr -> Some W4IFP.SingleFloatRepr
    VDoubleFloatRepr -> Some W4IFP.DoubleFloatRepr
    VQuadFloatRepr -> Some W4IFP.QuadFloatRepr
    VX86_80FloatRepr -> Some W4IFP.X86_80FloatRepr
    VDoubleDoubleFloatRepr -> Some W4IFP.DoubleDoubleFloatRepr

data FullTypeReprView
  = VFTIntRepr Width
  | VFTPtrRepr PartTypeReprView
  | VFTFloatRepr FloatInfoReprView
  | VFTArrayRepr Natural FullTypeReprView
  | VFTUnboundedArrayRepr FullTypeReprView
  | VFTStructRepr StructPackedReprView [FullTypeReprView]
  | VFTVoidFuncPtrRepr VarArgsReprView [FullTypeReprView]
  | VFTNonVoidFuncPtrRepr VarArgsReprView FullTypeReprView [FullTypeReprView]
  | VFTOpaquePtrRepr TypeName
  deriving (Eq, Ord, Show, Generic)

fullTypeReprView :: FullTypeRepr m ft -> FullTypeReprView
fullTypeReprView =
  \case
    FTIntRepr natRepr -> VFTIntRepr (Width (NatRepr.natValue natRepr))
    FTPtrRepr ptRepr -> VFTPtrRepr (partTypeReprView ptRepr)
    FTFloatRepr floatInfo -> VFTFloatRepr (floatInfoReprView floatInfo)
    FTArrayRepr natRepr elems ->
      VFTArrayRepr (NatRepr.natValue natRepr) (fullTypeReprView elems)
    FTUnboundedArrayRepr elems ->
      VFTUnboundedArrayRepr (fullTypeReprView elems)
    FTStructRepr sp fields ->
      VFTStructRepr (structPackedReprView sp) (toListFC fullTypeReprView fields)
    FTVoidFuncPtrRepr varArgs args ->
      VFTVoidFuncPtrRepr (varArgsReprView varArgs) (toListFC fullTypeReprView args)
    FTNonVoidFuncPtrRepr varArgs retRepr args ->
      VFTNonVoidFuncPtrRepr
        (varArgsReprView varArgs)
        (fullTypeReprView retRepr)
        (toListFC fullTypeReprView args)
    FTOpaquePtrRepr symb -> VFTOpaquePtrRepr (TypeName (symbolRepr symb))

data FullTypeReprViewError
  = ZeroWidth
  | ZeroArraySize
  | BadAlias L.Ident
  deriving (Eq, Ord, Show)

ppFullTypeReprViewError :: FullTypeReprViewError -> Doc ann
ppFullTypeReprViewError =
  \case
    ZeroWidth -> "Zero-width integer"
    ZeroArraySize -> "Zero-size array"
    BadAlias (L.Ident nm) -> "Non-existing type alias: " <> PP.pretty nm

viewFullTypeRepr ::
  ModuleTypes m ->
  FullTypeReprView ->
  Either FullTypeReprViewError (Some (FullTypeRepr m))
viewFullTypeRepr mts =
  \case
    VFTIntRepr (Width w) ->
      case NatRepr.mkNatRepr w of
        Some natRepr ->
          case NatRepr.isZeroOrGT1 natRepr of
            Left NatRepr.Refl -> Left ZeroWidth
            Right NatRepr.LeqProof -> Right (Some (FTIntRepr natRepr))
    VFTPtrRepr vpt ->
      do Some pt <- viewPartTypeRepr mts vpt
         return (Some (FTPtrRepr pt))
    VFTFloatRepr vfi ->
      do Some fi <- return (viewFloatInfoRepr vfi)
         return (Some (FTFloatRepr fi))
    VFTArrayRepr nat vft ->
      case (NatRepr.mkNatRepr nat, viewFullTypeRepr mts vft) of
        (_, Left err) -> Left err
        (Some natRepr, Right (Some ft)) ->
          case NatRepr.isZeroOrGT1 natRepr of
            Left NatRepr.Refl -> Left ZeroArraySize
            Right NatRepr.LeqProof -> Right (Some (FTArrayRepr natRepr ft))
    VFTUnboundedArrayRepr vft ->
      do Some ft <- viewFullTypeRepr mts vft
         return (Some (FTUnboundedArrayRepr ft))
    VFTStructRepr vsp vfields ->
      do Some sp <- return (viewStructPackedRepr vsp)
         Some fields <- Ctx.fromList <$> traverse (viewFullTypeRepr mts) vfields
         return (Some (FTStructRepr sp fields))
    VFTVoidFuncPtrRepr vva vargs ->
      do Some va <- return (viewVarArgsRepr vva)
         Some args <- Ctx.fromList <$> traverse (viewFullTypeRepr mts) vargs
         return (Some (FTVoidFuncPtrRepr va args))
    VFTNonVoidFuncPtrRepr vva vret vargs ->
      do Some va <- return (viewVarArgsRepr vva)
         Some args <- Ctx.fromList <$> traverse (viewFullTypeRepr mts) vargs
         Some ret <- viewFullTypeRepr mts vret
         return (Some (FTNonVoidFuncPtrRepr va ret args))
    VFTOpaquePtrRepr (TypeName nm) ->
      do Some symb <- return (someSymbol nm)
         return (Some (FTOpaquePtrRepr symb))

data PartTypeReprView
  = VPTFullRepr FullTypeReprView
  | VPTAliasRepr TypeName
  deriving (Eq, Ord, Show, Generic)

partTypeReprView :: PartTypeRepr m ft -> PartTypeReprView
partTypeReprView ptRepr =
  case aliasOrFullType ptRepr of
    Left (L.Ident iden) -> VPTAliasRepr (TypeName (Text.pack iden))
    Right ft -> VPTFullRepr (fullTypeReprView ft)

viewPartTypeRepr ::
  ModuleTypes m ->
  PartTypeReprView ->
  Either FullTypeReprViewError  (Some (PartTypeRepr m))
viewPartTypeRepr mts =
  \case
    VPTFullRepr vft ->
      do Some ft <- viewFullTypeRepr mts vft
         return (Some (toPartType ft))
    VPTAliasRepr (TypeName nm) ->
      let iden = L.Ident (Text.unpack nm)
      in case makePartTypeRepr mts iden of
           Just spt -> Right spt
           Nothing -> Left (BadAlias iden)

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''StructPackedReprView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''VarArgsReprView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''FloatInfoReprView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''FullTypeReprView)
$(Aeson.TH.deriveJSON Aeson.defaultOptions ''PartTypeReprView)
