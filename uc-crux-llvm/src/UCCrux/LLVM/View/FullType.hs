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
import qualified UCCrux.LLVM.View.Options.FullType as Opts
import           UCCrux.LLVM.View.TH (deriveMutualJSON)

data VarArgsReprView
  = IsVarArgsReprView
  | NotVarArgsReprView
  deriving (Bounded, Enum, Eq, Ord, Show, Generic)

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
  deriving (Bounded, Enum, Eq, Ord, Show, Generic)

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
  = HalfFloatReprView
  | SingleFloatReprView
  | DoubleFloatReprView
  | QuadFloatReprView
  | X86_80FloatReprView
  | DoubleDoubleFloatReprView
  deriving (Bounded, Enum, Eq, Ord, Show, Generic)

floatInfoReprView :: FloatInfoRepr fi -> FloatInfoReprView
floatInfoReprView =
  \case
    W4IFP.HalfFloatRepr -> HalfFloatReprView
    W4IFP.SingleFloatRepr -> SingleFloatReprView
    W4IFP.DoubleFloatRepr -> DoubleFloatReprView
    W4IFP.QuadFloatRepr -> QuadFloatReprView
    W4IFP.X86_80FloatRepr -> X86_80FloatReprView
    W4IFP.DoubleDoubleFloatRepr -> DoubleDoubleFloatReprView

viewFloatInfoRepr :: FloatInfoReprView -> Some FloatInfoRepr
viewFloatInfoRepr =
  \case
    HalfFloatReprView -> Some W4IFP.HalfFloatRepr
    SingleFloatReprView -> Some W4IFP.SingleFloatRepr
    DoubleFloatReprView -> Some W4IFP.DoubleFloatRepr
    QuadFloatReprView -> Some W4IFP.QuadFloatRepr
    X86_80FloatReprView -> Some W4IFP.X86_80FloatRepr
    DoubleDoubleFloatReprView -> Some W4IFP.DoubleDoubleFloatRepr

data FullTypeReprView
  = FTIntReprView Width
  | FTPtrReprView PartTypeReprView
  | FTFloatReprView FloatInfoReprView
  | FTArrayReprView Natural FullTypeReprView
  | FTUnboundedArrayReprView FullTypeReprView
  | FTStructReprView StructPackedReprView [FullTypeReprView]
  | FTVoidFuncPtrReprView VarArgsReprView [FullTypeReprView]
  | FTNonVoidFuncPtrReprView VarArgsReprView FullTypeReprView [FullTypeReprView]
  | FTOpaquePtrReprView TypeName
  deriving (Eq, Ord, Show, Generic)

fullTypeReprView :: FullTypeRepr m ft -> FullTypeReprView
fullTypeReprView =
  \case
    FTIntRepr natRepr -> FTIntReprView (Width (NatRepr.natValue natRepr))
    FTPtrRepr ptRepr -> FTPtrReprView (partTypeReprView ptRepr)
    FTFloatRepr floatInfo -> FTFloatReprView (floatInfoReprView floatInfo)
    FTArrayRepr natRepr elems ->
      FTArrayReprView (NatRepr.natValue natRepr) (fullTypeReprView elems)
    FTUnboundedArrayRepr elems ->
      FTUnboundedArrayReprView (fullTypeReprView elems)
    FTStructRepr sp fields ->
      FTStructReprView (structPackedReprView sp) (toListFC fullTypeReprView fields)
    FTVoidFuncPtrRepr varArgs args ->
      FTVoidFuncPtrReprView (varArgsReprView varArgs) (toListFC fullTypeReprView args)
    FTNonVoidFuncPtrRepr varArgs retRepr args ->
      FTNonVoidFuncPtrReprView
        (varArgsReprView varArgs)
        (fullTypeReprView retRepr)
        (toListFC fullTypeReprView args)
    FTOpaquePtrRepr symb -> FTOpaquePtrReprView (TypeName (symbolRepr symb))

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
    FTIntReprView (Width w) ->
      case NatRepr.mkNatRepr w of
        Some natRepr ->
          case NatRepr.isZeroOrGT1 natRepr of
            Left NatRepr.Refl -> Left ZeroWidth
            Right NatRepr.LeqProof -> Right (Some (FTIntRepr natRepr))
    FTPtrReprView vpt ->
      do Some pt <- viewPartTypeRepr mts vpt
         return (Some (FTPtrRepr pt))
    FTFloatReprView vfi ->
      do Some fi <- return (viewFloatInfoRepr vfi)
         return (Some (FTFloatRepr fi))
    FTArrayReprView nat vft ->
      case (NatRepr.mkNatRepr nat, viewFullTypeRepr mts vft) of
        (_, Left err) -> Left err
        (Some natRepr, Right (Some ft)) ->
          case NatRepr.isZeroOrGT1 natRepr of
            Left NatRepr.Refl -> Left ZeroArraySize
            Right NatRepr.LeqProof -> Right (Some (FTArrayRepr natRepr ft))
    FTUnboundedArrayReprView vft ->
      do Some ft <- viewFullTypeRepr mts vft
         return (Some (FTUnboundedArrayRepr ft))
    FTStructReprView vsp vfields ->
      do Some sp <- return (viewStructPackedRepr vsp)
         Some fields <- Ctx.fromList <$> traverse (viewFullTypeRepr mts) vfields
         return (Some (FTStructRepr sp fields))
    FTVoidFuncPtrReprView vva vargs ->
      do Some va <- return (viewVarArgsRepr vva)
         Some args <- Ctx.fromList <$> traverse (viewFullTypeRepr mts) vargs
         return (Some (FTVoidFuncPtrRepr va args))
    FTNonVoidFuncPtrReprView vva vret vargs ->
      do Some va <- return (viewVarArgsRepr vva)
         Some args <- Ctx.fromList <$> traverse (viewFullTypeRepr mts) vargs
         Some ret <- viewFullTypeRepr mts vret
         return (Some (FTNonVoidFuncPtrRepr va ret args))
    FTOpaquePtrReprView (TypeName nm) ->
      do Some symb <- return (someSymbol nm)
         return (Some (FTOpaquePtrRepr symb))

data PartTypeReprView
  = PTFullReprView FullTypeReprView
  | PTAliasReprView TypeName
  deriving (Eq, Ord, Show, Generic)

partTypeReprView :: PartTypeRepr m ft -> PartTypeReprView
partTypeReprView ptRepr =
  case aliasOrFullType ptRepr of
    Left (L.Ident iden) -> PTAliasReprView (TypeName (Text.pack iden))
    Right ft -> PTFullReprView (fullTypeReprView ft)

viewPartTypeRepr ::
  ModuleTypes m ->
  PartTypeReprView ->
  Either FullTypeReprViewError  (Some (PartTypeRepr m))
viewPartTypeRepr mts =
  \case
    PTFullReprView vft ->
      do Some ft <- viewFullTypeRepr mts vft
         return (Some (toPartType ft))
    PTAliasReprView (TypeName nm) ->
      let iden = L.Ident (Text.unpack nm)
      in case makePartTypeRepr mts iden of
           Just spt -> Right spt
           Nothing -> Left (BadAlias iden)

$(Aeson.TH.deriveJSON Opts.structPackedRepr ''StructPackedReprView)
$(Aeson.TH.deriveJSON Opts.varArgsRepr ''VarArgsReprView)
$(Aeson.TH.deriveJSON Opts.floatInfoRepr ''FloatInfoReprView)
$(deriveMutualJSON
  [ (Opts.fullTypeRepr, ''FullTypeReprView)
  , (Opts.partTypeRepr, ''PartTypeReprView)
  ])
