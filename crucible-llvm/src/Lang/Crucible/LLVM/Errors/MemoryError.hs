-- |
-- Module           : Lang.Crucible.LLVM.Errors.MemoryError
-- Description      : Errors that arise when reading and writing memory
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
--------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.LLVM.Errors.MemoryError
( MemoryError(..)
, MemErrContext
, explain
, details
, ppME
, concMemoryError
, MemoryErrorReason(..)
, ppMemoryErrorReason
) where

import           Prelude hiding (pred)

import           Data.Text (Text)
import qualified Data.Text as Text

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.Interface
import           What4.Expr (GroundValue)

import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment)
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.Pointer (LLVMPtr)
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.MemLog


data MemoryError sym where
  MemoryError :: (1 <= w) =>
    Maybe String ->
    LLVMPtr sym w ->
    Mem sym ->
    MemoryErrorReason ->
    MemoryError sym

type MemErrContext sym w = (Maybe String, LLVMPtr sym w, Mem sym)

ppGSym :: Maybe String -> [Doc]
ppGSym Nothing = []
ppGSym (Just nm) = [ text "Global symbol", text (show nm) ]

explain :: MemoryError sym -> Doc
explain (MemoryError _ _ _ rsn) = ppMemoryErrorReason rsn

details :: IsExpr (SymExpr sym) => MemoryError sym -> Doc
details (MemoryError gsym p mem _rsn) =
    vcat
       [ hsep ([ text "Via pointer:" ] ++ ppGSym gsym ++ [UB.ppPointerPair (UB.pointerView p) ])
       , text "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppME :: IsExpr (SymExpr sym) => MemoryError sym -> Doc
ppME (MemoryError gsym p mem rsn) =
    vcat
       [ hsep ([ text "Via pointer:" ] ++ ppGSym gsym ++ [UB.ppPointerPair (UB.pointerView p) ])
       , ppMemoryErrorReason rsn
       , text "In memory state:"
       , indent 2 (ppMem mem)
       ]

concMemoryError ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemoryError sym -> IO (MemoryError sym)
concMemoryError sym conc (MemoryError gsym ptr mem rsn) =
  MemoryError gsym <$> concPtr sym conc ptr <*> concMem sym conc mem <*> pure rsn

------------------------------------------------------------------------
-- ** MemoryErrorReason

-- | The kinds of type errors that arise while reading memory/constructing LLVM
-- values
data MemoryErrorReason =
    TypeMismatch StorageType StorageType
  | UnexpectedArgumentType Text [StorageType]
  | ApplyViewFail ValueView
  | Invalid StorageType
  | Invalidated Text
  | NoSatisfyingWrite [Doc]
  | UnalignedPointer Alignment
  | UnwritableRegion
  | BadFunctionPointer Doc

instance Pretty MemoryErrorReason where
  pretty = ppMemoryErrorReason

instance Show MemoryErrorReason where
  show = show . ppMemoryErrorReason

ppMemoryErrorReason :: MemoryErrorReason -> Doc
ppMemoryErrorReason =
  \case
    TypeMismatch ty1 ty2 ->
      "Type mismatch: "
      <$$> indent 2 (vcat [ text (show ty1)
                          , text (show ty2)
                          ])
    UnexpectedArgumentType txt vals ->
      vcat [ "Unexpected argument type:"
           , text (Text.unpack txt)
           ]
      <$$> indent 2 (vcat (map (text . show) vals))
    ApplyViewFail vw ->
      "Failure when applying value view" <+> text (show vw)
    Invalid ty ->
      "Load from invalid memory at type " <+> text (show ty)
    Invalidated msg ->
      "Load from explicitly invalidated memory:" <+> text (Text.unpack msg)
    NoSatisfyingWrite [] ->
      "No previous write to this location was found"
    NoSatisfyingWrite doc ->
      vcat
       [ "No previous write to this location was found"
       , indent 2 (vcat doc)
       ]
    UnalignedPointer a ->
      vcat
       [ "Pointer not sufficently aligned"
       , "Required alignment:" <+> text (show (fromAlignment a)) <+> "bytes"
       ]
    UnwritableRegion ->
      vcat
       [ "The region wasn't allocated, or was marked as readonly"
       ]

    BadFunctionPointer msg ->
      vcat
       [ "The given pointer could not be resolved to a callable function"
       , msg
       ]
