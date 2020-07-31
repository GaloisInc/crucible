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
, ppMemoryError
, MemoryOp(..)
, ppMemoryOp
, MemoryErrorReason(..)
, ppMemoryErrorReason

, concMemoryError
, concMemoryOp
, concMemoryErrorReason
) where

import           Prelude hiding (pred)

import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Text.LLVM.AST as L
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.Interface
import           What4.Expr (GroundValue)

import           Lang.Crucible.LLVM.MemModel.Pointer (LLVMPtr)
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.MemLog


data MemoryOp sym w
  = MemLoadOp  StorageType (Maybe String) (LLVMPtr sym w) (Mem sym)
  | MemStoreOp StorageType (Maybe String) (LLVMPtr sym w) (Mem sym)
  | MemLoadHandleOp L.Type (Maybe String) (LLVMPtr sym w) (Mem sym)

data MemoryError sym where
  MemoryError :: (1 <= w) =>
    MemoryOp sym w ->
    MemoryErrorReason sym w ->
    MemoryError sym

-- | The kinds of type errors that arise while reading memory/constructing LLVM
-- values
data MemoryErrorReason sym w =
    TypeMismatch StorageType StorageType
  | UnexpectedArgumentType Text [StorageType]
  | ApplyViewFail ValueView
  | Invalid StorageType
  | Invalidated Text
  | NoSatisfyingWrite StorageType (LLVMPtr sym w)
  | UnwritableRegion
  | BadFunctionPointer Doc

type MemErrContext sym w = MemoryOp sym w

ppGSym :: Maybe String -> [Doc]
ppGSym Nothing = []
ppGSym (Just nm) = [ text "Global symbol", text (show nm) ]

ppMemoryOp :: IsExpr (SymExpr sym) => MemoryOp sym w -> Doc
ppMemoryOp (MemLoadOp tp gsym ptr mem)  =
  vsep [ "Performing overall load at type:" <+> ppType tp
       , indent 2 (hsep ([ text "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , text "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemStoreOp tp gsym ptr mem) =
  vsep [ "Performing store at type:" <+> ppType tp
       , indent 2 (hsep ([ text "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , text "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemLoadHandleOp sig gsym ptr mem) =
  vsep [ "Loading callable function with type:" <+> text (show sig)
       , indent 2 (hsep ([ text "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , text "In memory state:"
       , indent 2 (ppMem mem)
       ]

explain :: IsExpr (SymExpr sym) => MemoryError sym -> Doc
explain (MemoryError _mop rsn) = ppMemoryErrorReason rsn

details :: IsExpr (SymExpr sym) => MemoryError sym -> Doc
details (MemoryError mop _rsn) = ppMemoryOp mop

ppMemoryError :: IsExpr (SymExpr sym) => MemoryError sym -> Doc
ppMemoryError (MemoryError mop rsn) = ppMemoryErrorReason rsn <$$> ppMemoryOp mop

ppMemoryErrorReason :: IsExpr (SymExpr sym) => MemoryErrorReason sym w -> Doc
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
    NoSatisfyingWrite tp ptr ->
      vcat
       [ "No previous write to this location was found"
       , indent 2 ("Attempting load at type:" <+> ppType tp)
       , indent 2 ("Via pointer:" <+> ppPtr ptr)
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


concMemoryError ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemoryError sym -> IO (MemoryError sym)
concMemoryError sym conc (MemoryError mop rsn) =
  MemoryError <$> concMemoryOp sym conc mop <*> concMemoryErrorReason sym conc rsn

concMemoryOp ::
  (1 <= w, IsExprBuilder sym) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemoryOp sym w -> IO (MemoryOp sym w)
concMemoryOp sym conc (MemLoadOp tp gsym ptr mem) =
  MemLoadOp tp gsym <$> concPtr sym conc ptr <*> concMem sym conc mem
concMemoryOp sym conc (MemStoreOp tp gsym ptr mem) =
  MemStoreOp tp gsym <$> concPtr sym conc ptr <*> concMem sym conc mem
concMemoryOp sym conc (MemLoadHandleOp tp gsym ptr mem) =
  MemLoadHandleOp tp gsym <$> concPtr sym conc ptr <*> concMem sym conc mem

concMemoryErrorReason ::
  (1 <= w, IsExprBuilder sym) =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemoryErrorReason sym w -> IO (MemoryErrorReason sym w)
concMemoryErrorReason sym conc rsn = case rsn of
  TypeMismatch t1 t2 -> pure (TypeMismatch t1 t2)
  UnexpectedArgumentType msg ts -> pure (UnexpectedArgumentType msg ts)
  ApplyViewFail v -> pure (ApplyViewFail v)
  Invalid tp -> pure (Invalid tp)
  Invalidated msg -> pure (Invalidated msg)
  NoSatisfyingWrite tp ptr -> NoSatisfyingWrite tp <$> concPtr sym conc ptr
  UnwritableRegion -> pure UnwritableRegion
  BadFunctionPointer msg -> pure (BadFunctionPointer msg)
