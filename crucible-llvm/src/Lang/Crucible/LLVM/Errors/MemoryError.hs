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
import qualified Text.LLVM.PP as L
import qualified Text.LLVM.AST as L
import           Prettyprinter

import           What4.Interface
import           What4.Expr (GroundValue)

import           Lang.Crucible.LLVM.MemModel.Pointer (LLVMPtr, concBV)
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.Type
import           Lang.Crucible.LLVM.MemModel.MemLog


data MemoryOp sym w
  = MemLoadOp  StorageType (Maybe String) (LLVMPtr sym w) (Mem sym)
  | MemStoreOp StorageType (Maybe String) (LLVMPtr sym w) (Mem sym)
  | MemStoreBytesOp (Maybe String) (LLVMPtr sym w) (Maybe (SymBV sym w)) (Mem sym)
  | forall wlen. (1 <= wlen) => MemCopyOp
       (Maybe String, LLVMPtr sym w) -- dest
       (Maybe String, LLVMPtr sym w) -- src
       (SymBV sym wlen) -- length
       (Mem sym)
  | MemLoadHandleOp L.Type (Maybe String) (LLVMPtr sym w) (Mem sym)
  | forall wlen. (1 <= wlen) => MemInvalidateOp
       Text (Maybe String) (LLVMPtr sym w) (SymBV sym wlen) (Mem sym)

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
  | UnreadableRegion
  | BadFunctionPointer (Doc ())
  | OverlappingRegions

type MemErrContext sym w = MemoryOp sym w

ppGSym :: Maybe String -> [Doc ann]
ppGSym Nothing = []
ppGSym (Just nm) = [ "Global symbol", pretty (show nm) ]

ppMemoryOp :: IsExpr (SymExpr sym) => MemoryOp sym w -> Doc ann
ppMemoryOp (MemLoadOp tp gsym ptr mem)  =
  vsep [ "Performing overall load at type:" <+> ppType tp
       , indent 2 (hsep ([ "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemStoreOp tp gsym ptr mem) =
  vsep [ "Performing store at type:" <+> ppType tp
       , indent 2 (hsep ([ "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemStoreBytesOp gsym ptr Nothing mem) =
  vsep [ "Performing byte array store for entire address space"
       , indent 2 (hsep ([ "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemStoreBytesOp gsym ptr (Just len) mem) =
  vsep [ "Performing byte array store of length:" <+> printSymExpr len
       , indent 2 (hsep ([ "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemCopyOp (gsym_dest, dest) (gsym_src, src) len mem) =
  vsep [ "Performing a memory copy of" <+> printSymExpr len <+> "bytes"
       , indent 2 (hsep ([ "Destination:" ] ++ ppGSym gsym_dest ++ [ ppPtr dest ]))
       , indent 2 (hsep ([ "Source:     " ] ++ ppGSym gsym_src ++ [ ppPtr src ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemLoadHandleOp sig gsym ptr mem) =
  vsep [ "Attempting to load callable function with type:" <+> pretty (show (L.ppType sig))
       , indent 2 (hsep ([ "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

ppMemoryOp (MemInvalidateOp msg gsym ptr len mem) =
  vsep [ "Performing explicit memory invalidation of" <+> printSymExpr len <+> "bytes"
       , pretty msg
       , indent 2 (hsep ([ "Via pointer:" ] ++ ppGSym gsym ++ [ ppPtr ptr ]))
       , "In memory state:"
       , indent 2 (ppMem mem)
       ]

explain :: IsExpr (SymExpr sym) => MemoryError sym -> Doc ann
explain (MemoryError _mop rsn) = ppMemoryErrorReason rsn

details :: IsExpr (SymExpr sym) => MemoryError sym -> Doc ann
details (MemoryError mop _rsn) = ppMemoryOp mop

ppMemoryError :: IsExpr (SymExpr sym) => MemoryError sym -> Doc ann
ppMemoryError (MemoryError mop rsn) = vcat [ppMemoryErrorReason rsn, ppMemoryOp mop]

ppMemoryErrorReason :: IsExpr (SymExpr sym) => MemoryErrorReason sym w -> Doc ann
ppMemoryErrorReason =
  \case
    TypeMismatch ty1 ty2 ->
      vcat
      [ "Type mismatch: "
      , indent 2 (vcat [ pretty (show ty1)
                       , pretty (show ty2)
                       ])
      ]
    UnexpectedArgumentType txt vals ->
      vcat
      [ "Unexpected argument type:"
      , pretty txt
      , indent 2 (vcat (map (pretty . show) vals))
      ]
    ApplyViewFail vw ->
      "Failure when applying value view" <+> pretty (show vw)
    Invalid ty ->
      "Load from invalid memory at type " <+> pretty (show ty)
    Invalidated msg ->
      "Load from explicitly invalidated memory:" <+> pretty msg
    NoSatisfyingWrite tp ptr ->
      vcat
       [ "No previous write to this location was found"
       , indent 2 ("Attempting load at type:" <+> ppType tp)
       , indent 2 ("Via pointer:" <+> ppPtr ptr)
       ]
    UnwritableRegion ->
      "The region wasn't allocated, wasn't large enough, or was marked as readonly"
    UnreadableRegion ->
      "The region wasn't allocated or wasn't large enough"
    BadFunctionPointer msg ->
      vcat
       [ "The given pointer could not be resolved to a callable function"
       , unAnnotate msg
       ]
    OverlappingRegions ->
      "Memory regions required to be disjoint"

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
concMemoryOp sym conc (MemStoreBytesOp gsym ptr len mem) =
  MemStoreBytesOp gsym <$>
    concPtr sym conc ptr <*>
    traverse (concBV sym conc) len <*>
    concMem sym conc mem
concMemoryOp sym conc (MemLoadHandleOp tp gsym ptr mem) =
  MemLoadHandleOp tp gsym <$> concPtr sym conc ptr <*> concMem sym conc mem
concMemoryOp sym conc (MemCopyOp (gsym_dest, dest) (gsym_src, src) len mem) =
  do dest' <- concPtr sym conc dest
     src'  <- concPtr sym conc src
     len'  <- concBV sym conc len
     mem'  <- concMem sym conc mem
     pure (MemCopyOp (gsym_dest, dest') (gsym_src, src') len' mem')
concMemoryOp sym conc (MemInvalidateOp msg gsym ptr len mem) =
  MemInvalidateOp msg gsym <$>
    concPtr sym conc ptr <*>
    concBV sym conc len <*>
    concMem sym conc mem

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
  UnreadableRegion -> pure UnreadableRegion
  BadFunctionPointer msg -> pure (BadFunctionPointer msg)
  OverlappingRegions -> pure OverlappingRegions
