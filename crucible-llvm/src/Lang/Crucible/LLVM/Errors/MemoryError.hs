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
, memOpMem
, ppMemoryOp
, MemoryErrorReason(..)
, ppMemoryErrorReason
, FuncLookupError(..)
, ppFuncLookupError

, concMemoryError
, concMemoryOp
) where

import           Prelude hiding (pred)

import           Data.Text (Text)
import qualified Text.LLVM.PP as L
import qualified Text.LLVM.AST as L
import           Type.Reflection (SomeTypeRep(SomeTypeRep))
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
  | MemLoadHandleOp (Maybe L.Type) (Maybe String) (LLVMPtr sym w) (Mem sym)
  | forall wlen. (1 <= wlen) => MemInvalidateOp
       Text (Maybe String) (LLVMPtr sym w) (SymBV sym wlen) (Mem sym)

memOpMem :: MemoryOp sym w -> Mem sym
memOpMem =
  \case
    MemLoadOp _ _ _ mem -> mem
    MemStoreOp _ _ _ mem -> mem
    MemStoreBytesOp _ _ _ mem -> mem
    MemCopyOp _ _ _ mem -> mem
    MemLoadHandleOp _ _ _ mem -> mem
    MemInvalidateOp _ _ _ _ mem -> mem

data MemoryError sym where
  MemoryError :: (1 <= w) =>
    MemoryOp sym w ->
    MemoryErrorReason ->
    MemoryError sym

-- | The kinds of type errors that arise while reading memory/constructing LLVM
-- values
data MemoryErrorReason =
    TypeMismatch StorageType StorageType
  | UnexpectedArgumentType Text [StorageType]
  | ApplyViewFail ValueView
  | Invalid StorageType
  | Invalidated Text
  | NoSatisfyingWrite StorageType
  | UnwritableRegion
  | UnreadableRegion
  | BadFunctionPointer FuncLookupError
  | OverlappingRegions
  deriving (Eq, Ord)

-- | Reasons that looking up a function handle associated with an LLVM pointer
-- may fail
data FuncLookupError
  = SymbolicPointer
  | RawBitvector
  | NoOverride
  | Uncallable SomeTypeRep
  deriving (Eq, Ord)

ppFuncLookupError :: FuncLookupError -> Doc ann
ppFuncLookupError =
  \case
    SymbolicPointer -> "Cannot resolve a symbolic pointer to a function handle"
    RawBitvector -> "Cannot treat raw bitvector as function pointer"
    NoOverride -> "No implementation or override found for pointer"
    Uncallable (SomeTypeRep typeRep) ->
      vsep [ "Data associated with the pointer found, but was not a callable function:"
           , hang 2 (viaShow typeRep)
           ]

type MemErrContext sym w = MemoryOp sym w

ppGSym :: Maybe String -> [Doc ann]
ppGSym Nothing = []
ppGSym (Just nm) = [ "Global symbol", viaShow nm ]

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
  vsep [ case sig of
           Just s ->
             hsep ["Attempting to load callable function with type:", viaShow (L.ppType s)]
           Nothing ->
             hsep ["Attempting to load callable function:"]
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

ppMemoryErrorReason :: MemoryErrorReason -> Doc ann
ppMemoryErrorReason =
  \case
    TypeMismatch ty1 ty2 ->
      vcat
      [ "Type mismatch: "
      , indent 2 (vcat [ ppType ty1
                       , ppType ty2
                       ])
      ]
    UnexpectedArgumentType txt vals ->
      vcat
      [ "Unexpected argument type:"
      , pretty txt
      , indent 2 (vcat (map viaShow vals))
      ]
    ApplyViewFail vw ->
      "Failure when applying value view" <+> viaShow vw
    Invalid ty ->
      "Load from invalid memory at type" <+> ppType ty
    Invalidated msg ->
      "Load from explicitly invalidated memory:" <+> pretty msg
    NoSatisfyingWrite tp ->
      vcat
       [ "No previous write to this location was found"
       , indent 2 ("Attempting load at type:" <+> ppType tp)
       ]
    UnwritableRegion ->
      "The region wasn't allocated, wasn't large enough, or was marked as readonly"
    UnreadableRegion ->
      "The region wasn't allocated or wasn't large enough"
    BadFunctionPointer err ->
      vcat
       [ "The given pointer could not be resolved to a callable function"
       , ppFuncLookupError err
       ]
    OverlappingRegions ->
      "Memory regions required to be disjoint"

concMemoryError ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  MemoryError sym -> IO (MemoryError sym)
concMemoryError sym conc (MemoryError mop rsn) =
  MemoryError <$> concMemoryOp sym conc mop <*> pure rsn

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
