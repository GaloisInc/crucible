------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.PrettyPrint
-- Description      : Printing utilties for LLVM
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
--
-- This module defines several functions whose names clash with functions
-- offered elsewhere in @llvm-pretty@ (e.g., "Text.LLVM.PP") and in
-- @crucible-llvm@ (e.g., "Lang.Crucible.LLVM.MemModel.MemLog"). For this
-- reason, it is recommended to import this module qualified.
------------------------------------------------------------------------

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
module Lang.Crucible.LLVM.PrettyPrint
  ( commaSepList
  , ppIntType
  , ppPtrType
  , ppArrayType
  , ppVectorType
  , ppIntVector

    -- * @llvm-pretty@ printing with the latest LLVM version
  , ppLLVMLatest
  , ppDeclare
  , ppIdent
  , ppSymbol
  , ppType
  , ppValue
  ) where

import Numeric.Natural
import Prettyprinter
import qualified Text.PrettyPrint.HughesPJ as HPJ

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

-- | Print list of documents separated by commas and spaces.
commaSepList :: [Doc ann] -> Doc ann
commaSepList l = hcat (punctuate (comma <> pretty ' ') l)

-- | Pretty print int type with width.
ppIntType :: Integral a => a -> Doc ann
ppIntType i = pretty 'i' <> pretty (toInteger i)

-- | Pretty print pointer type.
ppPtrType :: Doc ann -> Doc ann
ppPtrType tp = tp <> pretty '*'

ppArrayType :: Natural -> Doc ann -> Doc ann
ppArrayType n e = brackets (pretty (toInteger n) <+> pretty 'x' <+> e)

ppVectorType :: Natural -> Doc ann -> Doc ann
ppVectorType n e = angles (pretty (toInteger n) <+> pretty 'x' <+> e)

ppIntVector :: Integral a => Natural -> a -> Doc ann
ppIntVector n w = ppVectorType n (ppIntType w)

-- | Pretty-print an LLVM-related AST in accordance with the latest LLVM version
-- that @llvm-pretty@ currently supports (i.e., the value of 'L.llvmVlatest'.)
--
-- Note that we are mainly using the @llvm-pretty@ printer in @crucible-llvm@
-- for the sake of defining 'Show' instances and creating error messages, not
-- for creating machine-readable LLVM code. As a result, it doesn't particularly
-- matter which LLVM version we use, as any version-specific differences in
-- pretty-printer output won't be that impactful.
ppLLVMLatest :: ((?config :: L.Config) => a) -> a
ppLLVMLatest = L.withConfig (L.Config { L.cfgVer = L.llvmVlatest })

-- | Invoke 'L.ppDeclare' in accordance with the latest LLVM version that
-- @llvm-pretty@ supports.
ppDeclare :: L.Declare -> HPJ.Doc
ppDeclare = ppLLVMLatest L.ppDeclare

-- | Invoke 'L.ppIdent' in accordance with the latest LLVM version that
-- @llvm-pretty@ supports.
ppIdent :: L.Ident -> HPJ.Doc
ppIdent = ppLLVMLatest L.ppIdent

-- | Invoke 'L.ppSymbol' in accordance with the latest LLVM version that
-- @llvm-pretty@ supports.
ppSymbol :: L.Symbol -> HPJ.Doc
ppSymbol = ppLLVMLatest L.ppSymbol

-- | Invoke 'L.ppType' in accordance with the latest LLVM version that
-- @llvm-pretty@ supports.
ppType :: L.Type -> HPJ.Doc
ppType = ppLLVMLatest L.ppType

-- | Invoke 'L.ppValue' in accordance with the latest LLVM version that
-- @llvm-pretty@ supports.
ppValue :: L.Value -> HPJ.Doc
ppValue = ppLLVMLatest L.ppValue
