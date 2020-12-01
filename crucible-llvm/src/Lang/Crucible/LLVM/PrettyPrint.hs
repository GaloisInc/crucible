------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.PrettyPrint
-- Description      : Printing utilties for LLVM
-- Copyright        : (c) Galois, Inc 2015-2016
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

module Lang.Crucible.LLVM.PrettyPrint
  ( commaSepList
  , ppIntType
  , ppPtrType
  , ppArrayType
  , ppVectorType
  , ppIntVector
  ) where

import Numeric.Natural
import Prettyprinter

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
