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
import Text.PrettyPrint.ANSI.Leijen

-- | Print list of documents separated by commas and spaces.
commaSepList :: [Doc] -> Doc
commaSepList l = hcat (punctuate (comma <> char ' ') l)

-- | Pretty print int type with width.
ppIntType :: Integral a => a -> Doc
ppIntType i = char 'i' <> integer (toInteger i)

-- | Pretty print pointer type.
ppPtrType :: Doc -> Doc
ppPtrType tp = tp <> char '*'

ppArrayType :: Natural -> Doc -> Doc
ppArrayType n e = brackets (integer (toInteger n) <+> char 'x' <+> e)

ppVectorType :: Natural -> Doc -> Doc
ppVectorType n e = angles (integer (toInteger n) <+> char 'x' <+> e)

ppIntVector :: Integral a => Natural -> a -> Doc
ppIntVector n w = ppVectorType n (ppIntType w)
