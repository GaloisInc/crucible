{-
Module           : UCCrux.LLVM.FullType.PP
Description      : Pretty-printing 'FullTypeRepr'
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

module UCCrux.LLVM.FullType.PP
  ( ppFullTypeRepr,
    ppPartTypeRepr
  )
where

import           Prettyprinter (Doc)

import           Lang.Crucible.LLVM.MemType (ppMemType, ppSymType)

import           UCCrux.LLVM.FullType.MemType (toMemType, toSymType)
import           UCCrux.LLVM.FullType.Type (FullTypeRepr, PartTypeRepr)

ppFullTypeRepr :: FullTypeRepr m ft -> Doc ann
ppFullTypeRepr = ppMemType . toMemType

ppPartTypeRepr :: PartTypeRepr m ft -> Doc ann
ppPartTypeRepr = ppSymType . toSymType
