{-
Module           : UCCrux.LLVM.FullType.PP
Description      : Pretty-printing 'FullTypeRepr'
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

These functions are in their own module (instead of in
"UCCrux.LLVM.FullType.PP.Type") to ensure only a small amount of code has access
to the constructors of 'PartTypeRepr', which can be used to violate its
invariant.
-}

module UCCrux.LLVM.FullType.PP
  ( ppFullTypeRepr,
    ppPartTypeRepr
  )
where

import           Prettyprinter (Doc)

import           Lang.Crucible.LLVM.MemType (ppMemType, ppSymType)

import           UCCrux.LLVM.FullType.MemType (toMemType, toSymType)
import           UCCrux.LLVM.FullType.Type (DataLayout, FullTypeRepr, PartTypeRepr)

ppFullTypeRepr :: DataLayout m -> FullTypeRepr m ft -> Doc ann
ppFullTypeRepr dl = ppMemType . toMemType dl

ppPartTypeRepr :: DataLayout m -> PartTypeRepr m ft -> Doc ann
ppPartTypeRepr dl = ppSymType . toSymType dl
