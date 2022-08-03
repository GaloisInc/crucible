{-
Module           : UCCrux.LLVM.View.Options.Shape
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.Shape"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.Shape
  ( ptrShape
  , shape
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Shape.PtrShapeView'.
ptrShape :: Aeson.Options
ptrShape =
  Idioms.constructorSuffix "View" $
    Idioms.constructorPrefix "Shape" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Shape.ShapeView'.
shape :: Aeson.Options
shape =
  Idioms.constructorSuffix "View" $
    Idioms.constructorPrefix "Shape" Aeson.defaultOptions
