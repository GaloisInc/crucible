{-
Module           : UCCrux.LLVM.View.Options.Constraint
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.Constraint"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.Constraint
  ( constraint
  , constrainedShape
  , constrainedTypedValue
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Constraint.ConstraintView'.
constraint :: Aeson.Options
constraint = Idioms.constructorSuffix "View" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Constraint.ConstrainedShapeView'.
constrainedShape :: Aeson.Options
constrainedShape = Aeson.defaultOptions { Aeson.unwrapUnaryRecords = True }

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Constraint.ConstrainedTypedValue'.
constrainedTypedValue :: Aeson.Options
constrainedTypedValue =
  Idioms.recordSelectorPrefix "vConstrained" Aeson.defaultOptions
