{-
Module           : UCCrux.LLVM.View.Options.FullType
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.FullType"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.FullType
  ( structPackedRepr
  , varArgsRepr
  , floatInfoRepr
  , fullTypeRepr
  , partTypeRepr
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.FullType.StructPackedReprView'.
structPackedRepr :: Aeson.Options
structPackedRepr = Idioms.constructorSuffix "ReprView" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.FullType.VarArgsReprView'.
varArgsRepr :: Aeson.Options
varArgsRepr = Idioms.constructorSuffix "ReprView" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.FullType.FloatInfoReprView'.
floatInfoRepr :: Aeson.Options
floatInfoRepr = Idioms.constructorSuffix "ReprView" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.FullType.FullTypeReprView'.
fullTypeRepr :: Aeson.Options
fullTypeRepr =
  Idioms.constructorSuffix "ReprView" $
    Idioms.constructorPrefix "FT" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.PartType.PartTypeReprView'.
partTypeRepr :: Aeson.Options
partTypeRepr =
  Idioms.constructorSuffix "ReprView" $
    Idioms.constructorPrefix "PT" Aeson.defaultOptions
