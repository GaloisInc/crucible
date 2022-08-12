{-
Module           : UCCrux.LLVM.View.Options.Specs
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.Specs"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.Specs
  ( specPreconds
  , specSoundness
  , spec
  , specs
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Specs.SpecPrecondsView'.
specPreconds :: Aeson.Options
specPreconds = Idioms.recordSelectorPrefix "vSpec" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Specs.SpecSoundnessView'.
specSoundness :: Aeson.Options
specSoundness = Idioms.constructorSuffix "View" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Specs.SpecView'.
spec :: Aeson.Options
spec = Idioms.recordSelectorPrefix "vSpec" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Specss.SpecsView'.
specs :: Aeson.Options
specs = Aeson.defaultOptions { Aeson.unwrapUnaryRecords = True }
