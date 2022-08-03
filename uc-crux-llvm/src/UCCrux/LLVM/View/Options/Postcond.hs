{-
Module           : UCCrux.LLVM.View.Options.Postcond
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.Postcond"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.Postcond
  ( clobberValue
  , clobberArg
  , uPostcond
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Postcond.ClobberValueView'.
clobberValue :: Aeson.Options
clobberValue = Idioms.recordSelectorPrefix "vClobber" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Postcond.ClobberArgView'.
clobberArg :: Aeson.Options
clobberArg = Idioms.constructorSuffix "View" Aeson.defaultOptions

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Postcond.UPostcondView'.
uPostcond :: Aeson.Options
uPostcond = Idioms.recordSelectorPrefix "vU" Aeson.defaultOptions
