{-
Module           : UCCrux.LLVM.View.Options.Precond
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.Precond"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.Precond
  ( preconds
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Precond.PrecondsView'.
preconds :: Aeson.Options
preconds = Idioms.recordSelectorPrefix "v" Aeson.defaultOptions
