{-
Module           : UCCrux.LLVM.View.Options.Cursor
Description      : 'Aeson.Options' used in "UCCrux.LLVM.View.Cursor"
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

This module is intended to be imported qualified as \"Opts\".
-}

module UCCrux.LLVM.View.Options.Cursor
  ( cursor
  )
where

import qualified Data.Aeson as Aeson

import qualified UCCrux.LLVM.View.Options.Idioms as Idioms

-- | Options used to derive JSON instances for
-- 'UCCrux.LLVM.View.Cursor.CursorView'.
cursor :: Aeson.Options
cursor = Idioms.constructorSuffix "View" Aeson.defaultOptions
