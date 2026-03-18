{-# LANGUAGE TypeFamilies #-}

module Mir.Intrinsics.Syntax where

import Lang.Crucible.CFG.Extension (EmptyExprExtension, ExprExtension)

-- | Sigil type indicating the MIR syntax extension
data MIR

type instance ExprExtension MIR = EmptyExprExtension
