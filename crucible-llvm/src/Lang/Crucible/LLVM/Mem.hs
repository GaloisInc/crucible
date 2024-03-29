-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Mem
-- Description      : TODO
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : langston@galois.com
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Lang.Crucible.LLVM.Mem
  ( Mem
  , MemData
  ) where

import Data.Kind (Type)

import Lang.Crucible.Types (CrucibleType)

import qualified Lang.Crucible.LLVM.MemModel.Generic as G
import qualified Lang.Crucible.LLVM.Types as T

-- TODO: Move me!
class Mem (mem :: CrucibleType) where
  type MemData (mem :: CrucibleType) sym = (r :: Type) | r -> mem

instance Mem T.Mem where
  type MemData T.Mem sym = G.Mem sym
