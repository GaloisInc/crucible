-- |
-- Module           : Lang.Crucible.LLVM.Safety
-- Description      : Safety assertions for the LLVM syntax extension
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
--------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Safety
  ( LLVMSafetyAssertion(..)
  ) where

import           Data.Data (Data)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic, Generic1)

import           Data.Text (Text)

import           Lang.Crucible.CFG.Extension.Safety
import           Lang.Crucible.LLVM.Extension
import           What4.Partial
import qualified What4.Interface as W4I
import           What4.Interface (Pred, IsExprBuilder)

import qualified Lang.Crucible.LLVM.Safety.UndefinedBehavior as UB
import qualified Lang.Crucible.LLVM.Safety.Poison as Poison
-- import qualified Lang.Crucible.LLVM.MemModel.Value as Value
import           Lang.Crucible.LLVM.MemModel.Value (LLVMVal(..), PartLLVMVal)

type instance SafetyAssertion (LLVM arch) sym = LLVMSafetyAssertion arch sym

-- | Combine the three types of bad behaviors
data BadBehavior sym =
    BBUndefinedBehavior (UB.UndefinedBehavior sym)
  | BBPoison            (Poison.Poison sym)
  -- | LLVM @undef@ values.
  | BBUndef             Text -- TODO(langston) Needs a module like @Poison@ and @UB@.
  deriving (Generic, Typeable)

-- | TODO: `undef` values?
data LLVMSafetyAssertion (arch :: LLVMArch) sym =
  LLVMSafetyAssertion
    { _clasifier :: BadBehavior sym -- ^ What could have gone wrong?
    , _predicate :: Pred sym        -- ^ Did it actually occur?
    , _extra     :: Text            -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

type PartLLVMVal arch sym =
  PartExpr (AssertionTree (LLVMSafetyAssertion arch sym)) (LLVMVal sym)

instance HasSafetyAssertions (LLVM arch) sym where
  toPredicate sym = _
    -- \case
    --   SAUndefinedBehavior p -> 
