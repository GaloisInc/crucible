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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Safety
  ( LLVMSafetyAssertion
  , undefinedBehavior
  , undefinedBehavior'
  , poison
  , poison'
  , safe
  ) where

import           Data.Data (Data)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic, Generic1)

import           Control.Lens
import           Data.Text (Text)

import           Lang.Crucible.CFG.Extension.Safety
import           Lang.Crucible.LLVM.Extension
import           What4.Partial
import qualified What4.Interface as W4I
import           What4.Interface (Pred, IsExprBuilder)

import qualified Lang.Crucible.LLVM.Safety.Poison as Poison
import qualified Lang.Crucible.LLVM.Safety.UndefValue as UV
import qualified Lang.Crucible.LLVM.Safety.UndefinedBehavior as UB
-- import qualified Lang.Crucible.LLVM.MemModel.Value as Value
import           Lang.Crucible.LLVM.MemModel.Value (LLVMVal(..))

-- | Combine the three types of bad behaviors
--
-- TODO(langston): should there just be a 'BadBehavior' class?
data BadBehavior sym =
    BBUndefinedBehavior (UB.UndefinedBehavior sym)
  | BBPoison            (Poison.Poison sym)
  | BBUndef             (UV.UndefValue sym)
  | BBSafe                                  -- ^ This value is always safe
  deriving (Generic, Typeable)

data LLVMSafetyAssertion (arch :: LLVMArch) sym =
  LLVMSafetyAssertion
    { _classifier :: BadBehavior sym -- ^ What could have gone wrong?
    , _predicate  :: Pred sym        -- ^ Is the value safe/defined?
    , _extra      :: Maybe Text      -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

-- -----------------------------------------------------------------------
-- ** Constructors

-- We expose these rather than the constructors to retain the freedom to
-- change the internal representation.

undefinedBehavior' :: UB.UndefinedBehavior sym
                   -> Pred sym
                   -> Text
                   -> LLVMSafetyAssertion arch sym
undefinedBehavior' ub pred expl =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred (Just expl)

undefinedBehavior :: UB.UndefinedBehavior sym
                  -> Pred sym
                  -> LLVMSafetyAssertion arch sym
undefinedBehavior ub pred =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred Nothing


poison' :: Poison.Poison sym
        -> Pred sym
        -> Text
        -> LLVMSafetyAssertion arch sym
poison' poison pred expl = LLVMSafetyAssertion (BBPoison poison) pred (Just expl)

poison :: Poison.Poison sym
       -> Pred sym
       -> LLVMSafetyAssertion arch sym
poison ub pred = LLVMSafetyAssertion (BBPoison ub) pred Nothing

-- | For values that are always safe, but are expected to be paired with safety
-- assertions.
safe :: W4I.IsExprBuilder sym => sym -> LLVMSafetyAssertion arch sym
safe sym = LLVMSafetyAssertion BBSafe (W4I.truePred sym) (Just "always safe")

-- -----------------------------------------------------------------------
-- ** Lenses

classifier :: Simple Lens (LLVMSafetyAssertion arch sym) (BadBehavior sym)
classifier = lens _classifier (\s v -> s { _classifier = v})

predicate :: Simple Lens (LLVMSafetyAssertion arch sym) (Pred sym)
predicate = lens _predicate (\s v -> s { _predicate = v})

extra :: Simple Lens (LLVMSafetyAssertion arch sym) (Maybe Text)
extra = lens _extra (\s v -> s { _extra = v})

-- -----------------------------------------------------------------------
-- ** HasSafetyAssertions

type instance SafetyAssertion (LLVM arch) sym = LLVMSafetyAssertion arch sym

instance HasSafetyAssertions (LLVM arch) sym where
  toPredicate sym = view predicate
    -- \case
    --   SAUndefinedBehavior p ->
