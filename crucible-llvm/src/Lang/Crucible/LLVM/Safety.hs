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
  , LLVMAssertionTree
  , undefinedBehavior
  , undefinedBehavior'
  , poison
  , poison'
  , safe
  ) where

import           Data.Kind (Type)
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
-- TODO(langston): parameterize on kind :: BaseType -> Type
data BadBehavior e =
    BBUndefinedBehavior (UB.UndefinedBehavior e)
  | BBPoison            (Poison.Poison e)
  -- | BBUndef             (UV.UndefValue e)
  | BBSafe                                  -- ^ This value is always safe
  deriving (Generic, Typeable)

data LLVMSafetyAssertion (arch :: LLVMArch) (e :: W4I.BaseType -> Type) =
  LLVMSafetyAssertion
    { _classifier :: BadBehavior e      -- ^ What could have gone wrong?
    , _predicate  :: e W4I.BaseBoolType -- ^ Is the value safe/defined?
    , _extra      :: Maybe Text         -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

type LLVMAssertionTree (arch :: LLVMArch) (e :: W4I.BaseType -> Type) =
  AssertionTree (e W4I.BaseBoolType) (LLVMSafetyAssertion arch e)

-- -----------------------------------------------------------------------
-- ** Constructors

-- We expose these rather than the constructors to retain the freedom to
-- change the internal representation.

undefinedBehavior' :: UB.UndefinedBehavior e
                   -> e W4I.BaseBoolType
                   -> Text
                   -> LLVMSafetyAssertion arch e
undefinedBehavior' ub pred expl =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred (Just expl)

undefinedBehavior :: UB.UndefinedBehavior e
                  -> e W4I.BaseBoolType
                  -> LLVMSafetyAssertion arch e
undefinedBehavior ub pred =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred Nothing


poison' :: Poison.Poison e
        -> e W4I.BaseBoolType
        -> Text
        -> LLVMSafetyAssertion arch e
poison' poison pred expl = LLVMSafetyAssertion (BBPoison poison) pred (Just expl)

poison :: Poison.Poison e
       -> e W4I.BaseBoolType
       -> LLVMSafetyAssertion arch e
poison ub pred = LLVMSafetyAssertion (BBPoison ub) pred Nothing

-- undefinedBehavior' :: UB.UndefinedBehavior (W4I.SymExpr sym)
--                    -> proxy sym -- ^ Unused, resolves ambiguous types
--                    -> Pred sym
--                    -> Text
--                    -> LLVMSafetyAssertion arch (W4I.SymExpr sym)
-- undefinedBehavior' _proxySym ub pred expl =
--   LLVMSafetyAssertion (BBUndefinedBehavior ub) pred (Just expl)

-- undefinedBehavior :: UB.UndefinedBehavior (W4I.SymExpr sym)
--                    -> proxy sym -- ^ Unused, resolves ambiguous types
--                   -> Pred sym
--                   -> LLVMSafetyAssertion arch (W4I.SymExpr sym)
-- undefinedBehavior _proxySym ub pred =
--   LLVMSafetyAssertion (BBUndefinedBehavior ub) pred Nothing


-- poison' :: Poison.Poison (W4I.SymExpr sym)
--         -> proxy sym  -- ^ Unused, resolves ambiguous types
--         -> Pred sym
--         -> Text
--         -> LLVMSafetyAssertion arch (W4I.SymExpr sym)
-- poison' _proxySym poison pred expl = LLVMSafetyAssertion (BBPoison poison) pred (Just expl)

-- poison :: Poison.Poison (W4I.SymExpr sym)
--        -> proxy sym  -- ^ Unused, resolves ambiguous types
--        -> Pred sym
--        -> LLVMSafetyAssertion arch (W4I.SymExpr sym)
-- poison _proxySym ub pred = LLVMSafetyAssertion (BBPoison ub) pred Nothing

-- | For values that are always safe, but are expected to be paired with safety
-- assertions.
safe :: W4I.IsExprBuilder sym => sym -> LLVMSafetyAssertion arch (W4I.SymExpr sym)
safe sym = LLVMSafetyAssertion BBSafe (W4I.truePred sym) (Just "always safe")

-- -----------------------------------------------------------------------
-- ** Lenses

classifier :: Simple Lens (LLVMSafetyAssertion arch e) (BadBehavior e)
classifier = lens _classifier (\s v -> s { _classifier = v})

predicate :: Simple Lens (LLVMSafetyAssertion arch e) (e W4I.BaseBoolType)
predicate = lens _predicate (\s v -> s { _predicate = v})

extra :: Simple Lens (LLVMSafetyAssertion arch e) (Maybe Text)
extra = lens _extra (\s v -> s { _extra = v})

-- -----------------------------------------------------------------------
-- ** HasSafetyAssertions

type instance SafetyAssertion (LLVM arch) (e :: W4I.BaseType -> Type) =
  LLVMSafetyAssertion arch e

-- instance HasSafetyAssertions (LLVM arch) sym where
--   toPredicate sym = view predicate
    -- \case
    --   SAUndefinedBehavior p ->
