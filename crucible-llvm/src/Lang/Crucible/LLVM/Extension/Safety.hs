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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Extension.Safety
  ( LLVMSafetyAssertion
  , BadBehavior(..)
  , LLVMAssertionTree
  , undefinedBehavior
  , undefinedBehavior'
  , poison
  , poison'
  , safe
    -- ** Lenses
  , classifier
  , predicate
  , extra
  ) where

import           Prelude hiding (pred)

import           Control.Lens
import           Data.Kind (Type)
import           Data.Text (Text)
import           Data.Type.Equality (TestEquality(..))
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)

import qualified What4.Interface as W4I
import           What4.Partial

import           Data.Parameterized.Classes (EqF(..))
import           Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))

import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.LLVM.Extension.Arch (LLVMArch)
import qualified Lang.Crucible.LLVM.Extension.Safety.Poison as Poison
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB

type LLVMAssertionTree (arch :: LLVMArch) (e :: CrucibleType -> Type) =
  AssertionTree (e BoolType) (LLVMSafetyAssertion e)

-- | Combine the three types of bad behaviors
--
-- TODO(langston): should there just be a 'BadBehavior' class?
data BadBehavior (e :: CrucibleType -> Type) =
    BBUndefinedBehavior (UB.UndefinedBehavior e)
  | BBPoison            (Poison.Poison e)
  -- | BBUndef             (UV.UndefValue e)
  | BBSafe                                  -- ^ This value is always safe
  deriving (Generic, Typeable)

instance TestEqualityC BadBehavior where
  testEqualityC subterms (BBUndefinedBehavior ub1) (BBUndefinedBehavior ub2) =
    testEqualityC subterms ub1 ub2
  testEqualityC subterms (BBPoison p1) (BBPoison p2) =
    testEqualityC subterms p1 p2
  testEqualityC subterms BBSafe BBSafe = True

data LLVMSafetyAssertion (e :: CrucibleType -> Type) =
  LLVMSafetyAssertion
    { _classifier :: BadBehavior e -- ^ What could have gone wrong?
    , _predicate  :: e BoolType    -- ^ Is the value safe/defined?
    , _extra      :: Maybe Text    -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

$(return [])

-- instance TestEqualityC (LLVMSafetyAssertion) where
--   testEqualityC testSubterm = _
--     $(U.structuralTypeEquality [t|LLVMSafetyAssertion|]
--         [ ( U.ConType [t|BadBehavior|] `U.TypeApp` U.AnyType
--           , [|testEqualityC testSubterm|]
--           )
--         ]
--      )

instance TestEqualityC LLVMSafetyAssertion where
  testEqualityC subterms sa1 sa2 = undefined

instance OrdC LLVMSafetyAssertion where
  compareC subterms sa1 sa2 = undefined

instance FunctorF LLVMSafetyAssertion where
  fmapF _ _ = undefined

instance FoldableF LLVMSafetyAssertion where
  foldMapF _ _ = undefined

instance TraversableF LLVMSafetyAssertion where
  traverseF _ _ = undefined

-- -----------------------------------------------------------------------
-- ** Constructors

-- We expose these rather than the constructors to retain the freedom to
-- change the internal representation.

undefinedBehavior' :: UB.UndefinedBehavior e
                   -> e BoolType
                   -> Text
                   -> LLVMSafetyAssertion e
undefinedBehavior' ub pred expl =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred (Just expl)

undefinedBehavior :: UB.UndefinedBehavior e
                  -> e BoolType
                  -> LLVMSafetyAssertion e
undefinedBehavior ub pred =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred Nothing


poison' :: Poison.Poison e
        -> e BoolType
        -> Text
        -> LLVMSafetyAssertion e
poison' poison pred expl = LLVMSafetyAssertion (BBPoison poison) pred (Just expl)

poison :: Poison.Poison e
       -> e BoolType
       -> LLVMSafetyAssertion e
poison ub pred = LLVMSafetyAssertion (BBPoison ub) pred Nothing

-- undefinedBehavior' :: UB.UndefinedBehavior (W4I.SymExpr sym)
--                    -> proxy sym -- ^ Unused, resolves ambiguous types
--                    -> Pred sym
--                    -> Text
--                    -> LLVMSafetyAssertion (W4I.SymExpr sym)
-- undefinedBehavior' _proxySym ub pred expl =
--   LLVMSafetyAssertion (BBUndefinedBehavior ub) pred (Just expl)

-- undefinedBehavior :: UB.UndefinedBehavior (W4I.SymExpr sym)
--                    -> proxy sym -- ^ Unused, resolves ambiguous types
--                   -> Pred sym
--                   -> LLVMSafetyAssertion (W4I.SymExpr sym)
-- undefinedBehavior _proxySym ub pred =
--   LLVMSafetyAssertion (BBUndefinedBehavior ub) pred Nothing


-- poison' :: Poison.Poison (W4I.SymExpr sym)
--         -> proxy sym  -- ^ Unused, resolves ambiguous types
--         -> Pred sym
--         -> Text
--         -> LLVMSafetyAssertion (W4I.SymExpr sym)
-- poison' _proxySym poison pred expl = LLVMSafetyAssertion (BBPoison poison) pred (Just expl)

-- poison :: Poison.Poison (W4I.SymExpr sym)
--        -> proxy sym  -- ^ Unused, resolves ambiguous types
--        -> Pred sym
--        -> LLVMSafetyAssertion (W4I.SymExpr sym)
-- poison _proxySym ub pred = LLVMSafetyAssertion (BBPoison ub) pred Nothing

-- | For values that are always safe, but are expected to be paired with safety
-- assertions.
safe :: W4I.IsExprBuilder sym => sym -> LLVMSafetyAssertion (RegValue' sym)
safe sym = LLVMSafetyAssertion BBSafe (RV (W4I.truePred sym)) (Just "always safe")

-- -----------------------------------------------------------------------
-- ** Lenses

classifier :: Simple Lens (LLVMSafetyAssertion e) (BadBehavior e)
classifier = lens _classifier (\s v -> s { _classifier = v})

predicate :: Simple Lens (LLVMSafetyAssertion e) (e BoolType)
predicate = lens _predicate (\s v -> s { _predicate = v})

extra :: Simple Lens (LLVMSafetyAssertion e) (Maybe Text)
extra = lens _extra (\s v -> s { _extra = v})
