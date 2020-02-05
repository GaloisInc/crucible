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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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
  , detailBB
  , explainBB
    -- ** Lenses
  , classifier
  , predicate
  , extra
  ) where

import           Prelude hiding (pred)

import           Control.Lens
import           Data.Kind (Type)
import           Data.Text (Text)
import           Data.Maybe (isJust)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified What4.Interface as W4I
import           What4.Partial.AssertionTree

import           Data.Parameterized.Classes (toOrdering, fromOrdering)
import           Data.Parameterized.ClassesC (TestEqualityC(..), OrdC(..))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))
import qualified Data.Parameterized.TraversableF as TF

import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.LLVM.Extension.Arch (LLVMArch)
import qualified Lang.Crucible.LLVM.Extension.Safety.Poison as Poison
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB

-- -----------------------------------------------------------------------
-- ** BadBehavior

-- | Combine the three types of bad behaviors
--
data BadBehavior (e :: CrucibleType -> Type) =
    BBUndefinedBehavior (UB.UndefinedBehavior e)
  | BBPoison            (Poison.Poison e)
  | BBSafe                                  -- ^ This value is always safe
  deriving (Generic, Typeable)

-- -----------------------------------------------------------------------
-- *** Instances

$(return [])

instance TestEqualityC BadBehavior where
  testEqualityC subterms =
    $(U.structuralEquality [t|BadBehavior|]
      [ ( U.AnyType `U.TypeApp` U.DataArg 0
        , [| \x y -> if testEqualityC subterms x y
                     then Just Refl
                     else Nothing
          |]
        )
      ]
     )

instance OrdC BadBehavior where
  compareC subterms sa1 sa2 = toOrdering $
    $(U.structuralTypeOrd [t|BadBehavior|]
       [ ( U.AnyType `U.TypeApp` U.DataArg 0
         , [| \x y -> fromOrdering (compareC subterms x y) |]
         )
       ]
     ) sa1 sa2

instance FunctorF BadBehavior where
  fmapF f (BBUndefinedBehavior ub) = BBUndefinedBehavior $ fmapF f ub
  fmapF f (BBPoison p)             = BBPoison $ fmapF f p
  fmapF _ BBSafe                   = BBSafe

instance FoldableF BadBehavior where
  foldMapF = TF.foldMapFDefault

instance TraversableF BadBehavior where
  traverseF subterms=
    $(U.structuralTraversal [t|BadBehavior|]
      [ ( U.AnyType `U.TypeApp` U.DataArg 0
        , [| \_ -> traverseF subterms |]
        )
      ]
     ) subterms

-- -----------------------------------------------------------------------
-- ** LLVMSafetyAssertion

-- TODO: Consider making this an instance of What4's 'LabeledPred'
data LLVMSafetyAssertion (e :: CrucibleType -> Type) =
  LLVMSafetyAssertion
    { _classifier :: BadBehavior e -- ^ What could have gone wrong?
    , _predicate  :: e BoolType    -- ^ Is the value safe/defined?
    , _extra      :: Maybe Text    -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

type LLVMAssertionTree (arch :: LLVMArch) (e :: CrucibleType -> Type) =
  AssertionTree (e BoolType) (LLVMSafetyAssertion e)

-- -----------------------------------------------------------------------
-- *** Instances

$(return [])

instance TestEqualityC LLVMSafetyAssertion where
  testEqualityC testSubterm (LLVMSafetyAssertion cls1 pred1 ext1)
                            (LLVMSafetyAssertion cls2 pred2 ext2) =
    and [ testEqualityC testSubterm cls1 cls2
        , isJust (testSubterm pred1 pred2)
        , ext1 == ext2
        ]

instance OrdC LLVMSafetyAssertion where
  compareC subterms sa1 sa2 = toOrdering $
    $(U.structuralTypeOrd [t|LLVMSafetyAssertion|]
       [ ( U.AnyType `U.TypeApp` U.DataArg 0
         , [| \x y -> fromOrdering (compareC subterms x y) |]
         )
       , ( U.DataArg 0 `U.TypeApp` U.AnyType
         , [| subterms |]
         )
       ]
     ) sa1 sa2

instance FunctorF LLVMSafetyAssertion where
  fmapF f (LLVMSafetyAssertion cls pred ext) =
    LLVMSafetyAssertion (fmapF f cls) (f pred) ext

instance FoldableF LLVMSafetyAssertion where
  foldMapF = TF.foldMapFDefault

instance TraversableF LLVMSafetyAssertion where
  traverseF subterms=
    $(U.structuralTraversal [t|LLVMSafetyAssertion|]
      [ ( U.AnyType `U.TypeApp` U.DataArg 0
        , [| \_ -> traverseF subterms |]
        )
      , ( U.DataArg 0 `U.TypeApp` U.AnyType
        , [| \_ -> subterms |]
        )
      ]
     ) subterms

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
poison' poison_ pred expl = LLVMSafetyAssertion (BBPoison poison_) pred (Just expl)

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



explainBB :: BadBehavior e -> Doc
explainBB = \case
  BBUndefinedBehavior ub -> UB.explain ub
  BBPoison p             -> Poison.explain p
  BBSafe                 -> text "A value that's always safe"

detailBB :: W4I.IsExpr (W4I.SymExpr sym) => BadBehavior (RegValue' sym) -> Doc
detailBB = \case
  BBUndefinedBehavior ub -> UB.ppReg ub
  BBPoison p             -> Poison.ppReg p
  BBSafe                 -> text "A value that's always safe"
