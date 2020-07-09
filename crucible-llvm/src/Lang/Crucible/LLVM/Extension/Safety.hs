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
  , MemoryError(..)
  , ppMemoryError
  , undefinedBehavior
  , undefinedBehavior'
  , poison
  , poison'
  , memoryError
  , detailBB
  , explainBB
    -- ** Lenses
  , classifier
  , predicate
  , extra
  ) where

import           Prelude hiding (pred)

import           Control.Lens
--import           Data.Kind (Type)
import           Data.Text (Text)
import qualified Data.Text as Text

import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.Interface

--import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import           Lang.Crucible.LLVM.DataLayout (Alignment, fromAlignment)
import qualified Lang.Crucible.LLVM.Extension.Safety.Poison as Poison
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.Pointer (LLVMPtr)
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.Type


------------------------------------------------------------------------
-- ** MemoryLoadError

-- | The kinds of type errors that arise while reading memory/constructing LLVM
-- values
data MemoryError =
    TypeMismatch StorageType StorageType
  | UnexpectedArgumentType Text [StorageType]
  | ApplyViewFail ValueView
  | Invalid StorageType
  | Invalidated Text
  | NoSatisfyingWrite [Doc]
  | UnalignedPointer Alignment
  | UnwritableRegion
  deriving (Generic)

instance Pretty MemoryError where
  pretty = ppMemoryError

instance Show MemoryError where
  show = show . ppMemoryError

ppMemoryError :: MemoryError -> Doc
ppMemoryError =
  \case
    TypeMismatch ty1 ty2 ->
      "Type mismatch: "
      <$$> indent 2 (vcat [ text (show ty1)
                          , text (show ty2)
                          ])
    UnexpectedArgumentType txt vals ->
      vcat [ "Unexpected argument type:"
           , text (Text.unpack txt)
           ]
      <$$> indent 2 (vcat (map (text . show) vals))
    ApplyViewFail vw ->
      "Failure when applying value view" <+> text (show vw)
    Invalid ty ->
      "Load from invalid memory at type " <+> text (show ty)
    Invalidated msg ->
      "Load from explicitly invalidated memory:" <+> text (Text.unpack msg)
    NoSatisfyingWrite [] ->
      "No previous write to this location was found"
    NoSatisfyingWrite doc ->
      vcat
       [ "No previous write to this location was found"
       , indent 2 (vcat doc)
       ]
    UnalignedPointer a ->
      vcat
       [ "Pointer not sufficently aligned."
       , "Required alignment:" <+> text (show (fromAlignment a)) <+> "bytes."
       ]
    UnwritableRegion ->
      vcat
       [ "The region wasn't allocated, or was marked as readonly"
       ]


-- -----------------------------------------------------------------------
-- ** BadBehavior

-- | Combine the three types of bad behaviors
--
data BadBehavior sym where
  BBUndefinedBehavior :: UB.UndefinedBehavior (RegValue' sym) -> BadBehavior sym
  BBMemoryError ::
    LLVMPtr sym w ->
    MemoryError ->
    BadBehavior sym
 deriving Typeable

-- -----------------------------------------------------------------------
-- *** Instances

$(return [])

-- -----------------------------------------------------------------------
-- ** LLVMSafetyAssertion

data LLVMSafetyAssertion sym =
  LLVMSafetyAssertion
    { _classifier :: BadBehavior sym -- ^ What could have gone wrong?
    , _predicate  :: Pred sym        -- ^ Is the value safe/defined?
    , _extra      :: Maybe Text      -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

-- -----------------------------------------------------------------------
-- *** Instances

$(return [])

-- -----------------------------------------------------------------------
-- ** Constructors

-- We expose these rather than the constructors to retain the freedom to
-- change the internal representation.

undefinedBehavior' :: UB.UndefinedBehavior (RegValue' sym)
                   -> Pred sym
                   -> Text
                   -> LLVMSafetyAssertion sym
undefinedBehavior' ub pred expl =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred (Just expl)

undefinedBehavior :: UB.UndefinedBehavior (RegValue' sym)
                  -> Pred sym
                  -> LLVMSafetyAssertion sym
undefinedBehavior ub pred =
  LLVMSafetyAssertion (BBUndefinedBehavior ub) pred Nothing

memoryError :: LLVMPtr sym w -> MemoryError -> Pred sym -> LLVMSafetyAssertion sym
memoryError pp ld pred =
  LLVMSafetyAssertion (BBMemoryError pp ld) pred Nothing

poison' :: Poison.Poison (RegValue' sym)
        -> Pred sym
        -> Text
        -> LLVMSafetyAssertion sym
poison' poison_ pred expl =
  LLVMSafetyAssertion (BBUndefinedBehavior (UB.PoisonValueCreated poison_)) pred (Just expl)

poison :: Poison.Poison (RegValue' sym)
       -> Pred sym
       -> LLVMSafetyAssertion sym
poison poison_ pred =
  LLVMSafetyAssertion (BBUndefinedBehavior (UB.PoisonValueCreated poison_)) pred Nothing

-- -----------------------------------------------------------------------
-- ** Lenses

classifier :: Simple Lens (LLVMSafetyAssertion sym) (BadBehavior sym)
classifier = lens _classifier (\s v -> s { _classifier = v})

predicate :: Simple Lens (LLVMSafetyAssertion sym) (Pred sym)
predicate = lens _predicate (\s v -> s { _predicate = v})

extra :: Simple Lens (LLVMSafetyAssertion sym) (Maybe Text)
extra = lens _extra (\s v -> s { _extra = v})

explainBB :: BadBehavior sym -> Doc
explainBB = \case
  BBUndefinedBehavior ub -> UB.explain ub
  BBMemoryError _ ld     -> ppMemoryError ld

detailBB :: IsExpr (SymExpr sym) => BadBehavior sym -> Doc
detailBB = \case
  BBUndefinedBehavior ub -> UB.ppReg ub
  BBMemoryError p _ld    ->
    text "Via pointer:" <+> UB.ppPointerPair (UB.pointerView p)
