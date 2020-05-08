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
  , MemoryLoadError(..)
  , ppMemoryLoadError
  , undefinedBehavior
  , undefinedBehavior'
  , poison
  , poison'
  , memoryLoadError
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
import qualified Data.Text as Text

import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified What4.Interface as W4I

import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF (FunctorF(..), FoldableF(..), TraversableF(..))
import qualified Data.Parameterized.TraversableF as TF

import           Lang.Crucible.Types
import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import qualified Lang.Crucible.LLVM.Extension.Safety.Poison as Poison
import qualified Lang.Crucible.LLVM.Extension.Safety.UndefinedBehavior as UB
import           Lang.Crucible.LLVM.MemModel.Common
import           Lang.Crucible.LLVM.MemModel.Type


------------------------------------------------------------------------
-- ** MemoryLoadError

-- | The kinds of type errors that arise while reading memory/constructing LLVM
-- values
data MemoryLoadError =
    TypeMismatch StorageType StorageType
  | UnexpectedArgumentType Text [StorageType]
  | PreviousErrors Text [MemoryLoadError]
  | ApplyViewFail ValueView
  | Invalid StorageType
  | Invalidated Text
  | NoSatisfyingWrite Doc
  deriving (Generic)

instance Pretty MemoryLoadError where
  pretty = ppMemoryLoadError

instance Show MemoryLoadError where
  show = show . ppMemoryLoadError

ppMemoryLoadError :: MemoryLoadError -> Doc
ppMemoryLoadError =
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
    PreviousErrors txt errs ->
      vcat [ "Operation failed due to previous errors: "
           , text (Text.unpack txt)
           ]
      <$$> indent 2 (vcat (map ppMemoryLoadError errs))
    ApplyViewFail vw ->
      "Failure when applying value view" <+> text (show vw)
    Invalid ty ->
      "Load from invalid memory at type " <+> text (show ty)
    Invalidated msg ->
      "Load from explicitly invalidated memory:" <+> text (Text.unpack msg)
    NoSatisfyingWrite doc ->
      vcat
       [ "No previous write to this location was found"
       , indent 2 doc
       ]

-- -----------------------------------------------------------------------
-- ** BadBehavior

-- | Combine the three types of bad behaviors
--
data BadBehavior (e :: CrucibleType -> Type) =
    BBUndefinedBehavior (UB.UndefinedBehavior e)
  | BBLoadError         MemoryLoadError
  deriving (Generic, Typeable)

-- -----------------------------------------------------------------------
-- *** Instances

$(return [])

instance FunctorF BadBehavior where
  fmapF f (BBUndefinedBehavior ub) = BBUndefinedBehavior $ fmapF f ub
  fmapF _ (BBLoadError ld)         = BBLoadError ld

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

data LLVMSafetyAssertion (e :: CrucibleType -> Type) =
  LLVMSafetyAssertion
    { _classifier :: BadBehavior e -- ^ What could have gone wrong?
    , _predicate  :: e BoolType    -- ^ Is the value safe/defined?
    , _extra      :: Maybe Text    -- ^ Additional human-readable context
    }
  deriving (Generic, Typeable)

-- -----------------------------------------------------------------------
-- *** Instances

$(return [])

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

memoryLoadError :: MemoryLoadError -> e BoolType -> LLVMSafetyAssertion e
memoryLoadError ld pred =
  LLVMSafetyAssertion (BBLoadError ld) pred Nothing

poison' :: Poison.Poison e
        -> e BoolType
        -> Text
        -> LLVMSafetyAssertion e
poison' poison_ pred expl =
  LLVMSafetyAssertion (BBUndefinedBehavior (UB.PoisonValueCreated poison_)) pred (Just expl)

poison :: Poison.Poison e
       -> e BoolType
       -> LLVMSafetyAssertion e
poison poison_ pred =
  LLVMSafetyAssertion (BBUndefinedBehavior (UB.PoisonValueCreated poison_)) pred Nothing

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
  BBLoadError ld         -> ppMemoryLoadError ld

detailBB :: (W4I.PrintExpr (W4I.SymExpr sym), W4I.IsExpr (W4I.SymExpr sym)) =>
         BadBehavior (RegValue' sym) -> Doc
detailBB = \case
  BBUndefinedBehavior ub -> UB.ppReg ub
  BBLoadError ld         -> ppMemoryLoadError ld
