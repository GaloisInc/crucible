-- |
-- Module           : Lang.Crucible.LLVM.Errors
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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Errors
  ( LLVMSafetyAssertion
  , BadBehavior(..)
  , undefinedBehavior
  , undefinedBehavior'
  , poison
  , poison'
  , memoryError
  , detailBB
  , explainBB
  , ppBB
  , concBadBehavior
    -- ** Lenses
  , classifier
  , predicate
  , extra
  ) where

import           Prelude hiding (pred)

import           Control.Lens
import           Data.Text (Text)

import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.Interface
import           What4.Expr (GroundValue)

import           Lang.Crucible.Simulator.RegValue (RegValue'(..))
import qualified Lang.Crucible.LLVM.Errors.MemoryError as ME
import qualified Lang.Crucible.LLVM.Errors.Poison as Poison
import qualified Lang.Crucible.LLVM.Errors.UndefinedBehavior as UB

-- -----------------------------------------------------------------------
-- ** BadBehavior

-- | Combine the three types of bad behaviors
--
data BadBehavior sym where
  BBUndefinedBehavior :: UB.UndefinedBehavior (RegValue' sym) -> BadBehavior sym
  BBMemoryError       :: ME.MemoryError sym -> BadBehavior sym
 deriving Typeable

concBadBehavior ::
  IsExprBuilder sym =>
  sym ->
  (forall tp. SymExpr sym tp -> IO (GroundValue tp)) ->
  BadBehavior sym -> IO (BadBehavior sym)
concBadBehavior sym conc (BBUndefinedBehavior ub) =
  BBUndefinedBehavior <$> UB.concUB sym conc ub
concBadBehavior sym conc (BBMemoryError me) =
  BBMemoryError <$> ME.concMemoryError sym conc me

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

memoryError :: (1 <= w) => ME.MemErrContext sym w -> ME.MemoryErrorReason -> Pred sym -> LLVMSafetyAssertion sym
memoryError (gsym,pp,mem) ld pred =
  LLVMSafetyAssertion (BBMemoryError (ME.MemoryError gsym pp mem ld)) pred Nothing

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
  BBMemoryError me       -> ME.explain me

detailBB :: IsExpr (SymExpr sym) => BadBehavior sym -> Doc
detailBB = \case
  BBUndefinedBehavior ub -> UB.ppReg ub
  BBMemoryError me -> ME.details me

ppBB :: IsExpr (SymExpr sym) => BadBehavior sym -> Doc
ppBB = \case
  BBUndefinedBehavior ub -> UB.ppReg ub
  BBMemoryError me -> ME.ppME me
