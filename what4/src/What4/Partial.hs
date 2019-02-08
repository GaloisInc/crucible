{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-|
Module           : What4.Solver.Partial
Copyright        : (c) Galois, Inc 2014-2016
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>

Often, various operations on values are only partially defined (in the case of
Crucible expressions, consider loading a value from a pointer - this is only
defined in the case that the pointer is valid and non-null). The 'PartExpr'
type allows for packaging values together with predicates that express their
partiality: the value is only valid if the predicate is true.

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module What4.Partial
 ( Partial(..)
 , partialPred
 , partialValue
 ) where

import           GHC.Generics (Generic, Generic1)
import           Data.Data (Data)

import           What4.BaseTypes
import           What4.Utils.Complex (Complex((:+)))
import           What4.Interface (IsExprBuilder, SymExpr)
import qualified What4.Interface as W4I

import           Control.Lens.TH (makeLenses)
import           Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import           Data.Eq.Deriving (deriveEq1, deriveEq2)
import           Data.Ord.Deriving (deriveOrd1, deriveOrd2)
import           Text.Show.Deriving (deriveShow1, deriveShow2)

------------------------------------------------------------------------
-- ** Partial

-- | A partial value represents a value that may or may not be valid.
--
-- The '_partialPred' field represents a predicate (optionally with additional
-- provenance information) embodying the value's partiality.
data Partial p v =
  Partial { _partialPred  :: !p
          , _partialValue :: !v
          }
  deriving (Data, Eq, Functor, Generic, Generic1, Foldable, Traversable, Ord, Show)

makeLenses ''Partial

$(deriveBifunctor     ''Partial)
$(deriveBifoldable    ''Partial)
$(deriveBitraversable ''Partial)
$(deriveEq1           ''Partial)
$(deriveEq2           ''Partial)
$(deriveOrd1          ''Partial)
$(deriveOrd2          ''Partial)
$(deriveShow1         ''Partial)
$(deriveShow2         ''Partial)

-- | The "zero value" of the given type
zero :: (IsExprBuilder sym) => sym -> BaseTypeRepr ty -> IO (Maybe (SymExpr sym ty))
zero sym =
  \case
    BaseBoolRepr       -> Just <$> pure (W4I.falsePred sym)
    BaseBVRepr w       -> Just <$> W4I.bvLit sym w 0
    BaseNatRepr        -> Just <$> W4I.natLit sym 0
    BaseIntegerRepr    -> Just <$> W4I.intLit sym 0
    BaseRealRepr       -> Just <$> W4I.realLit sym 0
    BaseFloatRepr fppr -> Just <$> W4I.floatLit sym fppr 0
    BaseStringRepr     -> Just <$> W4I.stringLit sym ""
    BaseComplexRepr    -> let z = fromIntegral (0 :: Int)
                          in Just <$> W4I.mkComplexLit sym (z :+ z)
    _                  -> pure Nothing
