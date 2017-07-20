------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Simulator.VarRecord
-- Description : Datastructure for recording symbolic values
-- Copyright   : (c) Galois, Inc 2015-2016
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
--
-- Symbolic values created at runtime are captured in a 'VarRecord'
-- so they can be retrieved later.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.VarRecord
  ( VarRecord(..)
  , traverseVarRecord
  ) where

import           Data.Parameterized.TraversableFC

import qualified Lang.MATLAB.MultiDimArray as MDA

import           Lang.Crucible.Simulator.RegValue (SomeSymbolicBVArray(..))
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Types
import qualified Lang.Crucible.Utils.SymMultiDimArray as SMDA

------------------------------------------------------------------------
-- VarRecord

-- | A var record contains symbolic expressions used in variables.
data VarRecord f
  = CplxVarArray       !(MDA.MultiDimArray (f BaseComplexType))
  | RealVarArray       !(MDA.MultiDimArray (f BaseRealType))
  | LogicalVarArray    !(MDA.MultiDimArray (f BaseBoolType))
  | forall n . (1 <= n)
  => IntVarArray !(NatRepr n)  !(MDA.MultiDimArray (f (BaseBVType n)))
  | forall n . (1 <= n)
  => UIntVarArray !(NatRepr n) !(MDA.MultiDimArray (f (BaseBVType n)))
  | SymLogicalVarArray !(SMDA.SymMultiDimArray f BaseBoolType)
  | SymIntegerVarArray !(SMDA.SymMultiDimArray f BaseIntegerType)
  | SymRealVarArray    !(SMDA.SymMultiDimArray f BaseRealType)
  | SymCplxVarArray    !(SMDA.SymMultiDimArray f BaseComplexType)
  | SymIntVarArray     !(SomeSymbolicBVArray f)
  | SymUIntVarArray    !(SomeSymbolicBVArray f)
  | forall n. (1 <= n)
  => BVVarScalar !(NatRepr n) !(f (BaseBVType n))
  | RealVarScalar (f BaseRealType)


traverseVarRecord :: Applicative m
                  => (forall tp . e tp -> m (f tp))
                  -> (VarRecord e -> m (VarRecord f))
traverseVarRecord f vr =
  case vr of
    CplxVarArray    a -> CplxVarArray    <$> traverse f a
    RealVarArray    a -> RealVarArray    <$> traverse f a
    LogicalVarArray a -> LogicalVarArray <$> traverse f a
    IntVarArray  w a  -> IntVarArray  w  <$> traverse f a
    UIntVarArray w a  -> UIntVarArray w  <$> traverse f a
    SymLogicalVarArray a -> SymLogicalVarArray <$> traverseFC f a
    SymIntegerVarArray a -> SymIntegerVarArray <$> traverseFC f a
    SymRealVarArray a    -> SymRealVarArray    <$> traverseFC f a
    SymCplxVarArray a    -> SymCplxVarArray    <$> traverseFC f a
    SymIntVarArray (SomeSymbolicBVArray w a) ->
      SymIntVarArray . SomeSymbolicBVArray w <$> traverseFC f a
    SymUIntVarArray (SomeSymbolicBVArray w a) ->
      SymUIntVarArray . SomeSymbolicBVArray w <$> traverseFC f a
    BVVarScalar w x ->
      BVVarScalar w <$> f x
    RealVarScalar x ->
      RealVarScalar <$> f x
