------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Solver.SatResult
-- Description : Simple datastructure for capturing the result of a SAT/SMT query
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
module Lang.Crucible.Solver.SatResult
  ( SatResult(..)
  , isSat
  , isUnsat
  , isUnknown
  ) where

data SatResult mdl
   = Sat mdl
   | Unsat
   | Unknown
  deriving (Functor, Foldable, Traversable, Show)

isSat :: SatResult mdl -> Bool
isSat (Sat _) = True
isSat _ = False

isUnsat :: SatResult mdl -> Bool
isUnsat Unsat = True
isUnsat _ = False

isUnknown :: SatResult mdl -> Bool
isUnknown Unknown = True
isUnknown _ = False
