------------------------------------------------------------------------
-- |
-- Module      : What4.SatResult
-- Description : Simple datastructure for capturing the result of a SAT/SMT query
-- Copyright   : (c) Galois, Inc 2015
-- License     : BSD3
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
module What4.SatResult
  ( SatResult(..)
  , isSat
  , isUnsat
  , isUnknown
  , forgetModelAndCore
  , traverseSatResult
  ) where

import           GHC.Generics (Generic)

data SatResult mdl core
   = Sat mdl
   | Unsat core
   | Unknown
 deriving (Show, Generic)

traverseSatResult :: Applicative t =>
  (a -> t q) ->
  (b -> t r) ->
  SatResult a b -> t (SatResult q r)
traverseSatResult f g = \case
  Sat m   -> Sat <$> f m
  Unsat c -> Unsat <$> g c
  Unknown -> pure Unknown

isSat :: SatResult mdl core -> Bool
isSat Sat{} = True
isSat _ = False

isUnsat :: SatResult mdl core -> Bool
isUnsat Unsat{} = True
isUnsat _ = False

isUnknown :: SatResult mdl core -> Bool
isUnknown Unknown = True
isUnknown _ = False

forgetModelAndCore :: SatResult a b -> SatResult () ()
forgetModelAndCore Sat{} = Sat ()
forgetModelAndCore Unsat{} = Unsat ()
forgetModelAndCore Unknown = Unknown
