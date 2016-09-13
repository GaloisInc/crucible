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

#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
#endif

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
