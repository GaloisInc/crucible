{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Lang.Crucible.Analysis.Taint where

import Lang.Crucible.Analysis.Fixpoint
import Lang.Crucible.Core

data Tainted (tp :: CrucibleType) where
  Tainted :: Tainted tp
  Untainted :: Tainted tp
  deriving (Eq, Show)

taintDomain :: Domain Tainted
taintDomain = Domain {domTop = Tainted
                     ,domBottom = Untainted
                     ,domJoin = \t1 t2 -> if t1 == Tainted || t2 == Tainted then Tainted
                                          else Untainted
                     ,domEq = (==)
                     ,domIter = WTO
                     }

