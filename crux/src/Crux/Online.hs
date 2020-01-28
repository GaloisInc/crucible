{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
module Crux.Online where

import Lang.Crucible.Backend.Online
import What4.Protocol.Online (OnlineSolver)
import qualified Lang.Crucible.Backend.Simple as CBS

-- | A GADT to capture the online solver constraints when we need them
data SomeOnlineSolver sym where
  SomeOnlineSolver :: (sym ~ OnlineBackend scope solver fs
                      , OnlineSolver scope solver
                      ) => SomeOnlineSolver sym

-- | Allows checking whether `sym` is an online solver.  Produces a
-- `SomeOnlineSolver` proof if it is, allowing the caller to use functions that
-- are specific to online solvers.
class MaybeOnlineSolver sym where
  maybeOnlineSolver :: Maybe (SomeOnlineSolver sym)

instance OnlineSolver scope solver => MaybeOnlineSolver (OnlineBackend scope solver fs) where
  maybeOnlineSolver = Just SomeOnlineSolver

instance MaybeOnlineSolver (CBS.SimpleBackend t fs) where
  maybeOnlineSolver = Nothing
