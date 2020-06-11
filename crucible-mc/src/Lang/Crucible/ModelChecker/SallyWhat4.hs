{-# LANGUAGE TypeOperators #-}

-- |
-- Module           : SallyWhat4
-- Description      : Utilities to bridge the gap between Sally and What4
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.SallyWhat4
  ( userSymbol',
  )
where

import qualified What4.Interface as What4

-- | @userSymbol'@ is really @What4.userSymbol@, but expecting that it won't
-- fail
userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol
