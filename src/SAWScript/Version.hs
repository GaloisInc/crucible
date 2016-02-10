-- |
-- Module      :  $Header$
-- Copyright   :  (c) 2013-2016 Galois, Inc.
-- License     :  Free for non-commercial use. See LICENSE.
-- Maintainer  :  saw@galois.com
-- Stability   :  provisional
-- Portability :  portable

{-# LANGUAGE Safe #-}

module SAWScript.Version (
    commitHash
  , commitShortHash
  , commitBranch
  , commitDirty
  , version
  ) where

import Paths_saw_script
import qualified GitRev

commitHash :: String
commitHash = GitRev.hash

commitShortHash :: String
commitShortHash = take 7 GitRev.hash

commitBranch :: String
commitBranch = GitRev.branch

commitDirty :: Bool
commitDirty = GitRev.dirty
