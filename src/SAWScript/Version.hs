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
  , hashText
  , versionText
  ) where

import Paths_saw_script (version)
import qualified GitRev
import Data.Version (showVersion)

commitHash :: String
commitHash = GitRev.hash

commitShortHash :: String
commitShortHash = take 7 GitRev.hash

commitBranch :: String
commitBranch = GitRev.branch

commitDirty :: Bool
commitDirty = GitRev.dirty

hashText :: String
hashText | commitShortHash == "UNKNOWN" = ""
         | otherwise = " (" ++ commitShortHash ++ ")"

versionText :: String
versionText = "version " ++ showVersion version ++ hashText
