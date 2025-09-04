{-# LANGUAGE TemplateHaskell #-}

-- | These are placed in their own module to minimize the cost of recompilation
-- due to Template Haskell.
module Crux.GitHash (hash, branch, dirty, unknown) where

import GitHash (GitInfo, giBranch, giDirty, giHash, tGitInfoCwdTry)

gitInfo :: Either String GitInfo
gitInfo = $$tGitInfoCwdTry

hash :: String
hash = case gitInfo of
  Left _ -> unknown
  Right gi -> giHash gi

branch :: String
branch = case gitInfo of
  Left _ -> unknown
  Right gi -> giBranch gi

dirty :: Bool
dirty = case gitInfo of
  Left _ -> False
  Right gi -> giDirty gi

-- | What to report if we are unable to determine git-related information.
unknown :: String
unknown = "UNKNOWN"
