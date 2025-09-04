{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Crux.Version
  ( version
  , commitHash
  , commitBranch
  , commitDirty
  ) where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KeyMap
import qualified Data.ByteString as BS
import Data.FileEmbed (embedFileRelative)
import qualified Data.Text as Text
import Data.Version (showVersion)
import qualified Paths_crux (version)

import qualified Crux.GitHash as GitHash

version :: String
version = showVersion Paths_crux.version

commitHash :: String
commitHash
  | hash /= GitHash.unknown =
      hash
  -- See Note [crux.buildinfo.json]
  | Just buildinfoVal <- Aeson.decodeStrict buildinfo
  , Just (Aeson.String buildinfoHash) <- KeyMap.lookup "hash" buildinfoVal =
      Text.unpack buildinfoHash
  | otherwise =
      GitHash.unknown
 where
  hash = GitHash.hash

commitBranch :: String
commitBranch
  | branch /= GitHash.unknown =
      branch
  -- See Note [crux.buildinfo.json]
  | Just buildinfoVal <- Aeson.decodeStrict buildinfo
  , Just (Aeson.String buildinfoCommit) <- KeyMap.lookup "branch" buildinfoVal =
      Text.unpack buildinfoCommit
  | otherwise =
      GitHash.unknown
 where
  branch = GitHash.branch

commitDirty :: Bool
commitDirty
  | dirty =
      dirty
  -- See Note [crux.buildinfo.json]
  | Just buildinfoVal <- Aeson.decodeStrict buildinfo
  , Just (Aeson.Bool buildinfoDirty) <- KeyMap.lookup "dirty" buildinfoVal =
      buildinfoDirty
  | otherwise =
      False
 where
  dirty = GitHash.dirty

-- Helper, not exported
--
-- See Note [crux.buildinfo.json]
buildinfo :: BS.ByteString
buildinfo = $(embedFileRelative "crux.buildinfo.json")

{-
Note [crux.buildinfo.json]
~~~~~~~~~~~~~~~~~~~~~~~~~~
By default, we determine the git commit hash, branch, and dirty information
using the githash library, which invokes git at compile time to query the
relevant information in the .git subdirectory. This works well for local
developments where the git binary and the .git subdirectory are both readily
available. It does not work so well for building in a Docker image, as we
intentionally do not copy over the .git subdirectory into the image to prevent
spurious cache invalidations caused by the contents of .git changing (which
they do, quite often).

As an alternative to githash, we also employ a convention where a build system
can create a crux.buildinfo.json file locally which contains the necessary
git-related information. The schema for this file is:

  {
    "hash": <string>,
    "branch": <string>,
    "dirty": <bool>
  }

This way, a build system (which has access to git/.git) can write this
information to a file, proceed to build the Docker image (which does not have
access to git/.git), and then have all of the expected information embedded
into the output of --version.
-}
