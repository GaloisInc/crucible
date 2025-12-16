module Mir.MirJsonArgs
  ( buildMirJsonArgs
  ) where

import Data.List (isPrefixOf)
import Mir.Defaults (defaultRustEditionFlag)

-- | Given base mir-json args (without any edition flag) and extra args
--   from the user, build the final argv.
--
-- Policy:
--   * If the user supplies any --edition (or --edition=...) in extras,
--     we DO NOT add the default edition.
--   * Otherwise, we add the default --edition flag.
buildMirJsonArgs :: [String]   -- ^ base/default args (no edition)
                 -> [String]   -- ^ extra args (from MIROptions.mirJsonArgs)
                 -> [String]
buildMirJsonArgs base extras =
  let hasEdition   = any isEditionArg extras
      editionPart  = if hasEdition then [] else [defaultRustEditionFlag]
  in base ++ editionPart ++ extras

isEditionArg :: String -> Bool
isEditionArg s =
  s == "--edition" || "--edition=" `isPrefixOf` s
