{-# OPTIONS_GHC -Wno-orphans #-}

module Crux.LogConfiguration
  ( cruxJSONOptions,
  )
where

import qualified Data.Aeson as JSON
import Data.Aeson.TypeScript.TH (TypeScript (getTypeScriptType))
import Data.Version (Version)
import Data.Word (Word64)

-- | To be used by deriving mechanisms for uniformity.  Must be defined in a
-- separate module due to GHC stage restriction.
cruxJSONOptions :: JSON.Options
cruxJSONOptions = JSON.defaultOptions

instance TypeScript Version where
  getTypeScriptType _ = "string" -- FIXME

instance TypeScript Word64 where
  getTypeScriptType _ = "number" -- FIXME
