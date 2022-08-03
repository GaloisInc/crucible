{-
Module      : UCCrux.LLVM.View.Idioms
Description : Tweak 'Aeson.Options' to remove Haskell idioms from JSON instances.
Copyright   : (c) Galois, Inc 2022
License     : BSD3
Maintainer  : Langston Barrett <langston@galois.com>
Stability   : provisional

This module contains helper functions for tweaking 'Aeson.Options' to remove
unnecessary Haskell idioms from the JSON representations. There is no need for
the JSON representation to reflect implementation details, and removing such can
make the JSON more terse, hopefully making it use less RAM/disk space and
network bandwidth, and making it easier to write by hand (especially for users
not familiar with Haskell coding conventions).

The helpers in this module post-compose their modifications with those already
specified in the 'Aeson.fieldLabelModifier' and 'Aeson.constructorTagModifier'
fields of 'Aeson.Options'.
-}

module UCCrux.LLVM.View.Options.Idioms
  ( constructorPrefix
  , constructorSuffix
  , recordSelectorPrefix
  )
where

import qualified Data.Aeson as Aeson

-- | Drop shared prefixes from sum type constructors.
--
-- It's common in Haskell code for all constructors of a type to share a common
-- prefix, e.g., "Color" in
--
-- > data Color = ColorGreen | ColorBlue
constructorPrefix :: String -> Aeson.Options -> Aeson.Options
constructorPrefix s opts =
  opts { Aeson.constructorTagModifier =
           drop (length s) . Aeson.constructorTagModifier opts
       }

-- | Drop shared suffixes from sum type constructors.
--
-- It's common in Haskell code for all constructors of a type to share a common
-- suffix, e.g., "Box" in
--
-- > data Box = BigBox | SmallBox
constructorSuffix :: String -> Aeson.Options -> Aeson.Options
constructorSuffix s opts =
  opts { Aeson.constructorTagModifier =
           dropSuffix (length s) . Aeson.constructorTagModifier opts
       }
  where dropSuffix l = reverse . drop l . reverse

-- | Drop shared prefixes from record selector (i.e., field) names.
--
-- It's common in Haskell code for all record selectors for the same type to
-- share a common prefix, e.g., "pt" in
--
-- > data Point2D = Point2D { ptX :: Int, ptY :: Int }
--
-- This idiom is used in part to avoid name clashes due to the lack of
-- namespacing for record selectors.
recordSelectorPrefix :: String -> Aeson.Options -> Aeson.Options
recordSelectorPrefix s opts =
  opts { Aeson.fieldLabelModifier =
           drop (length s) . Aeson.fieldLabelModifier opts
       }
