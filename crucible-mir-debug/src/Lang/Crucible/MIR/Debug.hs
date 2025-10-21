{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.MIR.Debug
  ( MIRCommand
  , mirCommandExt
  , mirExtImpl
  ) where

import Data.Parameterized.Some (Some)
import Data.Text (Text)
import Lang.Crucible.Debug (ExtImpl, CommandExt)
import Lang.Crucible.Debug qualified as Debug
import Prettyprinter as PP

-- | There are currently no MIR-specific debugger commands, but we may add some
-- in the future.
data MIRCommand

instance PP.Pretty MIRCommand where
  pretty = PP.pretty . name

abbrev :: MIRCommand -> Text
abbrev = \case

help :: MIRCommand -> Text
help = \case

name :: MIRCommand -> Text
name = \case

regex :: MIRCommand -> Some (Debug.RegexRepr Debug.ArgTypeRepr)
regex = \case

mirCommandExt :: CommandExt MIRCommand
mirCommandExt =
  Debug.CommandExt
  { Debug.extAbbrev = abbrev
  , Debug.extDetail = const Nothing
  , Debug.extHelp = help
  , Debug.extList = []
  , Debug.extName = name
  , Debug.extRegex = regex
  }

-- | There are currently no MIR-specific debugger responses, but we may add some
-- in the future.
data MIRResponse

instance PP.Pretty MIRResponse where
  pretty = \case

type instance Debug.ResponseExt MIRCommand = MIRResponse

mirExtImpl :: ExtImpl MIRCommand p sym ext t
mirExtImpl =
  Debug.ExtImpl $
    \case
