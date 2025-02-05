{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Crucible.Debug.Command
  ( Command(..)
  , CommandExt(..)
  , voidExts
  , allCmds
  , name
  , abbrev
  , parse
  , detail
  , help
  , regex
  ) where

import Data.List qualified as List
import Data.Parameterized.Some (Some)
import Data.Text (Text)
import Data.Void (Void, absurd)
import Lang.Crucible.Debug.Arg.Type (ArgTypeRepr)
import Lang.Crucible.Debug.Command.Base qualified as BCmd
import Lang.Crucible.Debug.Regex qualified as Rgx
import Prettyprinter qualified as PP

data CommandExt cExt
  = CommandExt
  { -- | Used in 'abbrev', 'parse'
    extAbbrev :: cExt -> Text
  , extList :: [cExt]
    -- | Multi-line help string. Used in 'detail'.
    --
    -- This is always displayed as a new paragraph following 'extHelp', so it
    -- should not repeat the information there.
    --
    -- Should be long-form prose, with proper capitalization and punctuation.
    -- Should not rely on being shown in monospaced font.
  , extDetail :: cExt -> Maybe Text
    -- | Single-line help string. Used in 'help'.
    --
    -- The first letter should be capitalized, it should not end in a period.
    -- It should probably be less than about 70 characters long.
  , extHelp :: cExt -> Text
    -- | Used in 'help', 'parse'
  , extName :: cExt -> Text
    -- | Used in 'help'
  , extRegex :: cExt -> Some (Rgx.RegexRepr ArgTypeRepr)
  }

voidExts :: CommandExt Void
voidExts =
  CommandExt
  { extAbbrev = absurd
  , extDetail = absurd
  , extHelp = absurd
  , extList = []
  , extName = absurd
  , extRegex = absurd
  }

data Command cExt
  = Base BCmd.BaseCommand
  | Ext cExt
  deriving (Functor, Show)

instance PP.Pretty cExt => PP.Pretty (Command cExt) where
  pretty =
    \case
      Base bCmd -> PP.pretty bCmd
      Ext xCmd -> PP.pretty xCmd

name :: CommandExt cExt -> Command cExt -> Text
name cExts =
  \case
    Base bCmd -> BCmd.name bCmd
    Ext xCmd -> extName cExts xCmd

abbrev :: CommandExt cExt -> Command cExt -> Text
abbrev cExts =
  \case
    Base bCmd -> BCmd.abbrev bCmd
    Ext xCmd -> extAbbrev cExts xCmd

allCmds :: CommandExt cExt -> [Command cExt]
allCmds cExts = map Base [minBound..maxBound] ++ map Ext (extList cExts)

parse :: CommandExt cExt -> Text -> Maybe (Command cExt)
parse cExts txt =
  List.find (\c -> name cExts c == txt || abbrev cExts c == txt) (allCmds cExts)

detail :: CommandExt cExt -> Command cExt -> Maybe Text
detail cExts =
  \case
    Base bCmd -> BCmd.detail bCmd
    Ext xCmd -> extDetail cExts xCmd

help :: CommandExt cExt -> Command cExt -> Text
help cExts =
  \case
    Base bCmd -> BCmd.help bCmd
    Ext xCmd -> extHelp cExts xCmd

regex :: CommandExt cExt -> Command cExt -> Some (Rgx.RegexRepr ArgTypeRepr)
regex cExts =
  \case
    Base bCmd -> BCmd.regex bCmd
    Ext xCmd -> extRegex cExts xCmd
