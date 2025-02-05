{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Crucible.Debug.Statement
  ( Statement(..)
  , ParseError
  , renderParseError
  , parse
  ) where

import Data.Text (Text)
import Lang.Crucible.Debug.Command (Command)
import Lang.Crucible.Debug.Command qualified as Cmd
import Data.Text qualified as Text

data Statement cExt
  = Statement
  { stmtCmd :: Command cExt
  , stmtArgs :: [Text]
  }
  deriving Functor

data ParseError
  = InvalidCommand Text
  | NoCommand
  deriving Show

renderParseError :: ParseError -> Text
renderParseError =
  \case
    InvalidCommand txt -> "Invalid command: " <> txt
    NoCommand -> "No command given"

parse :: Cmd.CommandExt cExt -> Text -> Either ParseError (Statement cExt)
parse cExts txt =
  case Text.words txt of
    [] -> Left NoCommand
    (cmdText:args) ->
      case Cmd.parse cExts cmdText of
        Just cmd -> Right (Statement cmd args)
        Nothing -> Left (InvalidCommand cmdText)
