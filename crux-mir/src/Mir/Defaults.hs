module Mir.Defaults (defaultRustEditionFlag) where

defaultRustEdition :: String
defaultRustEdition = "2021"

defaultRustEditionFlag :: String
defaultRustEditionFlag = "--edition=" ++ defaultRustEdition
