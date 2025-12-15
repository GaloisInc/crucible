module Mir.Defaults
  ( defaultRustEdition
  , defaultRustEditionFlag
  ) where

-- | The default Rust language edition used by crux-mir when invoking Rust
-- tooling (e.g., mir-json or rustc) on a standalone @.rs@ file.
--
-- Cargo-managed builds continue to use the edition specified in @Cargo.toml@.
defaultRustEdition :: String
defaultRustEdition = "2021"

-- | The @--edition@ flag corresponding to 'defaultRustEdition'.
defaultRustEditionFlag :: String
defaultRustEditionFlag = "--edition=" ++ defaultRustEdition
