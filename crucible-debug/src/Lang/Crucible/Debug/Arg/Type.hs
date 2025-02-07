{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Lang.Crucible.Debug.Arg.Type
  ( type ArgType(..)
  , type Breakpoint
  , type Command
  , type Exactly
  , type Function
  , type Int
  , type Path
  , type Text
  , ArgTypeRepr(..)
  ) where

import Data.Kind (Type)
import Data.Parameterized.Classes (KnownRepr(knownRepr), ShowF (showF))
import Data.Parameterized.SymbolRepr (SymbolRepr, knownSymbol, symbolRepr)
import Data.Type.Equality (TestEquality(testEquality), type (:~:)(Refl))
import GHC.TypeLits (KnownSymbol, Symbol)
import Lang.Crucible.Debug.Regex qualified as Rgx
import Prelude hiding (Int)
import Prettyprinter qualified as PP

-- | Type-level only
data ArgType
  = TBreakpoint
  | TCommand
  | TExactly Symbol
  | TFunction
  | TInt
  | TPath
  | TText

type Breakpoint = Rgx.Lit 'TBreakpoint
type Command = Rgx.Lit 'TCommand
type Exactly s = Rgx.Lit ('TExactly s)
type Function = Rgx.Lit 'TFunction
type Int = Rgx.Lit 'TInt
type Path = Rgx.Lit 'TPath
type Text = Rgx.Lit 'TText

-- | Value-level representative of 'ArgType'
type ArgTypeRepr :: ArgType -> Type
data ArgTypeRepr i where
  TBreakpointRepr :: ArgTypeRepr 'TBreakpoint
  TCommandRepr :: ArgTypeRepr 'TCommand
  TExactlyRepr :: SymbolRepr s -> ArgTypeRepr ('TExactly s)
  TFunctionRepr :: ArgTypeRepr 'TFunction
  TIntRepr :: ArgTypeRepr 'TInt
  TPathRepr :: ArgTypeRepr 'TPath
  TTextRepr :: ArgTypeRepr 'TText

instance Show (ArgTypeRepr t) where
  show =
    \case
      TBreakpointRepr -> "TBreakpointRepr"
      TCommandRepr -> "TCommandRepr"
      TExactlyRepr s -> "TExactlyRepr(" ++ show s ++ ")"
      TFunctionRepr -> "TFunctionRepr"
      TIntRepr -> "TIntRepr"
      TPathRepr -> "TPathRepr"
      TTextRepr -> "TTextRepr"

instance ShowF ArgTypeRepr where
  showF = show

instance TestEquality ArgTypeRepr where
  testEquality r r' =
    case (r, r') of
      (TBreakpointRepr, TBreakpointRepr) -> Just Refl
      (TBreakpointRepr, _) -> Nothing
      (TCommandRepr, TCommandRepr) -> Just Refl
      (TCommandRepr, _) -> Nothing
      (TExactlyRepr s, TExactlyRepr s') ->
        case testEquality s s' of
          Just Refl -> Just Refl
          Nothing -> Nothing
      (TExactlyRepr {}, _) -> Nothing
      (TFunctionRepr, TFunctionRepr) -> Just Refl
      (TFunctionRepr {}, _) -> Nothing
      (TIntRepr, TIntRepr) -> Just Refl
      (TIntRepr, _) -> Nothing
      (TPathRepr, TPathRepr) -> Just Refl
      (TPathRepr, _) -> Nothing
      (TTextRepr, TTextRepr) -> Just Refl
      (TTextRepr, _) -> Nothing

instance KnownRepr ArgTypeRepr 'TBreakpoint where
  knownRepr = TBreakpointRepr

instance KnownRepr ArgTypeRepr 'TCommand where
  knownRepr = TCommandRepr

instance KnownSymbol s => KnownRepr ArgTypeRepr ('TExactly s) where
  knownRepr = TExactlyRepr knownSymbol

instance KnownRepr ArgTypeRepr 'TFunction where
  knownRepr = TFunctionRepr

instance KnownRepr ArgTypeRepr 'TInt where
  knownRepr = TIntRepr

instance KnownRepr ArgTypeRepr 'TPath where
  knownRepr = TPathRepr

instance KnownRepr ArgTypeRepr 'TText where
  knownRepr = TTextRepr

instance PP.Pretty (ArgTypeRepr t) where
  pretty =
    \case
      TBreakpointRepr -> "BREAKPOINT"
      TCommandRepr -> "COMMAND"
      TExactlyRepr s -> PP.pretty (symbolRepr s)
      TFunctionRepr -> "FUNCTION"
      TIntRepr -> "INT"
      TPathRepr -> "PATH"
      TTextRepr -> "TEXT"
