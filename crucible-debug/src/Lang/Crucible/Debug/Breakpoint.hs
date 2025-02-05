{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE ImportQualifiedPost #-}

module Lang.Crucible.Debug.Breakpoint
  ( Breakpoint(..)
  , toString
  , toText
  ) where

import Data.Text qualified as Text
import Data.Text (Text)
import What4.FunctionName qualified as W4

newtype Breakpoint
  = BreakFunction W4.FunctionName
  deriving (Eq, Ord)

toString :: Breakpoint -> String
toString = Text.unpack . toText
{-# INLINE toString #-}

toText :: Breakpoint -> Text
toText (BreakFunction fNm) = W4.functionName fNm
{-# INLINE toText #-}
