{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Crucible.Debug.Outputs
  ( Outputs
  , send
  , lift
  , accumulate
  , hPutStrLn
  , prettyOut
  , defaultDebuggerOutputs
  ) where

import Data.Functor.Contravariant (Contravariant(..))
import Data.IORef (IORef)
import Data.IORef qualified as IORef
import Data.Text (Text)
import Data.Text.IO qualified as IO
import Lang.Crucible.Debug.Response (Response, ResponseExt)
import Prettyprinter qualified as PP
import Prettyprinter.Render.Text qualified as PP
import System.IO (Handle, stdout)

newtype Outputs m a = Outputs { send :: a -> m () }

instance Contravariant (Outputs m) where
  contramap f (Outputs o) = Outputs (o . f)

lift :: (n () -> m ()) -> Outputs n a -> Outputs m a
lift f (Outputs s) = Outputs (f . s)

accumulate :: IORef [a] -> Outputs IO a
accumulate r = Outputs (IORef.modifyIORef r . (:))

hPutStrLn :: Handle -> Outputs IO Text
hPutStrLn hOut = Outputs (IO.hPutStrLn hOut)

prettyOut ::
  PP.Pretty a =>
  Handle ->
  PP.LayoutOptions ->
  Outputs IO a
prettyOut hOut opts =
  Outputs (PP.renderIO hOut . PP.layoutPretty opts . (PP.<> "\n") . PP.pretty)

defaultDebuggerOutputs ::
  PP.Pretty cExt =>
  PP.Pretty (ResponseExt cExt) =>
  Outputs IO (Response cExt)
defaultDebuggerOutputs = prettyOut stdout PP.defaultLayoutOptions
