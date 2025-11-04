{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.Debug.Inputs
  ( Inputs(..)
  , fail
  , parseInputs
  , parseInputsWithRetry
  , addPrompt
  , prepend
  , defaultDebuggerInputs
  ) where

import Control.Concurrent.Extra (once)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad qualified as Monad
import Control.Monad.Reader qualified as Reader
import Control.Monad.Trans (MonadTrans(lift))
import Data.Char qualified as Char
import Data.Functor.Contravariant (contramap)
import Data.IORef qualified as IORef
import Data.Text.IO qualified as IO
import Data.Text qualified as Text
import Data.Text (Text)
import Lang.Crucible.Debug.Command (CommandExt)
import Lang.Crucible.Debug.Complete (CompletionT)
import Lang.Crucible.Debug.Complete qualified as Complete
import Lang.Crucible.Debug.Outputs (Outputs)
import Lang.Crucible.Debug.Outputs qualified as Outs
import Lang.Crucible.Debug.Statement qualified as Stmt
import Lang.Crucible.Debug.Statement (Statement, ParseError, renderParseError)
import Lang.Crucible.Debug.Style qualified as Style
import Lang.Crucible.Debug.Style (StyleT)
import Prelude hiding (fail)
import System.Console.Isocline qualified as Isocline
import System.IO (Handle, hFlush, stdout)

newtype Inputs m a = Inputs { recv :: m a }
  deriving (Applicative, Functor, Monad)

instance MonadFail m => MonadFail (Inputs m) where
  fail = Inputs . Monad.fail

instance MonadIO m => MonadIO (Inputs m) where
  liftIO = Inputs . liftIO

instance MonadTrans Inputs where
  lift = Inputs

fail :: MonadFail m => Inputs m a
fail = Monad.fail "No more inputs"

addPrompt :: Handle -> Text -> Inputs IO a -> Inputs IO a
addPrompt hOut prompt (Inputs inps) =
  Inputs $ do
    IO.hPutStr hOut prompt
    hFlush hOut
    inps

prepend :: MonadIO m => [a] -> Inputs m a -> IO (Inputs m a)
prepend inps (Inputs rest) = do
  inpsRef <- IORef.newIORef inps
  pure (Inputs (go inpsRef))
  where
  go inpsRef = do
    is <- liftIO (IORef.readIORef inpsRef)
    case is of
      [] -> rest
      (i:is') -> do
        liftIO (IORef.writeIORef inpsRef is')
        pure i

parseInputs ::
  MonadFail m =>
  CommandExt cExt ->
  Inputs m Text ->
  Inputs m (Statement cExt)
parseInputs cExts (Inputs inps) = Inputs go
  where
    go = do
      txt <- inps
      case Stmt.parse cExts txt of
        Left err -> Monad.fail (show err)
        Right r -> pure r

parseInputsWithRetry ::
  Monad m =>
  CommandExt cExt ->
  Inputs m Text ->
  Outputs m ParseError ->
  Inputs m (Statement cExt)
parseInputsWithRetry cExts (Inputs inps) errs = Inputs go
  where
    go = do
      txt <- inps
      case Stmt.parse cExts txt of
        Left err -> do
          Outs.send errs err
          go
        Right r -> pure r

-- NOTE(lb): AFAIK, this only needs to be done once per process, not once per
-- debugger initialization. These settings probably persist no matter how many
-- times different debuggers (or defaultDebuggerInputs) are created.
initIsocline :: IO ()
initIsocline = do
  _ <- Isocline.enableAutoTab True
  Isocline.setHistory ".crucible-debug" 512

-- | Like 'Isocline.completeWord', but allow IO.
--
-- Implementation copied from 'Isocline.completeWord'.
completeWordIO ::
  Isocline.CompletionEnv ->
  String ->
  Maybe (Char -> Bool) ->
  (String -> IO [Isocline.Completion]) ->
  IO ()
completeWordIO cenv input isWordChar completer =
  Isocline.completeWordPrim cenv input isWordChar cenvCompleter
  where
    cenvCompleter ce i = do
      completes <- completer i
      _ <- Isocline.addCompletions ce completes
      return ()

readIsocline :: MonadIO m => CompletionT cExt (StyleT cExt m) String
readIsocline = do
  let extraPrompt = ""  -- prompt will be "> "
  styleEnv <- lift Reader.ask
  completionEnv <- Reader.ask
  let completer :: Isocline.CompletionEnv -> String -> IO ()
      completer cEnv input = do
        let isWordChar = Just (not . Char.isSpace)
        let completeWord w =
              mconcat . map Complete.completions <$>
                Complete.complete completionEnv input w
        let wordCompleter = fmap (map Isocline.completion) . completeWord
        completeWordIO cEnv input isWordChar wordCompleter
  liftIO $
    Isocline.readlineEx
      extraPrompt
      (Just completer)
      (Just (Style.runStyle styleEnv . Style.highlighter))

defaultDebuggerInputs ::
  MonadIO m =>
  CommandExt cExt ->
  IO (Inputs (CompletionT cExt (StyleT cExt m)) (Statement cExt))
defaultDebuggerInputs cExts = do
  -- NB: We delay initializing Isocline until the first input is requested, and
  -- then use 'once' to ensure that initialization occurs at most once. The
  -- benefit of doing it like this is that we ensure that a .crucible-debug
  -- file won't be created unless a Crux user specifically requests the
  -- debugger.
  initialize <- once initIsocline
  pure $
    parseInputsWithRetry
      cExts
      (do liftIO initialize
          Text.pack <$> lift readIsocline)
      (contramap renderParseError (Outs.lift (lift . liftIO) (Outs.hPutStrLn stdout)))
