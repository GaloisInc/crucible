{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}

------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Utils.MonadVerbosity
-- Description      : A typeclass for monads equipped with a logging function
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
module Lang.Crucible.Utils.MonadVerbosity
  ( MonadVerbosity(..)
  , withVerbosity
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Reader
import System.IO

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

-- | This class applies to monads that contain verbosity information,
--   which is used to control the level of debugging messages
--   presented to the user.
class (Applicative m, MonadIO m) => MonadVerbosity m where
  getVerbosity :: m Int

  whenVerbosity :: (Int -> Bool) -> m () -> m ()
  whenVerbosity p m = do
    v <- getVerbosity
    when (p v) m

  getLogFunction :: m (Int -> String -> IO ())

  -- Get function for writing a line of output.
  getLogLnFunction :: m (Int -> String -> IO ())
  getLogLnFunction = do
    w <- getLogFunction
    return (\n s -> w n (s ++ "\n"))

  -- | Print a message.
  showWarning :: String -> m ()

  -- | Print a warning message when verbosity satisfies predicate.
  showWarningWhen :: (Int -> Bool) -> String -> m ()
  showWarningWhen p m = whenVerbosity p $ showWarning m


instance (Applicative m, MonadIO m) => MonadVerbosity (ReaderT (Handle, Int) m) where
  getVerbosity = snd <$> ask
  getLogFunction  = do
    (h,v) <- ask
    return $ \n msg -> do
      when (n < v) $ liftIO $ hPutStr h msg
  showWarning msg = do
    (h, _) <- ask
    liftIO $ hPutStrLn h msg

withVerbosity :: Handle
              -> Int
              -> (forall m. MonadVerbosity m => m a)
              -> IO a
withVerbosity h v f = runReaderT f (h,v)
