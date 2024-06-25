module Lang.Crucible.Utils.Timeout
  ( Timeout(..)
  , TimeoutError(..)
  , withTimeout
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA
import           Control.Exception.Base (SomeException)

import qualified Lang.Crucible.Utils.Seconds as Secs

-- | A timeout, in seconds.
newtype Timeout = Timeout { getTimeout :: Secs.Seconds }
  deriving (Eq, Ord, Show)

-- Private, not exported
timeoutToMicros :: Timeout -> Int
timeoutToMicros = Secs.secondsToMicroseconds . getTimeout

-- Private, not exported
data DidTimeOut = DidTimeOut

-- | An error resulting from 'withTimeout'.
data TimeoutError
  = -- | The task timed out
    TimedOut
    -- | Some other exception ocurred
  | Exception SomeException
  deriving Show

-- | Execute a task with a timeout.
--
-- Catches any exceptions that occur during the task, returning them as
-- @'Left' ('Exception' exn)@.
withTimeout ::
  -- | Timeout duration (seconds)
  Timeout ->
  -- | Task to attempt
  IO a ->
  IO (Either TimeoutError a)
withTimeout to task = do
  worker <- CCA.async task
  timeout <- CCA.async $ do
    CC.threadDelay (timeoutToMicros to)
    CCA.cancel worker
    return DidTimeOut
  res <- CCA.waitEitherCatch timeout worker
  case res of
    Left (Right DidTimeOut) -> do
      return (Left TimedOut)
    Left (Left exn) -> do
      return (Left (Exception exn))
    Right (Left exn) -> do
      return (Left (Exception exn))
    Right (Right val) ->
      return (Right val)

