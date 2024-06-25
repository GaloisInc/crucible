module Lang.Crucible.Utils.Timeout
  ( Timeout(..)
  , TimedOut(..)
  , withTimeout
  ) where

import qualified Control.Concurrent as CC
import qualified Control.Concurrent.Async as CCA

import qualified Lang.Crucible.Utils.Seconds as Secs

-- | A timeout, in seconds.
newtype Timeout = Timeout { getTimeout :: Secs.Seconds }
  deriving (Eq, Ord, Show)

-- Private, not exported
timeoutToMicros :: Timeout -> Int
timeoutToMicros = Secs.secondsToMicroseconds . getTimeout

-- | A task timed out.
data TimedOut = TimedOut
  deriving Show

-- | Execute a task with a timeout.
--
-- Implemented via 'CCA.race', so re-throws exceptions that occur during the
-- task (if it completes before the timeout).
withTimeout ::
  -- | Timeout duration (seconds)
  Timeout ->
  -- | Task to attempt
  IO a ->
  IO (Either TimedOut a)
withTimeout to task = do
  let timeout = do
        CC.threadDelay (timeoutToMicros to)
        pure TimedOut
  CCA.race timeout task
