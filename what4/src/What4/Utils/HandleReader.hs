module What4.Utils.HandleReader where

import           Data.Text (Text)
import qualified Data.Text.Lazy as LazyText
import qualified Data.Text.IO as Text
import           Control.Exception(bracket,catch)
import           Control.Concurrent(ThreadId,forkIO,killThread)
import           Control.Concurrent.Chan(Chan,newChan,readChan,writeChan)
import           System.IO(Handle,hPutStrLn,stderr,hClose)
import           System.IO.Error(isEOFError,ioeGetErrorType)

{- | Wrapper to help with reading from another process's
     standard out and stderr.

We want to be able to read from another process's stderr and stdout without
causing the process to stall because 'stdout' or 'stderr' becomes full.  This
data type will read from either of the handles, and buffer as much data
as needed in the queue.  It then provides a line-based method for reading
that data as strict bytestrings. -}
data HandleReader = HandleReader { hrChan :: !(Chan (Maybe Text))
                                 , hrHandle :: !Handle
                                 , hrThreadId :: !ThreadId
                                 }

streamLines :: Chan (Maybe Text) -> Handle -> IO ()
streamLines c h = do
  ln <- Text.hGetLine h
  writeChan c (Just ln)
  streamLines c h

-- | Create a new handle reader for reading the given handle.
startHandleReader :: Handle -> IO HandleReader
startHandleReader h = do
  c <- newChan
  let handle_err e
        | isEOFError e = do
            writeChan c Nothing
        | otherwise = do
            hPutStrLn stderr $ show (ioeGetErrorType e)
            hPutStrLn stderr $ show e
  tid <- forkIO $ streamLines c h `catch` handle_err

  return $! HandleReader { hrChan     = c
                         , hrHandle   = h
                         , hrThreadId = tid
                         }


-- | Stop the handle reader; cannot be used afterwards.
stopHandleReader :: HandleReader -> IO ()
stopHandleReader hr = do
  killThread (hrThreadId hr)
  hClose (hrHandle hr)

-- | Run an execution with a handle reader and stop it wheen down
withHandleReader :: Handle -> (HandleReader -> IO a) -> IO a
withHandleReader h = bracket (startHandleReader h) stopHandleReader

readNextLine :: HandleReader -> IO (Maybe Text)
readNextLine hr = do
  mr <- readChan (hrChan hr)
  case mr of
    -- Write back 'Nothing' because thread should have terminated.
    Nothing -> writeChan (hrChan hr) Nothing
    Just{} -> return()
  return mr

readAllLines :: HandleReader -> IO LazyText.Text
readAllLines hr = go LazyText.empty
  where go :: LazyText.Text -> IO LazyText.Text
        go prev = do
          mr <- readNextLine hr
          case mr of
            Nothing -> return prev
            Just e -> go $! prev `LazyText.append` (LazyText.fromStrict e)
                                 `LazyText.snoc` '\n'


