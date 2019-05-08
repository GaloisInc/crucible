
module What4.Utils.HandleReader where

import           Control.Monad (unless)
import           Data.IORef
import           Data.Semigroup ( (<>) )
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LazyText
import qualified Data.Text.IO as Text
import           Control.Exception(bracket,catch)
import           Control.Concurrent(ThreadId,forkIO,killThread)
import           Control.Concurrent.Chan(Chan,newChan,readChan,writeChan)
import           System.IO(Handle,hPutStrLn,stderr,hClose)
import           System.IO.Error(isEOFError,ioeGetErrorType)
import           System.IO.Streams( OutputStream, InputStream )
import qualified System.IO.Streams as Streams


teeInputStream :: InputStream a -> OutputStream a -> IO (InputStream a)
teeInputStream i o = Streams.makeInputStream go
  where
  go = do x <- Streams.read i
          Streams.write x o
          return x

teeOutputStream :: OutputStream a -> OutputStream a -> IO (OutputStream a)
teeOutputStream o aux = Streams.makeOutputStream go
  where
  go x =
    do Streams.write x aux
       Streams.write x o

lineBufferedOutputStream :: Text -> OutputStream Text -> IO (OutputStream Text)
lineBufferedOutputStream prefix out =
    do ref <- newIORef mempty
       Streams.makeOutputStream (con ref)
 where
 newl = Text.pack "\n"

 con ref mx =
   do start <- readIORef ref
      case mx of
        Nothing ->
          do unless (Text.null start) (Streams.write (Just (prefix <> start)) out)
             Streams.write Nothing out
        Just x -> go ref (start <> x)

 go ref x =
   let (ln, x') = Text.break (== '\n') x in
   if Text.null x' then
     -- Flush
     do Streams.write (Just mempty) out
        writeIORef ref x
   else
     do Streams.write (Just (prefix <> ln <> newl)) out
        go ref (Text.drop 1 x')

demuxProcessHandles ::
  Handle {- ^ stdin for process -} ->
  Handle {- ^ stdout for process -} ->
  Handle {- ^ stderr for process -} ->
  Maybe (Text, Handle) {- optional handle to echo ouput; text argument is a line-comment prefix  -} ->
  IO ( OutputStream Text, InputStream Text, HandleReader )
demuxProcessHandles in_h out_h err_h Nothing =
  do in_str  <- Streams.encodeUtf8 =<< Streams.handleToOutputStream in_h
     out_str <- Streams.decodeUtf8 =<< Streams.handleToInputStream out_h
     err_reader <- startHandleReader err_h Nothing
     return (in_str, out_str, err_reader)
demuxProcessHandles in_h out_h err_h (Just (comment_prefix, aux_h)) =
  do aux_str <- Streams.lockingOutputStream =<< Streams.encodeUtf8 =<< Streams.handleToOutputStream aux_h
     in_str  <- Streams.encodeUtf8 =<< Streams.handleToOutputStream in_h
     out_str <- Streams.decodeUtf8 =<< Streams.handleToInputStream out_h

     in_aux <- lineBufferedOutputStream mempty aux_str
     in_str' <- teeOutputStream in_str in_aux

     out_aux <- lineBufferedOutputStream comment_prefix aux_str
     out_str' <- teeInputStream out_str out_aux

     err_reader <- startHandleReader err_h . Just
                    =<< lineBufferedOutputStream comment_prefix aux_str

     return (in_str', out_str', err_reader)


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

streamLines :: Chan (Maybe Text) -> Handle -> Maybe (OutputStream Text) -> IO ()
streamLines c h Nothing = go
 where
 go = do ln <- Text.hGetLine h
         writeChan c (Just ln)
         go
streamLines c h (Just auxstr) = go
 where
 go = do ln <- Text.hGetLine h
         Streams.write (Just ln) auxstr
         writeChan c (Just ln)
         go

-- | Create a new handle reader for reading the given handle.
startHandleReader :: Handle -> Maybe (OutputStream Text) -> IO HandleReader
startHandleReader h auxOutput = do
  c <- newChan
  let handle_err e
        | isEOFError e = do
            writeChan c Nothing
        | otherwise = do
            hPutStrLn stderr $ show (ioeGetErrorType e)
            hPutStrLn stderr $ show e
  tid <- forkIO $ streamLines c h auxOutput `catch` handle_err

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
withHandleReader :: Handle -> Maybe (OutputStream Text) -> (HandleReader -> IO a) -> IO a
withHandleReader h auxOut = bracket (startHandleReader h auxOut) stopHandleReader

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
