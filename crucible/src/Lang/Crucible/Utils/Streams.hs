module Lang.Crucible.Utils.Streams
( logErrorStream
) where

import qualified Data.ByteString.UTF8 as UTF8
import qualified System.IO.Streams as Streams

-- | Write from output stream to a logging function.
logErrorStream :: Streams.InputStream UTF8.ByteString
               -> (String -> IO ()) -- ^ Logging function
               -> IO ()
logErrorStream err_stream logFn = do
  -- Have err_stream log complete lines to logLn
  let write_err Nothing = return ()
      write_err (Just b) = logFn b
  err_output <- Streams.makeOutputStream write_err
  lns <- Streams.map UTF8.toString =<< Streams.lines err_stream
  Streams.connect lns err_output
