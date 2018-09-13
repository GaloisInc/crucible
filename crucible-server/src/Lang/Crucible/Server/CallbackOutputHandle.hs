-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.CallbackOutputHandle
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Utility for making an I/O handle from a collection of callback
-- functions.
------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
module Lang.Crucible.Server.CallbackOutputHandle
  ( OutputCallbacks(..)
  , mkCallbackOutputHandle
  ) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as B
import Data.Typeable
import Foreign.ForeignPtr
import Foreign.Marshal.Utils
import Foreign.Ptr
import GHC.IO.Buffer
import GHC.IO.BufferedIO
import GHC.IO.Device
import GHC.IO.Handle
import System.IO

-- | Callbacks for writing to file.
data OutputCallbacks
   = OutputCallbacks { devCallback :: !(B.ByteString -> IO ())
                       -- ^ Function to call when buffer flushes.
                     , devClose :: !(IO ())
                       -- ^ Function to call when device closes.
                     }
 deriving (Typeable)

instance IODevice OutputCallbacks where
  ready _ isWrite _ = return isWrite
  close d = devClose d
  devType _ = return Stream


instance BufferedIO OutputCallbacks where
  newBuffer _ = newByteBuffer 4096
  fillReadBuffer = error "Output device does not support reading."
  fillReadBuffer0 =  error "Output device does not support reading."
  flushWriteBuffer md buf = do
    -- Get offset of start of buffer.
    let offset = bufL buf
    -- Get length of offer
    let l = bufferElems buf
    -- Create bytestring with copy of data.
    bs <- B.create l $ \p -> do
      withForeignPtr (bufRaw buf) $ \src -> do
        copyBytes p (src `plusPtr` offset) l
    -- Send output to callback function.
    devCallback md bs
    -- Return empty buffer.
    return buf { bufL = 0
               , bufR = 0
               }

  flushWriteBuffer0 md buf = do
    buf' <- flushWriteBuffer md buf
    return (bufferElems buf, buf')

-- | A handle that can receive output and call a callback function.
mkCallbackOutputHandle :: FilePath -- ^ "FilePath" used in debug messages.
                       -> OutputCallbacks
                          -- ^ Functions to call when using device.
                       -> IO Handle
mkCallbackOutputHandle path callback = do
  let encoding = Nothing
  mkFileHandle callback path AppendMode encoding noNewlineTranslation
