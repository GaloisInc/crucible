module CrucibleProtobufTrace.GlobalEncodingState
    (
        protobufMessagesRef,
        addProtobufTraceEvent,
        writeOutProtobufTrace,
        getOutDirRef,
        setOutDirRef
    )
where


import Data.IORef
import System.IO.Unsafe
import CrucibleProtobufTrace.ProtoDefs.OperationTrace as ProtoOT
import Data.ProtoLens
import Lens.Micro
import Data.ByteString (ByteString, putStrLn)
import qualified Data.ByteString as SB


protobufMessagesRef :: IORef [ProtoOT.TraceEvent]
protobufMessagesRef = unsafePerformIO $ newIORef []
{-# NOINLINE protobufMessagesRef #-}

outDirRef :: IORef (Maybe FilePath)
outDirRef = unsafePerformIO $ newIORef Nothing
{-# NOINLINE outDirRef #-}

setOutDirRef :: FilePath -> IO ()
setOutDirRef = atomicWriteIORef outDirRef . Just

getOutDirRef :: IO FilePath
getOutDirRef = do
    m <- readIORef outDirRef
    case m of
        Nothing -> error "No output directory set"
        Just d -> return d

addProtobufTraceEvent :: ProtoOT.TraceEvent -> IO ()
addProtobufTraceEvent msg = do
    let ref = protobufMessagesRef
    -- Prelude.putStrLn ("Logging protobuf message: " ++ show msg)
    atomicModifyIORef' ref (\msgs -> (msg:msgs, ()))
    return ()

getFullProtobufTrace :: IO ProtoOT.OperationTrace
getFullProtobufTrace = do
    messages <- readIORef protobufMessagesRef
    let reordered_messages = reverse messages
    return $ defMessage & events .~ reordered_messages

getFullEncodedProtobufTrace :: IO ByteString
getFullEncodedProtobufTrace = encodeMessage <$> getFullProtobufTrace

writeOutProtobufTrace :: FilePath -> IO ()
writeOutProtobufTrace path = do
    trace <- getFullProtobufTrace
    Prelude.putStrLn ("Writing out protobuf trace to " ++ path)
    -- Prelude.putStrLn (showMessage trace)
    SB.writeFile path $ encodeMessage trace