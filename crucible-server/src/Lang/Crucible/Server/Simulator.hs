-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.Simulator
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- State-management datastructures and functions for interfacing with
-- the main crucible simulator.
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
module Lang.Crucible.Server.Simulator where

import           Control.Exception
import           Control.Lens
import           Control.Monad.IO.Class
import           Data.Hashable
import qualified Data.HashTable.IO as HIO
import           Data.IORef
import qualified Data.Map as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Text.Encoding (decodeUtf8)
import           System.IO.Error

import           GHC.Generics
import           GHC.IO.Handle


import           Data.HPB
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce (indexValue)
import           Data.Parameterized.Some

import           What4.Config
import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator
import           Lang.Crucible.Simulator.ExecutionTree (stateTree, activeFrames, filterCrucibleFrames)
import           Lang.Crucible.Simulator.Operations( abortExec )
import           Lang.Crucible.Server.CallbackOutputHandle
import           Lang.Crucible.Server.TypeConv

import           Lang.Crucible.Types
import qualified Lang.Crucible.Proto as P


------------------------------------------------------------------------
-- PredefinedHandle

data PredefinedHandle
   = SymbolicHandle ![Int] !(Some BaseTypeRepr)
   | NamedPredefHandle !FunctionName
   | PrintTermHandle !(Some TypeRepr)
   | MultiPartLoadHandle !Int !Int !Int
   | MultiPartStoreHandle !Int !Int !Int
  deriving (Eq, Generic)

instance Hashable PredefinedHandle where

------------------------------------------------------------------------
-- Simulator

-- | The simulator contains the state associated with the crucible-server
-- interface.
data Simulator p sym
   = Simulator { simContext      :: !(IORef (SimContext p sym ()))
               , requestHandle   :: !Handle
               , responseHandle  :: !Handle
                 -- | Maps handle ids to the associated handle.
               , handleCache     :: !(IORef (Map.Map Word64 SomeHandle))
                 -- | Maps predefined handles to associated handle.
               , predefinedHandles ::
                   !(HIO.BasicHashTable PredefinedHandle SomeHandle)
               , simValueCache :: !(HIO.BasicHashTable Word64 (Some (RegEntry sym)))
               , simValueCounter :: !(IORef Word64)
               , simExecFeatures :: [GenericExecutionFeature sym]
               }

getSimContext :: Simulator p sym -> IO (SimContext p sym ())
getSimContext sim = readIORef (simContext sim)

getHandleAllocator :: Simulator p sym -> IO HandleAllocator
getHandleAllocator sim = simHandleAllocator <$> getSimContext sim

getInterface :: Simulator p sym -> IO sym
getInterface sim = (^.ctxSymInterface) <$> getSimContext sim

-- | Create a new Simulator interface
newSimulator :: IsSymInterface sym
             => sym
             -> [ConfigDesc]
             -> p
             -> [GenericExecutionFeature sym]
                  -- ^ Execution features to install in the simulator
             -> [Simulator p sym -> IO SomeHandle] -- ^ Predefined function handles to install
             -> Handle
                -- ^ Handle for reading requests.
             -> Handle
                -- ^ Handle for writing responses.
             -> IO (Simulator p sym)
newSimulator sym opts p execFeats hdls request_handle response_handle = do
  let cb = OutputCallbacks { devCallback = \s -> do
                               sendPrintValue response_handle (decodeUtf8 s)
                           , devClose = return ()
                           }
  h <- mkCallbackOutputHandle "crucible-server" cb

  withHandleAllocator $ \halloc -> do

  let bindings = emptyHandleMap
  let extImpl :: ExtensionImpl p sym ()
      extImpl = ExtensionImpl (\_sym _iTypes _logFn _f x -> case x of) (\x -> case x of)

  -- add relevant configuration options
  extendConfig opts (getConfiguration sym)

  -- Create new context
  ctxRef <- newIORef $
    initSimContext sym MapF.empty halloc h bindings extImpl p

  hc <- newIORef Map.empty
  ph <- HIO.new
  svc <- HIO.new
  svCounter <- newIORef 0

  let sim =
         Simulator { simContext = ctxRef
                   , requestHandle = request_handle
                   , responseHandle = response_handle
                   , handleCache = hc
                   , predefinedHandles = ph
                   , simValueCache = svc
                   , simValueCounter = svCounter
                   , simExecFeatures = execFeats
                   }
  populatePredefHandles sim hdls ph
  return sim

populatePredefHandles :: IsSymInterface sym
                      => Simulator p sym
                      -> [Simulator p sym -> IO SomeHandle]
                      -> HIO.BasicHashTable PredefinedHandle SomeHandle
                      -> IO ()
populatePredefHandles _ [] _ = return ()
populatePredefHandles s (mkh : hs) ph = do
   SomeHandle h <- mkh s
   HIO.insert ph (NamedPredefHandle (handleName h)) (SomeHandle h)
   populatePredefHandles s hs ph

mkPredef :: (KnownCtx TypeRepr  args, KnownRepr TypeRepr ret, IsSymInterface sym)
         => Override p sym () args ret
         -> Simulator p sym
         -> IO SomeHandle
mkPredef ovr s = SomeHandle <$> simOverrideHandle s knownRepr knownRepr ovr

handleRef :: FnHandle args tp -> Word64
handleRef h = indexValue (handleID h)

-- | Create a handle associated with given arguments, and ensure simulator
-- can find it when given index.
simMkHandle :: Simulator p sim
            -> FunctionName
            -> CtxRepr args
            -> TypeRepr tp
            -> IO (FnHandle args tp)
simMkHandle sim nm args tp = do
  halloc <- getHandleAllocator sim
  h <- mkHandle' halloc nm args tp
  modifyIORef' (handleCache sim) $ Map.insert (handleRef h) (SomeHandle h)
  return h

getHandleBinding :: Simulator p sym -> Word64 -> IO SomeHandle
getHandleBinding sim r = do
  ms <- readIORef (handleCache sim)
  case Map.lookup r ms of
    Just s -> return s
    Nothing -> fail $ "The index " ++ show r ++ " is not associated with a known handle."

-- | Get a predefined handle associated with the entry.
getPredefinedHandle :: Simulator p sym
                    -> PredefinedHandle
                    -> IO SomeHandle -- Function to create handle (if needed).
                    -> IO SomeHandle
getPredefinedHandle sim predef fallback = do
  let tbl = predefinedHandles sim
  mh <- HIO.lookup tbl predef
  case mh of
    Just h -> return h
    Nothing -> do
      h <- fallback
      -- Associate predef with handle for caching.
      HIO.insert tbl predef h
      return h

-- | Send response to crucible-server.
sendResponse :: HasMessageRep a => Simulator p sym -> a -> IO ()
sendResponse sim resp = putDelimited (responseHandle sim) resp

toProtoHandleInfo :: FnHandle args rtp -> P.HandleInfo
toProtoHandleInfo h
  = mempty
  & P.handleInfo_display_name .~ fromString (show (handleName h))
  & P.handleInfo_arg_types    .~ mkProtoTypeSeq (handleArgTypes h)
  & P.handleInfo_return_type  .~ mkProtoType (handleReturnType h)

-- | Send a response with a predefined handle.
sendPredefinedHandleResponse :: Simulator p sym -> FnHandle args rtp -> IO ()
sendPredefinedHandleResponse sim h = do
  -- Sent response with value and info
  let resp = mempty
           & P.predefinedHandleInfo_ref  .~ handleRef h
           & P.predefinedHandleInfo_info .~ toProtoHandleInfo h
  let gresp = mempty
            & P.genericResponse_code .~ P.PredefHandleGenResp
            & P.genericResponse_predefHandleResponse .~ resp
  sendResponse sim gresp

-- | Respond to a request for a predefined handle.
respondToPredefinedHandleRequest :: Simulator p sym -> PredefinedHandle -> IO SomeHandle -> IO ()
respondToPredefinedHandleRequest sim predef fallback = do
  SomeHandle h <- getPredefinedHandle sim predef fallback
  sendPredefinedHandleResponse sim h

-- Associate a function with the given handle.
bindHandleToFunction :: Simulator p sym
                     -> FnHandle args ret
                     -> FnState p sym () args ret
                     -> IO ()
bindHandleToFunction sim h s =
  modifyIORef' (simContext sim) $
    functionBindings %~ insertHandleMap h s

simOverrideHandle :: Simulator p sym
                  -> CtxRepr args
                  -> TypeRepr tp
                  -> Override p sym () args tp
                  -> IO (FnHandle args tp)
simOverrideHandle sim args ret o = do
  h <- simMkHandle sim (overrideName o) args ret
  -- Add override to state.
  bindHandleToFunction sim h (UseOverride o)
  return h


sendExceptionResponse :: Simulator p sym
                      -> SomeException
                      -> IO ()
sendExceptionResponse sim ex = do
  let msg = case fromException ex of
              Just ioex | isUserError ioex -> Text.pack $ ioeGetErrorString ioex
              _ -> Text.pack $ displayException ex
  let gresp = mempty
            & P.genericResponse_code .~ P.ExceptionGenResp
            & P.genericResponse_message .~ msg
  sendResponse sim gresp


sendCallResponse :: Simulator p sym
                 -> P.CallResponse
                 -> IO ()
sendCallResponse sim cresp = do
  let gresp = mempty
            & P.genericResponse_code .~ P.CallGenResp
            & P.genericResponse_callResponse .~ cresp
  sendResponse sim gresp

sendAckResponse :: Simulator p sym
                -> IO ()
sendAckResponse sim =
  sendResponse sim (mempty & P.genericResponse_code .~ P.AcknowledgementResp)

sendCallReturnValue :: IsSymInterface sym
                    => Simulator p sym
                    -> P.Value --RegEntry sym tp
                    -> IO ()
sendCallReturnValue sim pv = do
  --pv <- toProtoValue sim v
  sendCallResponse sim $ mempty & P.callResponse_code .~ P.CallReturnValue
                                & P.callResponse_returnVal .~ pv

sendCallAllAborted :: Simulator p sym -> IO ()
sendCallAllAborted sim = do
  sendCallResponse sim $ mempty & P.callResponse_code    .~ P.CallAllAborted

sendTextResponse :: Simulator p sym
                 -> Text
                 -> IO ()
sendTextResponse sim msg = sendPrintValue (responseHandle sim) msg

-- | Send message to print value.
sendPrintValue :: Handle -> Text -> IO ()
sendPrintValue h msg = do
  putDelimited h $ mempty & P.genericResponse_code .~ P.PrintGenResp
                          & P.genericResponse_message .~ msg

sendCallPathAborted :: Simulator p sym
                    -> P.PathAbortedCode
                    -> String
                    -> [ProgramLoc]
                    -> IO ()
sendCallPathAborted sim code msg bt = do
  let ps = Seq.fromList $ map toProtoPos bt
  let abortMsg = mempty & P.pathAbortedMessage_code    .~ code
                        & P.pathAbortedMessage_message .~ fromString msg
                        & P.pathAbortedMessage_backtraces .~ ps
  sendCallResponse sim $ mempty & P.callResponse_code       .~ P.CallPathAborted
                                & P.callResponse_message    .~ abortMsg

serverErrorHandler :: IsSymInterface sym
                   => Simulator p sym
                   -> AbortHandler p sym () rtp
serverErrorHandler sim = AH $ \e ->
 do t <- view stateTree
    let frames = activeFrames t
    -- Get location of frame.
    let loc = mapMaybe filterCrucibleFrames frames
    -- let msg = ppExceptionContext frames e

    -- If a branch aborted becasue of an error condition,
    -- tell client that a part aborted with the given message.
    liftIO $
      case e of
        AssumedFalse (AssumingNoError se) ->
          case simErrorReason se of
            ReadBeforeWriteSimError msg -> do
              sendCallPathAborted sim P.AbortedReadBeforeWrite (show msg) loc
            AssertFailureSimError msg _details -> do
              sendCallPathAborted sim P.AbortedUserAssertFailure (show msg) loc
            _ -> do
              sendCallPathAborted sim P.AbortedGeneric (show (simErrorReason se)) loc

        -- In other cases, do nothing
        _ -> return ()

    -- Abort execution.
    abortExec e
