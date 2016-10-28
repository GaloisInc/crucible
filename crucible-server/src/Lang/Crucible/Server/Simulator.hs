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

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
module Lang.Crucible.Server.Simulator where

#if !MIN_VERSION_base(4,8,0)
import           Control.Applicative
#endif
import           Control.Exception
import           Control.Lens
import           Control.Monad.ST (RealWorld, stToIO)
import           Data.Hashable
import qualified Data.HashTable.IO as HIO
import           Data.IORef
import qualified Data.Map as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Text.Encoding (decodeUtf8)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           GHC.Generics
import           GHC.IO.Handle


import           Data.HPB
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce.Unsafe (indexValue)
import           Data.Parameterized.Some

import           Lang.Crucible.Config
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..), frameProgramLoc)
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.MSSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Server.CallbackOutputHandle
import           Lang.Crucible.Server.TypeConv
import           Lang.Crucible.Solver.Interface
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
data Simulator sym
   = Simulator { simContext      :: !(IORef (SimContext sym))
               , requestHandle   :: !Handle
               , responseHandle  :: !Handle
                 -- | Maps handle ids to the associated handle.
               , handleCache     :: !(IORef (Map.Map Word64 SomeHandle))
                 -- | Maps predefined handles to associated handle.
               , predefinedHandles ::
                   !(HIO.BasicHashTable PredefinedHandle SomeHandle)
               , simValueCache :: !(HIO.BasicHashTable Word64 (Some (RegEntry sym)))
               , simValueCounter :: !(IORef Word64)
               }

getSimContext :: Simulator sym -> IO (SimContext sym)
getSimContext sim = readIORef (simContext sim)

getHandleAllocator :: Simulator sym -> IO (HandleAllocator RealWorld)
getHandleAllocator sim = simHandleAllocator <$> getSimContext sim

getInterface :: Simulator sym -> IO sym
getInterface sim = (^.ctxSymInterface) <$> getSimContext sim

-- | Create a new Simulator interface
newSimulator :: IsSymInterface sym
             => sym
             -> [ConfigDesc (SimConfigMonad sym)] -- ^ Options to use
             -> [Simulator sym -> IO SomeHandle] -- ^ Predefined function handles to install
             -> Handle
                -- ^ Handle for reading requests.
             -> Handle
                -- ^ Handle for writing responses.
             -> IO (Simulator sym)
newSimulator sym opts hdls request_handle response_handle = do
  let cb = OutputCallbacks { devCallback = \s -> do
                               sendPrintValue response_handle (decodeUtf8 s)
                           , devClose = return ()
                           }
  h <- mkCallbackOutputHandle "crucible-server" cb

  let initVerbosity = 0
  cfg <- initialConfig initVerbosity opts

  withHandleAllocator $ \halloc -> do

  let bindings = emptyHandleMap
  -- Create new context
  ctxRef <- newIORef $
    initSimContext sym MapF.empty cfg halloc h bindings

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
                   }
  populatePredefHandles sim hdls ph
  return sim

populatePredefHandles :: IsSymInterface sym
                      => Simulator sym
                      -> [Simulator sym -> IO SomeHandle]
                      -> HIO.BasicHashTable PredefinedHandle SomeHandle
                      -> IO ()
populatePredefHandles _ [] _ = return ()
populatePredefHandles s (mkh : hs) ph = do
   SomeHandle h <- mkh s
   HIO.insert ph (NamedPredefHandle (handleName h)) (SomeHandle h)
   populatePredefHandles s hs ph

mkPredef :: (KnownCtx TypeRepr  args, KnownRepr TypeRepr ret, IsSymInterface sym)
         => Override sym args ret
         -> Simulator sym
         -> IO SomeHandle
mkPredef ovr s = SomeHandle <$> simOverrideHandle s knownRepr knownRepr ovr

handleRef :: FnHandle args tp -> Word64
handleRef h = indexValue (handleID h)

-- | Create a handle associated with given arguments, and ensure simulator
-- can find it when given index.
simMkHandle :: Simulator sim
            -> FunctionName
            -> CtxRepr args
            -> TypeRepr tp
            -> IO (FnHandle args tp)
simMkHandle sim nm args tp = do
  halloc <- getHandleAllocator sim
  h <- stToIO $ mkHandle' halloc nm args tp
  modifyIORef' (handleCache sim) $ Map.insert (handleRef h) (SomeHandle h)
  return h

getHandleBinding :: Simulator sym -> Word64 -> IO SomeHandle
getHandleBinding sim r = do
  ms <- readIORef (handleCache sim)
  case Map.lookup r ms of
    Just s -> return s
    Nothing -> fail $ "The index " ++ show r ++ " is not associated with a known handle."

-- | Get a predefined handle associated with the entry.
getPredefinedHandle :: Simulator sym
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
sendResponse :: HasMessageRep a => Simulator sym -> a -> IO ()
sendResponse sim resp = putDelimited (responseHandle sim) resp

toProtoHandleInfo :: FnHandle args rtp -> P.HandleInfo
toProtoHandleInfo h
  = mempty
  & P.handleInfo_display_name .~ fromString (show (handleName h))
  & P.handleInfo_arg_types    .~ mkProtoTypeSeq (handleArgTypes h)
  & P.handleInfo_return_type  .~ mkProtoType (handleReturnType h)

-- | Send a response with a predefined handle.
sendPredefinedHandleResponse :: Simulator sym -> FnHandle args rtp -> IO ()
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
respondToPredefinedHandleRequest :: Simulator sym -> PredefinedHandle -> IO SomeHandle -> IO ()
respondToPredefinedHandleRequest sim predef fallback = do
  SomeHandle h <- getPredefinedHandle sim predef fallback
  sendPredefinedHandleResponse sim h

-- Associate a function with the given handle.
bindHandleToFunction :: Simulator sym
                     -> FnHandle args ret
                     -> FnState sym args ret
                     -> IO ()
bindHandleToFunction sim h s =
  modifyIORef' (simContext sim) $
    functionBindings %~ insertHandleMap h s

simOverrideHandle :: Simulator sym
                  -> CtxRepr args
                  -> TypeRepr tp
                  -> Override sym args tp
                  -> IO (FnHandle args tp)
simOverrideHandle sim args ret o = do
  h <- simMkHandle sim (overrideName o) args ret
  -- Add override to state.
  bindHandleToFunction sim h (UseOverride o)
  return h


sendExceptionResponse :: Simulator sym
                      -> SomeException
                      -> IO ()
sendExceptionResponse  sim ex = do
  let gresp = mempty
            & P.genericResponse_code .~ P.ExceptionGenResp
            & P.genericResponse_message .~ (Text.pack $ show ex)
  sendResponse sim gresp

sendCallResponse :: Simulator sym
                 -> P.CallResponse
                 -> IO ()
sendCallResponse sim cresp = do
  let gresp = mempty
            & P.genericResponse_code .~ P.CallGenResp
            & P.genericResponse_callResponse .~ cresp
  sendResponse sim gresp

sendCallReturnValue :: IsSymInterface sym
                    => Simulator sym
                    -> P.Value --RegEntry sym tp
                    -> IO ()
sendCallReturnValue sim pv = do
  --pv <- toProtoValue sim v
  sendCallResponse sim $ mempty & P.callResponse_code .~ P.CallReturnValue
                                & P.callResponse_returnVal .~ pv

sendCallAllAborted :: Simulator sym -> IO ()
sendCallAllAborted sim = do
  sendCallResponse sim $ mempty & P.callResponse_code    .~ P.CallAllAborted

-- | Send message to print value.
sendPrintValue :: Handle -> Text -> IO ()
sendPrintValue h msg = do
  putDelimited h $ mempty & P.genericResponse_code .~ P.PrintGenResp
                          & P.genericResponse_message .~ msg

sendCallPathAborted :: Simulator sym
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
                   => Simulator sym
                   -> ErrorHandler SimContext sym rtp
serverErrorHandler sim = EH $ \e s -> do
    let t = s^.simTree
    let frames = activeFrames t
    -- Get location of frame.
    let loc = mapMaybe filterCrucibleFrames frames
    -- let msg = ppExceptionContext frames e

    -- Tell client that a part aborted with the given message.
    case simErrorReason e of
      ReadBeforeWriteSimError msg -> do
          sendCallPathAborted sim P.AbortedReadBeforeWrite (show msg) loc
      AssertFailureSimError msg -> do
          sendCallPathAborted sim P.AbortedUserAssertFailure (show msg) loc
      _ -> do
          sendCallPathAborted sim P.AbortedGeneric (show (simErrorReason e)) loc

    -- Abort execution.
    abortExec e s

------------------------------------
-- TODO move everything below here
-- into 'crucible'; delete corresponding
-- code from galois-mss/src/Verifier/MSS/OverrideSim

filterCrucibleFrames :: SomeFrame (SimFrame sym)
                     -> Maybe ProgramLoc
filterCrucibleFrames (SomeFrame (MF f)) = Just (frameProgramLoc f)
filterCrucibleFrames _ = Nothing

ppSimError :: SimError -> Doc
ppSimError er =
  vcat [ vcat (text <$> lines (show (simErrorReason er)))
       , text "in" <+> text (show (plFunction loc)) <+> text "at" <+> text (show (plSourceLoc loc))
       ]
 where loc = simErrorLoc er


-- | Print the exception
ppExceptionContext :: [SomeFrame (SimFrame sym)] -> SimError -> Doc
ppExceptionContext frames e =
  case frames of
    [_] -> ppSimError e
    SomeFrame (OF f):_ ->
        text ("When calling " ++ show nm ++ ":") <$$>
        indent 2 (ppSimError e)
      where nm = override f
    _ -> ppSimError e
