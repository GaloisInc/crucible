{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Main (main) where

import           Control.Exception
import           Control.Lens
import           Control.Monad
import qualified Data.Text as Text
import           GHC.IO.Handle
import           System.Exit
import           System.IO

import           Data.HPB

import           Data.Parameterized.Nonce

import           What4.InterpretedFloatingPoint (FloatModeRepr(..))

import           Lang.Crucible.Backend.Simple
import qualified Lang.Crucible.Backend.SAWCore as SAW
import           Lang.Crucible.Simulator.PathSatisfiability

import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Server.Requests
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.SAWOverrides
import           Lang.Crucible.Server.Verification.Override(SAWBack)
import           Lang.Crucible.Server.SimpleOverrides

import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Prelude as SAW
import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

main :: IO ()
main = do
  -- Check that standard input and output are not terminals.
  stdInputIsTerm <- hIsTerminalDevice stdin
  stdOutputIsTerm <- hIsTerminalDevice stdout
  when (stdInputIsTerm || stdOutputIsTerm) $ do
    logMsg $
      "crucible-server is not intended to be run directly, but rather\n"
      ++ "called by another process."
    exitFailure
  logMsg "Starting crucible-server"
  hSetBinaryMode stdout True
  hSetBuffering stdout (BlockBuffering Nothing)
  runSimulator stdin stdout
  hFlush stdout

-- | No interesting state needs to be threaded through
--   the crucible server...
data CrucibleServerPersonality sym = CrucibleServerPersonality

runSimulator :: Handle -> Handle -> IO ()
runSimulator hin hout = do
  handshake <- getDelimited hin
  let backend = handshake^.P.handShakeRequest_backend
  catch
    (case backend of
       P.SAWBackend -> do
         logMsg $ "Starting SAW server..."
         runSAWSimulator hin hout
       P.SimpleBackend -> do
         logMsg $ "Starting Simple server..."
         runSimpleSimulator hin hout
    )
    (\(ex::SomeException) ->
       do let msg = Text.pack $ displayException ex
          let err_resp = mempty
                & P.handShakeResponse_code .~ P.HandShakeError
                & P.handShakeResponse_message .~ msg
          putDelimited hout err_resp
    )

runSAWSimulator :: Handle -> Handle -> IO ()
runSAWSimulator hin hout =
  do let ok_resp = mempty
                   & P.handShakeResponse_code .~ P.HandShakeOK
     withIONonceGenerator $ \gen -> do
       sc <- SAW.mkSharedContext
       SAW.scLoadPreludeModule sc
       CryptolSAW.scLoadCryptolModule sc
       (sym :: SAWBack n) <- SAW.newSAWCoreBackend FloatRealRepr sc gen
       sawState <- initSAWServerPersonality sym
       pathSatFeat <- pathSatisfiabilityFeature sym (SAW.considerSatisfiability sym)
       s <- newSimulator sym sawServerOptions sawState [pathSatFeat] sawServerOverrides hin hout
       putDelimited hout ok_resp
       -- Enter loop to start reading commands.
       fulfillRequests s sawBackendRequests

runSimpleSimulator :: Handle -> Handle -> IO ()
runSimpleSimulator hin hout = do
  withIONonceGenerator $ \gen -> do
    let ok_resp = mempty
                  & P.handShakeResponse_code .~ P.HandShakeOK
    sym <- newSimpleBackend gen FloatRealRepr
    s <- newSimulator sym simpleServerOptions CrucibleServerPersonality [] simpleServerOverrides hin hout
    -- Enter loop to start reading commands.
    putDelimited hout ok_resp
    fulfillRequests s simpleBackendRequests
