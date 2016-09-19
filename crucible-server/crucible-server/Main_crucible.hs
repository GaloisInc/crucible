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

import           Control.Lens
import           Control.Monad
import           GHC.IO.Handle
import           System.Exit
import           System.IO

import           Data.HPB

import           Data.Parameterized.Nonce

import           Lang.Crucible.Solver.SimpleBackend
import qualified Lang.Crucible.Solver.SAWCoreBackend as SAW

import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Server.Requests
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.SAWOverrides
import           Lang.Crucible.Server.SimpleOverrides

import qualified Verifier.SAW.Prelude as SAW

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

runSimulator :: Handle -> Handle -> IO ()
runSimulator hin hout = do
  handshake <- getDelimited hin
  let backend = handshake^.P.handShakeRequest_backend
  let ok_resp = mempty
           & P.handShakeResponse_code .~ P.HandShakeOK
--  let err_resp msg = mempty
--           & P.handShakeResponse_code .~ P.HandShakeError
--           & P.handShakeResponse_message .~ (Text.pack msg)
  case backend of
    P.SAWBackend -> do
       putDelimited hout ok_resp
       logMsg $ "Starting SAW server..."
       runSAWSimulator hin hout
    P.SimpleBackend -> do
       putDelimited hout ok_resp
       logMsg $ "Starting Simple server..."
       runSimpleSimulator hin hout


runSAWSimulator :: Handle -> Handle -> IO ()
runSAWSimulator hin hout =
  SAW.withSAWCoreBackend SAW.preludeModule $ \(sym :: SAW.SAWCoreBackend n) -> do
    s <- newSimulator sym [] [] hin hout
    -- Enter loop to start reading commands.
    fulfillRequests s sawBackendRequests

runSimpleSimulator :: Handle -> Handle -> IO ()
runSimpleSimulator hin hout = do
  withIONonceGenerator $ \gen -> do
    sym <- newSimpleBackend gen
    s <- newSimulator sym simpleServerOptions simpleServerOverrides hin hout
    -- Enter loop to start reading commands.
    fulfillRequests s simpleBackendRequests
