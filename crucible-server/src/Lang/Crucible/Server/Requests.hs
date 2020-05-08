-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.Requests
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Code for handling requests from clients.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Server.Requests
  ( logMsg
  , fulfillRequests
  , BackendSpecificRequests(..)
  ) where

#if !MIN_VERSION_base(4,13,0)
import Control.Monad.Fail( MonadFail )
#endif

import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad.State.Strict
import           Data.IORef
import           Data.Foldable (toList)
import           Data.Typeable
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Parameterized.Context as Ctx
import           System.Exit
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen
  ( displayIO
  , renderPretty
  , plain
  )

import           Data.HPB

import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some

import           What4.Config
import           What4.Concrete
import           What4.Interface

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Reg as R
import           Lang.Crucible.CFG.SSAConversion (toSSA)

import           Lang.Crucible.Backend
import           Lang.Crucible.FunctionName
import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import qualified Lang.Crucible.Simulator.Evaluation as Sim
import           Lang.Crucible.Simulator.EvalStmt (executeCrucible, genericToExecutionFeature)
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.MonadVerbosity

import           Lang.Crucible.Server.MultipartOperations
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.Translation
import           Lang.Crucible.Server.TypeConv
import           Lang.Crucible.Server.ValueConv

------------------------------------------------------------------------
-- Utilities

data CrucibleNotImplementedException
   = CrucibleNotImplemented String
 deriving (Show, Typeable)
instance Exception CrucibleNotImplementedException where

data FunctionNotFoundException
   = FunctionNotFound Text
 deriving (Show, Typeable)
instance Exception FunctionNotFoundException where


nyi :: String -> a
nyi nm = throw $ CrucibleNotImplemented (nm ++ " unimplemented.")

getHead :: MonadFail m => Seq a -> m (a, Seq a)
getHead s =
  case Seq.viewl s of
    Seq.EmptyL -> fail "Unexpected end of arguments."
    h Seq.:< t -> return (h, t)

logMsg :: String -> IO ()
logMsg = hPutStrLn stderr


fulfillUseCFGRequest :: IsSymInterface sym
                     => Simulator p sym
                     -> P.Cfg
                     -> IO ()
fulfillUseCFGRequest sim pg =
  unpackCFG sim pg $ \g -> do
  case toSSA g of
    C.SomeCFG g' ->
      do bindHandleToFunction sim (R.cfgHandle g) $! (UseCFG g' (postdomInfo g'))
         sendAckResponse sim

fulfillPrintCFGRequest :: IsSymInterface sym
                     => Simulator p sym
                     -> P.Cfg
                     -> IO ()
fulfillPrintCFGRequest sim pg =
  unpackCFG sim pg $ \g -> do
  h <- printHandle <$> readIORef (simContext sim)
  -- FIXME, implement pretty printer for register-CFGs
  case toSSA g of
    C.SomeCFG g' -> do
      displayIO h $ renderPretty 1.0 maxBound $ C.ppCFG False g'
      hFlush h
      sendAckResponse sim

------------------------------------------------------------------------
-- RunCall request

parseArgs :: IsSymInterface sym
          => Simulator p sym
          -> CtxRepr ctx
          -> Seq P.Value
          -> IO (Ctx.Assignment (RegEntry sym) ctx)
parseArgs sim types s =
  case Ctx.viewAssign types of
    Ctx.AssignEmpty -> do
      when (not (Seq.null s)) $ do
        fail $ "More arguments than expected."
      return Ctx.empty
    Ctx.AssignExtend c tp -> do
      case Seq.viewr s of
        s' Seq.:> v -> do
          Ctx.extend <$> parseArgs sim c s'
                     <*> (checkedRegEntry tp =<< fromProtoValue sim v)
        Seq.EmptyR -> fail "Expected more arguments"

fulfillRunCallRequest :: IsSymInterface sym
                      => Simulator p sym
                      -> P.Value
                      -> Seq P.Value
                      -> IO ()
fulfillRunCallRequest sim f_val encoded_args = do
  Some (RegEntry f_tp f) <- fromProtoValue sim f_val
  case f_tp of
    FunctionHandleRepr arg_types res_tp -> do
      args <- parseArgs sim arg_types encoded_args

      -- TODO: Redirect standard IO so that we can print messages.
      ctx <- readIORef (simContext sim)

      let simSt = InitialState ctx emptyGlobals (serverErrorHandler sim) res_tp
                    $ runOverrideSim res_tp (regValue <$> callFnVal f (RegMap args))
      -- Send messages to server with bytestring.
      fm <- getFloatMode (ctx^.ctxSymInterface)
      exec_res <- executeCrucible fm (map genericToExecutionFeature (simExecFeatures sim)) simSt
      case exec_res of
        FinishedResult ctx' (TotalRes (GlobalPair r _globals)) -> do
          writeIORef (simContext sim) $! ctx'
          sendCallReturnValue sim =<< toProtoValue sim r
        FinishedResult ctx' (PartialRes _ _ (GlobalPair r _globals) _) -> do
          writeIORef (simContext sim) $! ctx'
          sendCallReturnValue sim =<< toProtoValue sim r
        AbortedResult ctx' _ -> do
          writeIORef (simContext sim) $! ctx'
          sendCallAllAborted sim
        TimeoutResult exst -> do
          writeIORef (simContext sim) $! execStateContext exst
          sendCallAllAborted sim -- FIXME, this isn't really right...

    _ -> do
      sendCallPathAborted sim
             P.AbortedNonFunction
             "Could not interpret first argument as function."
             []
      sendCallAllAborted sim

------------------------------------------------------------------------
-- GetConfigValue request

fulfillGetConfigValueRequest
    :: IsSymInterface sym
    => Simulator p sym
       -- ^ Simulator to run.
    -> Text
       -- ^ Name of the configuration setting
    -> IO ()
fulfillGetConfigValueRequest sim nm =
  do ctx <- getSimContext sim
     let sym = ctx^.ctxSymInterface
         cfg = getConfiguration sym
     Some optSetting <- getOptionSettingFromText nm cfg
     getOption optSetting >>= \case
       Just v ->
         do e <- concreteToSym sym v
            pv <- toProtoValue sim (RegEntry (baseToType (concreteType v)) e)
            let resp =
                 mempty & P.simulatorValueResponse_successful .~ True
                        & P.simulatorValueResponse_value .~ pv
            let gresp =
                 mempty & P.genericResponse_code .~ P.SimulatorValueGenResp
                        & P.genericResponse_simValResponse .~ resp
            sendResponse sim gresp
       Nothing ->
         do let msg = "Config option " <> nm <> " is not set."
                gresp =
                  mempty & P.genericResponse_code .~ P.ExceptionGenResp
                         & P.genericResponse_message .~ msg
            sendResponse sim gresp

------------------------------------------------------------------------
-- SetConfigValue request

fulfillSetConfigValueRequest
    :: IsSymInterface sym
    => Simulator p sym
       -- ^ Simulator to run.
    -> Text
       -- ^ Name of the configuration setting
    -> Seq P.Value
       -- ^ Value of the configuration setting
    -> IO ()
fulfillSetConfigValueRequest sim nm vals =
  do ctx <- getSimContext sim
     let sym = ctx^.ctxSymInterface
         cfg = getConfiguration sym
     case Seq.viewl vals of
       val Seq.:< (Seq.null -> True) ->
         do Some (RegEntry tpr v) <- fromProtoValue sim val
            Some optSetting <- getOptionSettingFromText nm cfg
            let tpr' = baseToType (configOptionType (optionSettingName optSetting))
            case testEquality tpr tpr' of
              Just Refl
                | Just x <- asConcrete v ->
                    do res <- setOption optSetting x
                       case optionSetError res of
                         Just msg -> fail (show msg)
                         Nothing ->
                           do let ws = toList (optionSetWarnings res)
                              unless (null ws)
                                     (sendTextResponse sim (Text.unlines (map (Text.pack . show) ws)))
                              sendAckResponse sim

                | otherwise ->
                      fail $ unlines [ "Expected concrete value of type " ++ show tpr'
                                     , "but was given a symbolic value."
                                     ]

              Nothing   -> fail $ unlines [ "Expected value of type " ++ show tpr'
                                          , "when setting configuration value " ++ show nm
                                          , "but was given a value of type " ++ show tpr
                                          ]

       _ -> fail "Expected a single argument for SetConfigValue"

------------------------------------------------------------------------
-- SetVerbosity request

fulfillSetVerbosityRequest
    :: IsSymInterface sym
    => Simulator p sym
       -- ^ Simulator to run.
    -> Seq P.Value
       -- ^ Verbosity level to set
    -> IO ()
fulfillSetVerbosityRequest sim args = do
  unless (Seq.length args == 1)
         (fail "expected exactly one argument to SetVerbosity request")
  v <- fromProtoValue sim (Seq.index args 0)
  case v of
    Some (RegEntry NatRepr nv) | Just n <- asNat nv -> do
      ctx <- readIORef (simContext sim)
      let cfg = getConfiguration (ctx^.ctxSymInterface)
      let h   = printHandle ctx
      verbSetting <- getOptionSetting verbosity cfg
      oldv <- fromInteger <$> liftIO (getOpt verbSetting)
      ws <- withVerbosity h oldv $ liftIO (setOpt verbSetting (toInteger n))
      unless (null ws) (sendTextResponse sim (Text.unlines (map (Text.pack . show) ws)))
      sendAckResponse sim
    _ -> fail "expected a natural number argument to SetVerbosity request"

------------------------------------------------------------------------
-- ApplyPrimitive request

fulfillApplyPrimitiveRequest :: IsSymInterface sym
                             => Simulator p sym
                                -- ^ Simulator to run.
                             -> P.PrimitiveOp
                                -- ^ Primitive operation to apply.
                             -> Seq P.Value
                                -- ^ Arguments to primitive op.
                             -> P.CrucibleType
                             -- ^ Optional Bitwidth passed into message.
                             -- Defaults to zero.
                             -> IO ()
fulfillApplyPrimitiveRequest sim p_op args res_type = do
  -- Run apply primitive
  mv <- try $ convertToCrucibleApp (fromProtoValue sim) parseNatRepr p_op args res_type
  case mv of
    Left e -> do
      let msg = fromString (show (e :: SomeException))
      let resp =
           mempty & P.simulatorValueResponse_successful .~ False
                  & P.simulatorValueResponse_error_msg .~ msg
      let gresp =
           mempty & P.genericResponse_code .~ P.SimulatorValueGenResp
                  & P.genericResponse_simValResponse .~ resp
      sendResponse sim gresp
    Right (Some a) -> do
      let logLn _ _ = return ()
      sym <- getInterface sim
      fm <- getFloatMode sym
      r <- Sim.evalApp sym fm MapF.empty logLn (\_ x -> case x of) (\(RegEntry _ v) -> return v) a
      pv <- toProtoValue sim (RegEntry (appType a) r)
      let resp =
           mempty & P.simulatorValueResponse_successful .~ True
                  & P.simulatorValueResponse_value .~ pv
      let gresp =
           mempty & P.genericResponse_code .~ P.SimulatorValueGenResp
                  & P.genericResponse_simValResponse .~ resp
      sendResponse sim gresp


----------------------------------------------------------------------------
-- GetHandleByName request

fulfillGetHandleByNameRequest :: Simulator p sim -> Text -> IO ()
fulfillGetHandleByNameRequest sim name = do
  respondToPredefinedHandleRequest sim (NamedPredefHandle (functionNameFromText name)) $ do
     -- if the function is not already in the cache, throw an exception
     throw $ FunctionNotFound name

----------------------------------------------------------------------------
-- GetMultipartStoreHandle request

fulfillGetMultipartStoreHandleRequest :: Simulator p sym -> P.HandleInfo -> IO ()
fulfillGetMultipartStoreHandleRequest sim hinfo = do
  let c_arg_types = hinfo^.P.handleInfo_arg_types
      c_ret_type  = hinfo^.P.handleInfo_return_type

  when (Seq.length c_arg_types /= 4)
       (fail ("expected 4 types for multipart store handle"))

  argty1 <- fromProtoType (Seq.index c_arg_types 0)
  argty2 <- fromProtoType (Seq.index c_arg_types 1)
  argty3 <- fromProtoType (Seq.index c_arg_types 2)
  argty4 <- fromProtoType (Seq.index c_arg_types 3)
  rettype <- fromProtoType c_ret_type

  case (argty1, argty2, argty3, argty4, rettype) of
   (  Some BoolRepr
    , Some (BVRepr addrWidth)
    , Some (BVRepr valWidth)
    , Some (WordMapRepr addrWidth'  (BaseBVRepr cellWidth))
    , Some (WordMapRepr addrWidth'' (BaseBVRepr cellWidth'))
    )
     | Just Refl <- testEquality addrWidth addrWidth'
     , Just Refl <- testEquality addrWidth addrWidth''
     , Just Refl <- testEquality cellWidth cellWidth'
     , Just LeqProof <- isPosNat addrWidth
     , Just LeqProof <- isPosNat cellWidth
     , Just LeqProof <- isPosNat valWidth
      -> do let addrInt = fromIntegral (natValue addrWidth)
            let valInt  = fromIntegral (natValue valWidth)
            let cellInt = fromIntegral (natValue cellWidth)
            let num = valInt `div` cellInt
            when (num * cellInt /= valInt)
                 (fail $ unwords [ "value bitwidth must be a multiple of the wordmap cell width for multipart stores:"
                                 , show valInt
                                 , show cellInt
                                 ])
            respondToPredefinedHandleRequest sim (MultiPartStoreHandle addrInt cellInt num) $
                SomeHandle <$> multipartStoreFn sim addrWidth cellWidth valWidth num

   _ -> (fail $ unwords [ "illegal types to multipart store", show argty1, show argty2,
                          show argty3, show argty4, show rettype])


----------------------------------------------------------------------------
-- GetMultipartLoadHandle request

fulfillGetMultipartLoadHandleRequest :: Simulator p sym -> P.HandleInfo -> IO ()
fulfillGetMultipartLoadHandleRequest sim hinfo = do
  let c_arg_types = hinfo^.P.handleInfo_arg_types
      c_ret_type  = hinfo^.P.handleInfo_return_type

  when (Seq.length c_arg_types /= 4)
       (fail ("expected 4 types for multipart load handle"))

  argty1 <- fromProtoType (Seq.index c_arg_types 0)
  argty2 <- fromProtoType (Seq.index c_arg_types 1)
  argty3 <- fromProtoType (Seq.index c_arg_types 2)
  argty4 <- fromProtoType (Seq.index c_arg_types 3)
  rettype <- fromProtoType c_ret_type

  case (argty1, argty2, argty3, argty4, rettype) of
   (  Some BoolRepr
    , Some (BVRepr addrWidth)
    , Some (WordMapRepr addrWidth' (BaseBVRepr cellWidth))
    , Some (MaybeRepr (BVRepr cellWidth'))
    , Some (BVRepr valWidth)
    )
     | Just Refl <- testEquality addrWidth addrWidth'
     , Just Refl <- testEquality cellWidth cellWidth'
     , Just LeqProof <- isPosNat addrWidth
     , Just LeqProof <- isPosNat cellWidth
     , Just LeqProof <- isPosNat valWidth
      -> do let addrInt = fromIntegral (natValue addrWidth)
            let valInt  = fromIntegral (natValue valWidth)
            let cellInt = fromIntegral (natValue cellWidth)
            let num = valInt `div` cellInt
            when (num * cellInt /= valInt)
                 (fail $ unwords [ "value bitwidth must be a multiple of the wordmap cell width for multipart loads:"
                                 , show valInt
                                 , show cellInt
                                 ])
            respondToPredefinedHandleRequest sim (MultiPartLoadHandle addrInt cellInt num) $
                SomeHandle <$> multipartLoadFn sim addrWidth cellWidth valWidth num

   _ -> (fail $ unwords [ "illegal types to multipart load", show argty1, show argty2,
                          show argty3, show argty4, show rettype])

-------------------------------------------------------------------------
-- PrintTermHandle Request

printTermOverride :: (IsSymInterface sym)
                  => BaseTypeRepr ty
                  -> Override p sym () (EmptyCtx ::> BaseToType ty) UnitType
printTermOverride tpr =
  mkOverride (functionNameFromText (Text.pack ("printTerm_"++show tpr))) $ do
    RegMap args <- getOverrideArgs
    let p = regValue $ args^._1
    let doc = printSymExpr p
    h <- printHandle <$> getContext
    liftIO $ displayIO h (renderPretty 1.0 maxBound $ plain doc)
    liftIO $ hPutStrLn h ""
    liftIO $ hFlush h

buildPrintTermOverride
    :: (IsSymInterface sym)
    => Simulator p sym
    -> BaseTypeRepr ty
    -> IO SomeHandle
buildPrintTermOverride sim tpr =
  SomeHandle <$> simOverrideHandle sim (Ctx.empty Ctx.:> baseToType tpr) UnitRepr
                                   (printTermOverride tpr)

fulfillPrintTermHandleRequest :: IsSymInterface sym
                              => Simulator p sym
                              -> TypeRepr ty
                              -> IO ()
fulfillPrintTermHandleRequest sim tpr = do
  respondToPredefinedHandleRequest sim (PrintTermHandle (Some tpr)) $
     case tpr of
       BoolRepr    -> buildPrintTermOverride sim BaseBoolRepr
       NatRepr     -> buildPrintTermOverride sim BaseNatRepr
       IntegerRepr -> buildPrintTermOverride sim BaseIntegerRepr
       RealValRepr -> buildPrintTermOverride sim BaseRealRepr
       BVRepr w | Just LeqProof <- isPosNat w ->
           buildPrintTermOverride sim (BaseBVRepr w)
       _ -> fail $ "Cannot print values of type: "++show tpr

------------------------------------------------------------------------
-- RegisterHandle request

fulfillRegisterHandleRequest :: IsSymInterface sym
                             => Simulator p sym
                             -> P.HandleInfo
                             -> IO ()
fulfillRegisterHandleRequest sim hinfo = do
  let nm          = hinfo^.P.handleInfo_display_name
      c_arg_types = hinfo^.P.handleInfo_arg_types
      c_ret_type  = hinfo^.P.handleInfo_return_type

  Some arg_types <- fromProtoTypeSeq c_arg_types
  Some ret_type <- fromProtoType c_ret_type
  h <- simMkHandle sim (functionNameFromText nm) arg_types ret_type

  let resp = mempty & P.registerHandleResponse_index .~ handleRef h
  let gresp = mempty
            & P.genericResponse_code .~ P.RegisterHandleGenResp
            & P.genericResponse_regHandleResponse .~ resp

  sendResponse sim $ gresp

------------------------------------------------------------------------
-- main

handleOneRequest :: IsSymInterface sym
                 => Simulator p sym
                 -> BackendSpecificRequests p sym
                 -> P.Request
                 -> IO ()
handleOneRequest sim addlRequests request =
  case request^.P.request_code of
    P.RegisterHandle -> do
      let hinfo = request^.P.request_handle
      fulfillRegisterHandleRequest sim hinfo
    P.UseCFG -> do
      fulfillUseCFGRequest sim (request^.P.request_cfg)
    P.RunCall -> do
      let all_args = request^.P.request_args
      -- Get function aand arguments.
      (fn, args) <- getHead all_args
      -- Fulfill request
      fulfillRunCallRequest sim fn args
    P.ReleaseValue -> do
      releaseRegEntryRef sim (request^.P.request_index)
    P.SetVerbosity -> do
      let args = request^.P.request_args
      fulfillSetVerbosityRequest sim args
    P.GetConfigValue -> do
      let nm   = request^.P.request_config_setting_name
      fulfillGetConfigValueRequest sim nm
    P.SetConfigValue -> do
      let nm   = request^.P.request_config_setting_name
      let args = request^.P.request_args
      fulfillSetConfigValueRequest sim nm args
    P.ApplyPrimitive -> do
      let p_op = request^.P.request_prim_op
      let args = request^.P.request_args
      let res_type = request^.P.request_result_type
      fulfillApplyPrimitiveRequest sim p_op args res_type
    P.PrintCFG -> do
      fulfillPrintCFGRequest sim (request^.P.request_cfg)
    P.GetHandleByName -> do
      fulfillGetHandleByNameRequest sim (request^.P.request_handle^.P.handleInfo_display_name)
    P.SymbolicHandle -> do
      fulfillSymbolHandleRequest addlRequests sim (request^.P.request_varType)
    P.PrintTermHandle -> do
      Some tyr <- fromProtoType (request^.P.request_type)
      fulfillPrintTermHandleRequest sim tyr
    P.MultipartStoreHandle -> do
      fulfillGetMultipartStoreHandleRequest sim (request^.P.request_handle)
    P.MultipartLoadHandle -> do
      fulfillGetMultipartLoadHandleRequest sim (request^.P.request_handle)
    P.ExportModel -> do
      let path     = request^.P.request_export_path
      let all_args = request^.P.request_args
      let format   = request^.P.request_export_format
      fulfillExportModelRequest addlRequests sim format path all_args

    P.CompileVerificationOverride -> do
      let harness  = request^.P.request_verification_harness
      fulfillCompileVerificationOverrideRequest addlRequests sim harness

    P.SimulateVerificationHarness -> do
      let harness  = request^.P.request_verification_harness
      let opts     = request^.P.request_verification_sim_options
      fullfillSimulateVerificationHarnessRequest addlRequests sim harness opts

    P.ResumeSimulation -> do
      nyi "resumeSimulation"
    P.UseOverride -> do
      nyi "useOverride"

    P.KillSimulator  -> fail "kill simulator unexpected"
    P.UnknownMessage -> fail "unknown message"



data BackendSpecificRequests p sym
    = BackendSpecificRequests
      { fulfillExportModelRequest
         :: Simulator p sym
         -> P.ExportFormat
         -> Text
         -> Seq P.Value
         -> IO ()
      , fulfillSymbolHandleRequest
         :: Simulator p sym
         -> P.VarType
         -> IO ()
      , fulfillCompileVerificationOverrideRequest
         :: Simulator p sym
         -> P.VerificationHarness
         -> IO ()
      , fullfillSimulateVerificationHarnessRequest
         :: Simulator p sym
         -> P.VerificationHarness
         -> P.VerificationSimulateOptions
         -> IO ()
      }

-- | Loop for fulfilling request
fulfillRequests :: IsSymInterface sym
                => Simulator p sym
                -> BackendSpecificRequests p sym
                -> IO ()
fulfillRequests sim addlRequests = do
  -- logMsg "Waiting for request"
  request <- getDelimited (requestHandle sim)
  -- logMsg "Received request"
  case request^.P.request_code of
    P.KillSimulator -> exitSuccess
    P.UnknownMessage -> do
      hPutStrLn stderr "Could not interpret message."
      exitWith (ExitFailure (-1))
    _ -> do
      r <- try (handleOneRequest sim addlRequests request)
      case r of
        Left ex -> sendExceptionResponse sim ex
        Right _ -> return ()
      fulfillRequests sim addlRequests
