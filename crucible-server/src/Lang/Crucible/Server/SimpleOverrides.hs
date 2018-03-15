-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.SimpleOverrides
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Function implementations that are specific to the "simple" backend.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Server.SimpleOverrides where

import           Control.Lens
import           Control.Monad.State.Strict
import           Data.Foldable (toList)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import           Data.Typeable
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen ( text )

import           Data.Parameterized.Some
import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.Config
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Solver.Adapter
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.SatResult
import           Lang.Crucible.Solver.SimpleBackend
import           Lang.Crucible.Solver.SimpleBackend.ABC ( abcAdapter, genericSatAdapter )
import qualified Lang.Crucible.Solver.SimpleBackend.ABC as ABC
import           Lang.Crucible.Solver.SimpleBackend.Boolector ( boolectorAdapter )
import           Lang.Crucible.Solver.SimpleBackend.CVC4 ( cvc4Adapter )
import qualified Lang.Crucible.Solver.SimpleBackend.SMTLib2 as SMT2
import qualified Lang.Crucible.Solver.SimpleBackend.Yices as Yices
import           Lang.Crucible.Solver.SimpleBackend.Z3 ( z3Adapter )
import           Lang.Crucible.Solver.SimpleBuilder
import           Lang.Crucible.Solver.Symbol
import           Lang.Crucible.Types
import           Lang.Crucible.Utils.MonadVerbosity

import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.Requests
import           Lang.Crucible.Server.TypeConv
import           Lang.Crucible.Server.ValueConv

crucibleServerAdapters :: Typeable st => [SolverAdapter st]
crucibleServerAdapters =
  [ abcAdapter
  , genericSatAdapter
  , boolectorAdapter
  , Yices.yicesAdapter
  , cvc4Adapter
  , z3Adapter
  ]

simpleServerOptions :: forall p t st
                    .  Typeable st
                    => [ConfigDesc (SimConfigMonad p (SimpleBuilder t st))]
simpleServerOptions =
  let adapters :: [SolverAdapter st]
      adapters = crucibleServerAdapters in
  [ optListShow defaultSolverAdapter adapters
    (text "Indicates which solver to use for check-sat queries")

  ] ++ concatMap solver_adapter_config_options adapters

simpleServerOverrides :: [Simulator p (SimpleBackend n) -> IO SomeHandle]
simpleServerOverrides =
 [ mkPredef checkSatWithAbcOverride
 , mkPredef checkSatWithYicesOverride
 , mkPredef writeSMTLib2Override
 , mkPredef writeYicesOverride
 ]


simpleBackendRequests :: BackendSpecificRequests p (SimpleBackend n)
simpleBackendRequests =
  BackendSpecificRequests
  { fulfillExportModelRequest = sbFulfillExportModelRequest
  , fulfillSymbolHandleRequest = sbFulfillSymbolHandleRequest
  , fulfillCompileVerificationOverrideRequest = sbFulfillCompileVerificationOverrideRequest
  , fullfillSimulateVerificationHarnessRequest = sbFulfillSimulateVerificationHarnessRequest
  }

------------------------------------------------------------------------
-- CheckSatWithAbcHandle Request

type CheckSatArgs = EmptyCtx ::> BoolType

-- | Returns override for creating a given variable associated with the given type.
checkSatWithAbcOverride :: Override p (SimpleBackend n) () CheckSatArgs BoolType
checkSatWithAbcOverride = do
  mkOverride "checkSatWithAbc" $ do
    RegMap args <- getOverrideArgs
    let p = regValue $ args^._1
    sym <- getSymInterface
    logLn <- getLogFunction
    cfg <- simConfig <$> getContext
    r <- liftIO $ ABC.checkSat cfg logLn p
    return $ backendPred sym (isSat r)

------------------------------------------------------------------------
-- CheckSatWithYicesHandle Request

-- | Returns override for creating a given variable associated with the given type.
checkSatWithYicesOverride :: Override p (SimpleBackend n) () CheckSatArgs BoolType
checkSatWithYicesOverride = do
  mkOverride "checkSatWithYices" $ do
    RegMap args <- getOverrideArgs
    let p = regValue $ args^._1
    sym <- getSymInterface
    logLn <- getLogFunction
    cfg <- simConfig <$> getContext
    r <- liftIO $ Yices.runYicesInOverride sym cfg logLn p (return . isSat)
    return $ backendPred sym r

------------------------------------------------------------------------
-- WriteSMTLib2Handle request

type WriteSMTLIB2Args
   = EmptyCtx
   ::> StringType
   ::> BoolType

writeSMTLib2Override :: Override p (SimpleBackend n) () WriteSMTLIB2Args UnitType
writeSMTLib2Override = do
  mkOverride "write_SMTLIB2" $ do
    RegMap args <- getOverrideArgs
    let file_nm = regValue $ args^._1
        p       = regValue $ args^._2
    sym <- getSymInterface
    liftIO $ withFile (Text.unpack file_nm) WriteMode $ \h ->
      SMT2.writeDefaultSMT2 () "SMTLIB2" defaultWriteSMTLIB2Features sym h p

-----------------------------------------------------------------------------------------
-- WriteYicesHandle request

writeYicesOverride :: Override p (SimpleBackend n) () WriteSMTLIB2Args UnitType
writeYicesOverride = do
  mkOverride "write_yices" $ do
    RegMap args <- getOverrideArgs
    let file_nm = regValue $ args^._1
        p       = regValue $ args^._2
    ctx <- getContext
    let sym = ctx^.ctxSymInterface
    let cfg = simConfig ctx
    liftIO $ Yices.writeYicesFile sym cfg (Text.unpack file_nm) p

------------------------------------------------------------------------
-- SimpleBackend ExportModel request

sbFulfillExportModelRequest
   :: Simulator p (SimpleBackend n)
   -> P.ExportFormat
   -> Text.Text
   -> Seq.Seq P.Value
   -> IO ()
sbFulfillExportModelRequest sim P.ExportAIGER path vals = do
  vals' <- mapM (fromProtoValue sim) (toList vals)
  let f :: Some (RegEntry (SimpleBackend n)) -> Maybe (Some (SymExpr (SimpleBackend n)))
      f (Some r) = asSymExpr r (\x -> Just (Some x)) Nothing
  case traverse f vals' of
    Nothing -> fail "Could not translate values for AIG export"
    Just vals'' -> do
      ABC.writeAig (Text.unpack path) vals'' []
      let v = mempty & P.value_code .~ P.UnitValue
      sendCallReturnValue sim v

sbFulfillExportModelRequest _sim P.ExportSAW _path _vals = do
  fail "The simple backend does not support exporting SAWCore terms"


------------------------------------------------------------------------
-- SymbolHandle request

-- | Returns override for creating a given variable associated with the given type.
symbolicOverride :: IsSymInterface sym => BaseTypeRepr tp -> Override p sym () EmptyCtx (BaseToType tp)
symbolicOverride tp = do
  mkOverride' "symbolic" (baseToType tp) $ do
    sym <- getSymInterface
    liftIO $ freshConstant sym emptySymbol tp

sbFulfillSymbolHandleRequest :: IsSymInterface sym => Simulator p sym -> P.VarType -> IO ()
sbFulfillSymbolHandleRequest sim proto_tp = do
  Some vtp <- varTypeFromProto proto_tp
  let dims = proto_tp^.P.varType_dimensions
  when (not $ Seq.null dims)
       (fail "Simple backend does not support creating symbolic sequences")
  respondToPredefinedHandleRequest sim (SymbolicHandle [] (Some vtp)) $ do
    let o = symbolicOverride vtp
    let tp = baseToType vtp
    SomeHandle <$> simOverrideHandle sim Ctx.empty tp o

-------------------------------------------------------------------------
-- Compile verification request

sbFulfillCompileVerificationOverrideRequest
 :: IsSymInterface sym => Simulator p sym -> P.VerificationHarness -> IO ()
sbFulfillCompileVerificationOverrideRequest _sim _harness =
  fail "The 'simple' server backend does not support verification harnesses"

sbFulfillSimulateVerificationHarnessRequest
 :: IsSymInterface sym => Simulator p sym -> P.VerificationHarness -> P.VerificationSimulateOptions -> IO ()
sbFulfillSimulateVerificationHarnessRequest _sim _harness _opts =
  fail "The 'simple' server backend does not support verification harnesses"
