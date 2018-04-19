-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Server.SAWOverrides
-- Copyright        : (c) Galois, Inc 2014-2016
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-- License          : BSD3
--
-- Function implementations that are specific to the SAW backend.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Server.SAWOverrides where

import           Control.Lens
import           Control.Monad.IO.Class
import           Data.Foldable (toList)
import           Data.IORef
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V
import           System.Directory
import           System.FilePath

import           Lang.Crucible.Config
import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Server.CryptolEnv
import           Lang.Crucible.Server.Requests
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.TypeConv
--import           Lang.Crucible.Server.TypedTerm
import           Lang.Crucible.Server.ValueConv
import           Lang.Crucible.Server.Verification.Harness
import           Lang.Crucible.Server.Verification.Override
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Solver.Interface
import qualified Lang.Crucible.Solver.SAWCoreBackend as SAW
import qualified Lang.Crucible.Solver.SimpleBuilder as SB
import           Lang.Crucible.Types

import qualified Verifier.SAW.ExternalFormat as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Recognizer as SAW

sawServerOptions :: [ConfigDesc]
sawServerOptions = SAW.sawOptions

sawServerOverrides :: [Simulator p (SAW.SAWCoreBackend n) -> IO SomeHandle]
sawServerOverrides = []

data SAWCrucibleServerPersonality =
   SAWCrucibleServerPersonality
   { _sawServerCryptolEnv :: CryptolEnv
   }

sawServerCryptolEnv :: Simple Lens SAWCrucibleServerPersonality CryptolEnv
sawServerCryptolEnv = lens _sawServerCryptolEnv (\s v -> s{ _sawServerCryptolEnv = v })

initSAWServerPersonality ::
  SAW.SAWCoreBackend n ->
  IO SAWCrucibleServerPersonality
initSAWServerPersonality sym =
  do sc <- SAW.sawBackendSharedContext sym
     cryEnv <- initCryptolEnv sc
     return SAWCrucibleServerPersonality
            { _sawServerCryptolEnv = cryEnv
            }

sawBackendRequests :: BackendSpecificRequests SAWCrucibleServerPersonality (SAW.SAWCoreBackend n)
sawBackendRequests =
  BackendSpecificRequests
  { fulfillExportModelRequest = sawFulfillExportModelRequest
  , fulfillSymbolHandleRequest = sawFulfillSymbolHandleRequest
  , fulfillCompileVerificationOverrideRequest = sawFulfillCompileVerificationOverrideRequest
  , fullfillSimulateVerificationHarnessRequest = sawFulfillSimulateVerificationHarnessRequest
  }


sawFulfillCompileVerificationOverrideRequest
   :: forall n
    . Simulator SAWCrucibleServerPersonality (SAW.SAWCoreBackend n)
   -> P.VerificationHarness
   -> IO ()
sawFulfillCompileVerificationOverrideRequest sim harness =
  do sc <- SAW.sawBackendSharedContext =<< getInterface sim
     cryEnv <- view (cruciblePersonality . sawServerCryptolEnv) <$> readIORef (simContext sim)
     let hout = sendTextResponse sim . Text.pack

     (cryEnv',harness') <- processHarness hout sc cryEnv harness
     -- NB: we explicitly do not store the modified cryEnv' back into the simContext;
     -- the modifications to the environment produced by processing a harness are only
     -- scoped over the harness itself.

     let addrWidth = verificationAddressWidth harness'
     let regFileWidth = verificationRegFileWidth harness'

     case someNat (toInteger regFileWidth) of
       Just (Some rw) | Just LeqProof <- isPosNat rw ->
         case someNat (toInteger addrWidth) of
           Just (Some w) | Just LeqProof <- isPosNat w ->

              do fnhandle <- verificationHarnessOverrideHandle sim rw w cryEnv' harness'
                 let response = displayHarness (fmap snd harness')

                 sendTextResponse sim response
                 sendPredefinedHandleResponse sim fnhandle

           _ -> fail ("Improper address width given for verification harness: " ++ show addrWidth)
       _ -> fail ("Improper register file width given for verification harness: " ++ show regFileWidth)


sawFulfillSimulateVerificationHarnessRequest ::
  Simulator SAWCrucibleServerPersonality (SAW.SAWCoreBackend n) ->
  P.VerificationHarness ->
  P.VerificationSimulateOptions ->
  IO ()
sawFulfillSimulateVerificationHarnessRequest sim harness opts =
  do sym <- getInterface sim
     ctx <- readIORef (simContext sim)
     let hout = sendTextResponse sim . Text.pack

     sc <- SAW.sawBackendSharedContext sym
     let cryEnv = ctx^.cruciblePersonality.sawServerCryptolEnv

     (cryEnv', harness') <- processHarness hout sc cryEnv harness
     -- NB: we explicitly do not store the modified cryEnv' back into the simContext;
     -- the modifications to the environment produced by processing a harness are only
     -- scoped over the harness itself.

     let addrWidth = verificationAddressWidth harness'
     let regFileWidth = verificationRegFileWidth harness'

     -- Clear all proof-management context and restore it afterwards
     SAW.inFreshNamingContext sym $
       case someNat (toInteger regFileWidth) of
         Just (Some rw) | Just LeqProof <- isPosNat rw ->
           case someNat (toInteger addrWidth) of
             Just (Some w) | Just LeqProof <- isPosNat w ->
               do pc  <- regValue <$> (checkedRegEntry (BVRepr w) =<< fromProtoValue sim (opts^.P.verificationSimulateOptions_start_pc))
                  sp  <- regValue <$> (checkedRegEntry (BVRepr w) =<< fromProtoValue sim (opts^.P.verificationSimulateOptions_start_stack))
                  ret <- regValue <$> (checkedRegEntry (BVRepr w) =<< fromProtoValue sim (opts^.P.verificationSimulateOptions_return_address))
                  fn  <- regValue <$> (checkedRegEntry (verifFnRepr rw w) =<< fromProtoValue sim (opts^.P.verificationSimulateOptions_program))

                  let simSt = initSimState ctx emptyGlobals (serverErrorHandler sim)

                  exec_res <- runOverrideSim simSt UnitRepr (simulateHarness sim rw w sc cryEnv' harness' pc sp ret fn)

                  case exec_res of
                    FinishedExecution ctx' (TotalRes (GlobalPair _r _globals)) -> do
                      sendTextResponse sim "Finished!"
                      writeIORef (simContext sim) $! ctx'
                    FinishedExecution ctx' (PartialRes _ (GlobalPair _r _globals) _) -> do
                      sendTextResponse sim "Finished, some paths aborted!"
                      writeIORef (simContext sim) $! ctx'
                    AbortedResult ctx' _ -> do
                      sendTextResponse sim "All paths aborted!"
                      writeIORef (simContext sim) $! ctx'
                  handleProofObligations sim sym opts

             _ -> fail ("Improper address width given for verification harness: " ++ show addrWidth)
         _ -> fail ("Improper register file width given for verification harness: " ++ show regFileWidth)

handleProofObligations ::
  Simulator SAWCrucibleServerPersonality (SAW.SAWCoreBackend n) ->
  SAW.SAWCoreBackend n ->
  P.VerificationSimulateOptions ->
  IO ()
handleProofObligations sim sym opts =
  do obls <- SB.sbGetProofObligations sym
     SB.sbSetProofObligations sym mempty
     dirPath <- makeAbsolute (Text.unpack (opts^.P.verificationSimulateOptions_output_directory))
     createDirectoryIfMissing True dirPath
     if opts^.P.verificationSimulateOptions_separate_obligations
        then handleSeparateProofObligations sim sym dirPath obls
        else handleSingleProofObligation sim sym dirPath obls
     sendAckResponse sim

handleSeparateProofObligations ::
  Simulator SAWCrucibleServerPersonality (SAW.SAWCoreBackend n) ->
  SAW.SAWCoreBackend n ->
  FilePath ->
  Seq (Seq (Pred (SAW.SAWCoreBackend n)), Assertion (Pred (SAW.SAWCoreBackend n))) ->
  IO ()
handleSeparateProofObligations sim sym dir obls = fail "FIXME separate proof obligations!"

handleSingleProofObligation ::
  Simulator SAWCrucibleServerPersonality (SAW.SAWCoreBackend n) ->
  SAW.SAWCoreBackend n ->
  FilePath ->
  Seq (Seq (Pred (SAW.SAWCoreBackend n)), Assertion (Pred (SAW.SAWCoreBackend n))) ->
  IO ()
handleSingleProofObligation sim sym dir obls =
  do createDirectoryIfMissing True {- create parents -} dir
     preds <- mapM (sequentToSC sym) obls
     totalPred <- andAllOf sym folded preds
     sc <- SAW.sawBackendSharedContext sym
     exts <- toList <$> SAW.getInputs sym
     finalPred <- SAW.scAbstractExts sc exts =<< SAW.toSC sym totalPred

     let fname = dir </> "obligations.saw"
     writeFile fname (SAW.scWriteExternal finalPred)

sequentToSC ::
  SAW.SAWCoreBackend n ->
  (Seq (Pred (SAW.SAWCoreBackend n)), Assertion (Pred (SAW.SAWCoreBackend n))) ->
  IO (Pred (SAW.SAWCoreBackend n))
sequentToSC sym (assumes, assert) =
  do assume <- andAllOf sym folded assumes
     impliesPred sym assume (assert^.assertPred)

sawFulfillExportModelRequest
   :: forall p n
    . Simulator p (SAW.SAWCoreBackend n)
   -> P.ExportFormat
   -> Text.Text
   -> Seq.Seq P.Value
   -> IO ()
sawFulfillExportModelRequest sim P.ExportSAW path vals = do
  sym <- getInterface sim
  st <- readIORef $ SB.sbStateManager sym

  let f :: Some (RegEntry (SAW.SAWCoreBackend n))
        -> IO (Maybe (SAW.Term, SAW.Term))
      f (Some (RegEntry (VectorRepr tp) v)) = do
           (v' :: [Maybe (SAW.Term, SAW.Term)])
               <- traverse (\x -> f (Some (RegEntry tp x))) $ V.toList v
           case sequence v' of
             Nothing -> return Nothing
             Just [] -> return Nothing -- FIXME? fail on empty vectors...
             Just vs@((_,vtp):_) -> do
                x'  <- SAW.scVector (SAW.saw_ctx st) vtp (map fst vs)
                tp' <- SAW.scTypeOf (SAW.saw_ctx st) x'
                return (Just (x',tp'))
      f (Some r) = asSymExpr r (\x -> do
                                   x' <- SAW.toSC sym x
                                   tp <- SAW.scTypeOf (SAW.saw_ctx st) x'
                                   return $ Just (x',tp))
                               (return Nothing)
  vals' <- traverse f =<< mapM (fromProtoValue sim) (toList vals)
  case map fst <$> sequence vals' of
    Nothing -> fail "Could not translate values for SAW export"
    Just scs -> do
      tm  <- case scs of
                [] -> fail "No terms passed to SAW export"
                [x] -> return x
                _ -> SAW.scTuple (SAW.saw_ctx st) scs
      exts <- toList <$> readIORef (SAW.saw_inputs st)
      tm' <- SAW.scAbstractExts (SAW.saw_ctx st) exts tm
      writeFile (Text.unpack path) (SAW.scWriteExternal tm')
      let v = mempty & P.value_code .~ P.UnitValue
      sendCallReturnValue sim v

sawFulfillExportModelRequest _sim P.ExportAIGER _path _vals = do
  fail "SAW backend does not implement AIGER export"


sawTypeFromTypeVar :: SAW.SharedContext
                   -> [Int]
                   -> BaseTypeRepr tp
                   -> IO SAW.Term
sawTypeFromTypeVar sc [] bt = SAW.baseSCType sc bt
sawTypeFromTypeVar sc (x:xs) bt = do
  txs <- sawTypeFromTypeVar sc xs bt
  n <- SAW.scNat sc (fromIntegral x)
  SAW.scVecType sc n txs

-- | Returns override for creating a given variable associated with the given type.
symbolicOverride :: forall p n tp
                  . SAW.SharedContext
                 -> [Int]
                 -> SAW.Term
                 -> TypeRepr tp
                 -> Override p (SAW.SAWCoreBackend n) () EmptyCtx tp
symbolicOverride sc dims0 sawTp0 tpr0 = do
  mkOverride' "symbolic" tpr0 $ do
    sym <- getSymInterface

    t <- liftIO $ SAW.sawCreateVar sym "x" sawTp0
    liftIO $ buildVecs dims0 sym sawTp0 tpr0 t

 where buildVecs :: [Int]
                 -> SAW.SAWCoreBackend n
                 -> SAW.Term
                 -> TypeRepr tp'
                 -> SAW.Term
                 -> IO (RegValue (SAW.SAWCoreBackend n) tp')

       buildVecs [] sym _ tpr t =
         case asBaseType tpr of
           AsBaseType bt -> SAW.bindSAWTerm sym bt t
           NotBaseType -> fail $ "Unsupported SAW base type" ++ show tpr

       buildVecs (x:xs) sym sawTp (VectorRepr tpr) t = do
          (n SAW.:*: sawTp') <- SAW.asVecType sawTp
          V.generateM x (\i -> do
                    n' <- SAW.scNat sc n
                    i' <- SAW.scNat sc (fromIntegral i)
                    t' <- SAW.scAt sc n' sawTp' t i'
                    buildVecs xs sym sawTp' tpr t'
                 )

       buildVecs _ _ _ tpr _ = do
          fail $ "Unsupported SAW variable type: " ++ show tpr

sawFulfillSymbolHandleRequest :: Simulator p (SAW.SAWCoreBackend n) -> P.VarType -> IO ()
sawFulfillSymbolHandleRequest sim proto_tp = do
  let dims = proto_tp^.P.varType_dimensions
  let dims' = map fromIntegral $ toList dims
  Some tpr <- crucibleTypeFromProtoVarType proto_tp
  Some vtp <- varTypeFromProto proto_tp
  sym <- getInterface sim
  st <- readIORef $ SB.sbStateManager sym
  sawTp <- sawTypeFromTypeVar (SAW.saw_ctx st) dims' vtp

  respondToPredefinedHandleRequest sim (SymbolicHandle dims' (Some vtp)) $ do
    let o = symbolicOverride (SAW.saw_ctx st) dims' sawTp tpr
    SomeHandle <$> simOverrideHandle sim Ctx.empty tpr o
