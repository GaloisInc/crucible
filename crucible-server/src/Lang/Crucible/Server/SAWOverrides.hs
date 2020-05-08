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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
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
--import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V
import           System.Directory
import           System.FilePath

import           What4.Config
import           What4.Interface
import qualified What4.Expr.Builder as SB

import           Lang.Crucible.Backend
import qualified Lang.Crucible.Backend.SAWCore as SAW
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
import           Lang.Crucible.Simulator.EvalStmt (executeCrucible,genericToExecutionFeature)
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import qualified Verifier.SAW.ExternalFormat as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Recognizer as SAW

sawServerOptions :: [ConfigDesc]
sawServerOptions = []

sawServerOverrides :: [Simulator p (SAWBack n) -> IO SomeHandle]
sawServerOverrides = []

data SAWCrucibleServerPersonality =
   SAWCrucibleServerPersonality
   { _sawServerCryptolEnv :: CryptolEnv
   }

sawServerCryptolEnv :: Lens' SAWCrucibleServerPersonality CryptolEnv
sawServerCryptolEnv = lens _sawServerCryptolEnv (\s v -> s{ _sawServerCryptolEnv = v })

initSAWServerPersonality ::
  SAWBack n ->
  IO SAWCrucibleServerPersonality
initSAWServerPersonality sym =
  do sc <- SAW.sawBackendSharedContext sym
     cryEnv <- initCryptolEnv sc
     return SAWCrucibleServerPersonality
            { _sawServerCryptolEnv = cryEnv
            }

sawBackendRequests :: BackendSpecificRequests SAWCrucibleServerPersonality (SAWBack n)
sawBackendRequests =
  BackendSpecificRequests
  { fulfillExportModelRequest = sawFulfillExportModelRequest
  , fulfillSymbolHandleRequest = sawFulfillSymbolHandleRequest
  , fulfillCompileVerificationOverrideRequest = sawFulfillCompileVerificationOverrideRequest
  , fullfillSimulateVerificationHarnessRequest = sawFulfillSimulateVerificationHarnessRequest
  }


sawFulfillCompileVerificationOverrideRequest
   :: forall n
    . Simulator SAWCrucibleServerPersonality (SAWBack n)
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
  Simulator SAWCrucibleServerPersonality (SAWBack n) ->
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

     fm <- getFloatMode sym

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

                  let simSt = InitialState ctx emptyGlobals (serverErrorHandler sim) UnitRepr
                                $ runOverrideSim UnitRepr
                                    (simulateHarness sim rw w sc cryEnv' harness' pc sp ret fn)

                  exec_res <- executeCrucible fm (map genericToExecutionFeature (simExecFeatures sim)) simSt
                  case exec_res of
                    TimeoutResult exst -> do
                      let ctx' = execStateContext exst
                      sendTextResponse sim "Simulation timed out!"
                      writeIORef (simContext sim) $! ctx'
                    FinishedResult ctx' (TotalRes (GlobalPair _r _globals)) -> do
                      sendTextResponse sim "Finished!"
                      writeIORef (simContext sim) $! ctx'
                    FinishedResult ctx' (PartialRes _ _ (GlobalPair _r _globals) _) -> do
                      sendTextResponse sim "Finished, some paths aborted!"
                      writeIORef (simContext sim) $! ctx'
                    AbortedResult ctx' _ -> do
                      sendTextResponse sim "All paths aborted!"
                      writeIORef (simContext sim) $! ctx'
                  handleProofObligations sim sym opts

             _ -> fail ("Improper address width given for verification harness: " ++ show addrWidth)
         _ -> fail ("Improper register file width given for verification harness: " ++ show regFileWidth)

handleProofObligations ::
  Simulator SAWCrucibleServerPersonality (SAWBack n) ->
  SAWBack n ->
  P.VerificationSimulateOptions ->
  IO ()
handleProofObligations sim sym opts =
  do obls <- getProofObligations sym
     clearProofObligations sym
     dirPath <- makeAbsolute (Text.unpack (opts^.P.verificationSimulateOptions_output_directory))
     createDirectoryIfMissing True dirPath
     if opts^.P.verificationSimulateOptions_separate_obligations
        then handleSeparateProofObligations sim sym dirPath obls
        else handleSingleProofObligation sim sym dirPath obls
     sendAckResponse sim

handleSeparateProofObligations ::
  Simulator SAWCrucibleServerPersonality (SAWBack n) ->
  SAWBack n ->
  FilePath ->
  ProofObligations (SAWBack n) ->
  IO ()
handleSeparateProofObligations _sim _sym _dir _obls = fail "FIXME separate proof obligations!"

handleSingleProofObligation ::
  Simulator SAWCrucibleServerPersonality (SAWBack n) ->
  SAWBack n ->
  FilePath ->
  ProofObligations (SAWBack n) ->
  IO ()
handleSingleProofObligation _sim sym dir obls =
  do createDirectoryIfMissing True {- create parents -} dir
     -- TODO: there is probably a much more efficient way to do this
     -- that more directly follows the structure of the proof goal tree
     preds <- mapM (sequentToSC sym) (proofGoalsToList obls)
     totalPred <- andAllOf sym folded preds
     sc <- SAW.sawBackendSharedContext sym
     exts <- toList <$> SAW.getInputs sym
     finalPred <- SAW.scAbstractExts sc exts =<< SAW.toSC sym totalPred

     let fname = dir </> "obligations.saw"
     writeFile fname (SAW.scWriteExternal finalPred)

sequentToSC ::
  SAWBack n ->
  ProofObligation (SAWBack n) ->
  IO (Pred (SAWBack n))
sequentToSC sym (ProofGoal assumes goal) =
  do assume <- andAllOf sym (folded.labeledPred) assumes
     impliesPred sym assume (goal^.labeledPred)

sawFulfillExportModelRequest
   :: forall p n
    . Simulator p (SAWBack n)
   -> P.ExportFormat
   -> Text.Text
   -> Seq.Seq P.Value
   -> IO ()
sawFulfillExportModelRequest sim P.ExportSAW path vals = do
  sym <- getInterface sim
  st <- readIORef $ SB.sbStateManager sym

  let f :: Some (RegEntry (SAWBack n))
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


sawTypeFromTypeVar :: SAWBack n
                   -> SAW.SharedContext
                   -> [Int]
                   -> BaseTypeRepr tp
                   -> IO SAW.Term
sawTypeFromTypeVar sym sc [] bt = SAW.baseSCType sym sc bt
sawTypeFromTypeVar sym sc (x:xs) bt = do
  txs <- sawTypeFromTypeVar sym sc xs bt
  n <- SAW.scNat sc (fromIntegral x)
  SAW.scVecType sc n txs

-- | Returns override for creating a given variable associated with the given type.
symbolicOverride :: forall p n tp
                  . SAW.SharedContext
                 -> [Int]
                 -> SAW.Term
                 -> TypeRepr tp
                 -> Override p (SAWBack n) () EmptyCtx tp
symbolicOverride sc dims0 sawTp0 tpr0 = do
  mkOverride' "symbolic" tpr0 $ do
    sym <- getSymInterface

    t <- liftIO $ SAW.sawCreateVar sym "x" sawTp0
    liftIO $ buildVecs dims0 sym sawTp0 tpr0 t

 where buildVecs :: [Int]
                 -> SAWBack n
                 -> SAW.Term
                 -> TypeRepr tp'
                 -> SAW.Term
                 -> IO (RegValue (SAWBack n) tp')

       buildVecs [] sym _ tpr t =
         case asBaseType tpr of
           AsBaseType bt -> SAW.bindSAWTerm sym bt t
           NotBaseType -> fail $ "Unsupported SAW base type" ++ show tpr

       buildVecs (x:xs) sym sawTp (VectorRepr tpr) t = do
          case SAW.asVecType sawTp of
            Nothing -> fail $ "Expected vector type, but got " ++ show sawTp
            Just (n SAW.:*: sawTp') ->
               V.generateM x (\i -> do
                         n' <- SAW.scNat sc n
                         i' <- SAW.scNat sc (fromIntegral i)
                         t' <- SAW.scAt sc n' sawTp' t i'
                         buildVecs xs sym sawTp' tpr t'
                      )

       buildVecs _ _ _ tpr _ = do
          fail $ "Unsupported SAW variable type: " ++ show tpr

sawFulfillSymbolHandleRequest :: Simulator p (SAWBack n) -> P.VarType -> IO ()
sawFulfillSymbolHandleRequest sim proto_tp = do
  let dims = proto_tp^.P.varType_dimensions
  let dims' = map fromIntegral $ toList dims
  Some tpr <- crucibleTypeFromProtoVarType proto_tp
  Some vtp <- varTypeFromProto proto_tp
  sym <- getInterface sim
  st <- readIORef $ SB.sbStateManager sym
  sawTp <- sawTypeFromTypeVar sym (SAW.saw_ctx st) dims' vtp

  respondToPredefinedHandleRequest sim (SymbolicHandle dims' (Some vtp)) $ do
    let o = symbolicOverride (SAW.saw_ctx st) dims' sawTp tpr
    SomeHandle <$> simOverrideHandle sim Ctx.empty tpr o
