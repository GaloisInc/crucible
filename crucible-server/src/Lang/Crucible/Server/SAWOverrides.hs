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
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import qualified Data.Vector as V

import qualified Lang.Crucible.Proto as P
import           Lang.Crucible.Server.Requests
import           Lang.Crucible.Server.Simulator
import           Lang.Crucible.Server.TypeConv
import           Lang.Crucible.Server.ValueConv
import           Lang.Crucible.Simulator.CallFrame (SomeHandle(..))
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Simulator.RegMap
import qualified Lang.Crucible.Solver.SAWCoreBackend as SAW
import qualified Lang.Crucible.Solver.SimpleBuilder as SB
import           Lang.Crucible.Types

import qualified Verifier.SAW.ExternalFormat as SAW
import qualified Verifier.SAW.SharedTerm as SAW
import qualified Verifier.SAW.Recognizer as SAW


sawBackendRequests :: BackendSpecificRequests p (SAW.SAWCoreBackend n)
sawBackendRequests =
  BackendSpecificRequests
  { fulfillExportModelRequest = sawFulfillExportModelRequest
  , fulfillSymbolHandleRequest = sawFulfillSymbolHandleRequest
  , fulfillCompileVerificationOverrideRequest = sawFulfillCompileVerificationOverrideRequest
  }

sawFulfillCompileVerificationOverrideRequest
   :: forall p n
    . Simulator p (SAW.SAWCoreBackend n)
   -> P.VerificationHarness
   -> IO ()
sawFulfillCompileVerificationOverrideRequest _sim _harness =
  do fail "FIXME implement verification harness compilation"


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
                 -> Override p (SAW.SAWCoreBackend n) EmptyCtx tp
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
