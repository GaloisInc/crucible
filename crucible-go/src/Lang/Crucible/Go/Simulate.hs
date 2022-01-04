{-|
Module      : Lang.Crucible.Go.Simulate
Description : Setup Go Crucible simulator
Maintainer  : abagnall@galois.com
Stability   : experimental

This file contains the Crux setup code for Go programs (given a parsed
program, translate it and construct the initial simulator state).
-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Lang.Crucible.Go.Simulate (setupCrucibleGoCrux) where

import           Control.Monad
import           Control.Monad.Fail (MonadFail)

import           Data.Text (Text)

import           System.IO

-- parameterized-utils
import           Data.Parameterized.Context as Ctx

-- crucible
import qualified Lang.Crucible.Analysis.Postdom as C
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as Reg
import           Lang.Crucible.Panic
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState

import           Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator as C

-- crux
import qualified Crux.Types   as Crux

-- what4
import qualified What4.Config as W4
import           What4.FunctionName (FunctionName)
import qualified What4.Interface as W4

-- go
import            Language.Go.AST
import            Language.Go.Desugar (desugar)
import            Language.Go.Parser as P
import            Language.Go.Rename (rename)
import            Language.Go.Types

import            Lang.Crucible.Go.Overrides
import            Lang.Crucible.Go.Translation (translate)
import            Lang.Crucible.Go.Types

-- | Borrowed from crucible-jvm.
setSimulatorVerbosity :: (W4.IsSymExprBuilder sym) => Int -> sym -> IO ()
setSimulatorVerbosity verbosity sym = do
  verbSetting <- W4.getOptionSetting W4.verbosity (W4.getConfiguration sym)
  _ <- W4.setOpt verbSetting (toInteger verbosity)
  return ()

goExtensionEval ::
  forall sym bak p ext rtp blocks r ctx.
  (IsSymInterface sym, IsBoolSolver sym bak) =>
  bak ->
  C.IntrinsicTypes sym ->
  (Int -> String -> IO ()) ->
  EvalAppFunc sym (ExprExtension Go)
goExtensionEval _bak _iTypes _logFn _f x = case x of {}

-- | No syntax extensions.
goExtensionImpl :: C.ExtensionImpl p sym Go
goExtensionImpl =
  C.ExtensionImpl
    (\bak iTypes logFn _ f ->
       goExtensionEval bak iTypes logFn f)
    (\x -> case x of)

failIfNotEqual :: forall k f m a (b :: k).
                  (MonadFail m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise = fail $ str ++ ": mismatch between "
                ++ show r1 ++ " and " ++ show r2

mkFunctionBindings :: forall sym p ext.
                      [SomeOverride p sym ext]
                   -> [(Maybe (Text, FunctionName), AnyCFG ext)]
                   -> FunctionBindings p sym ext
mkFunctionBindings _overrides [] = FnBindings emptyHandleMap
mkFunctionBindings overrides ((ident, AnyCFG cfg) : cfgs) =
  let f = case lookupOverride' ident overrides of
        Just (SomeOverride _pkg argsRepr retRepr override) ->
          case (testEquality (cfgArgTypes cfg) argsRepr,
                testEquality (cfgReturnType cfg) retRepr) of
            (Just Refl, Just Refl) -> UseOverride override
            _ -> panic "[Go simulator] mkFunctionBindings"
                 [ "Type mismatch for override of " ++ show ident
                 , "  Expected: " ++ show (cfgArgTypes cfg) ++ " -> " ++ show (cfgReturnType cfg)
                 , "  Got: " ++ show argsRepr ++ " -> " ++ show retRepr
                 ]
        Nothing -> UseCFG cfg $ C.postdomInfo cfg in
    FnBindings $ insertHandleMap (cfgHandle cfg) f
               $ fnBindings
               $ mkFunctionBindings overrides cfgs

asApp :: MonadFail m
      => Reg.Expr ext s tp
      -> (App ext (Reg.Expr ext s) tp -> m a)
      -> m a
asApp (Reg.App e) k = k e
asApp (Reg.AtomExpr a) _k =
  fail $ "asApp: expected App constructor, got atom " ++ show a

evalExpr :: (IsSymInterface sym, IsBoolSolver sym bak)
         => bak
         -> Reg.Expr Go s tp
         -> IO (C.RegValue sym tp)
evalExpr bak e = asApp e $ doAppGo bak

-- | Evaluate an App expression in the @IO@ monad.
doAppGo :: (IsSymInterface sym, IsBoolSolver sym bak)
        => bak
        -> App Go (Reg.Expr Go s) tp
        -> IO (C.RegValue sym tp)
doAppGo bak =
  evalApp bak goIntrinsicTypes out
  (goExtensionEval bak goIntrinsicTypes out) $
  flip asApp $ doAppGo bak
  where
    out = const putStrLn

mkGlobals :: (IsSymInterface sym, IsBoolSolver sym bak)
          => bak
          -> [GoGlobal]
          -> IO (SymGlobalState sym)
mkGlobals bak globals =
  foldM (\state (GoGlobal glob zero) -> do
            zv <- evalExpr bak zero
            return $ insertGlobal glob zv state)
  emptyGlobals globals

setupCrucibleGoCrux :: forall sym bak args p.
  (IsSymInterface sym, IsBoolSolver sym bak, KnownRepr CtxRepr args)
  => Int                   -- ^ Machine word width
  -> Node P.SourcePos Main -- ^ Input program
  -> Int                   -- ^ Verbosity level
  -> bak                   -- ^ Simulator state
  -> p sym                 -- ^ Personality
  -> C.RegMap sym args     -- ^ Arguments
  -> IO (C.ExecState (p sym) sym Go (C.RegEntry sym UnitType))
setupCrucibleGoCrux machineWordWidth fwi verbosity bak p args = do
  let sym = backendGetSym bak
  setSimulatorVerbosity verbosity sym

  case intToPosNat machineWordWidth of
    Nothing -> error "machineWordWidth should be >= 1"
    Just (PosNat w LeqProof) -> do
      translated <- translate (PosNat w LeqProof) $ rename $ desugar fwi
      case translated of
        Left msg -> fail msg
        Right (TranslatedMain _main _imports
                (SomeCFG ini) (Just (AnyCFG cfg)) globs funs halloc) -> do

          Refl <- failIfNotEqual (cfgArgTypes cfg) (knownRepr :: CtxRepr args) $
                  "Checking argument types for main"
          Refl <- failIfNotEqual (cfgReturnType cfg) (StructRepr Ctx.empty) $
                  "Checking return type for main"
          let fnBindings = mkFunctionBindings (go_overrides w) funs

          -- Call initializer before main.
          let k = C.runOverrideSim UnitRepr $ do
                C.callFnVal (C.HandleFnVal $ cfgHandle ini) C.emptyRegMap
                C.callFnVal (C.HandleFnVal $ cfgHandle cfg) args
                return ()

          -- Set up initial simulator state to call the main.
          let simctx = initSimContext bak goIntrinsicTypes halloc stdout
                       fnBindings goExtensionImpl p
          simGlobals <- mkGlobals bak globs
          let abortHandler = C.defaultAbortHandler
          return $ C.InitialState simctx simGlobals abortHandler knownRepr k
