{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Lang.Crucible.Go.Simulate (setupCrucibleGoCrux) where

import           Control.Monad
import           Control.Monad.Fail (MonadFail)
import           Control.Monad.Identity
import           Control.Monad.State

import           Data.Bifunctor (first)
import           Data.Default.Class
import           Data.Functor.Const
import qualified Data.HashMap.Strict as HM
import           Data.Text (Text, pack, unpack)

import           System.IO

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
-- import           Data.Parameterized.NatRepr as N

-- crucible
import qualified Lang.Crucible.Analysis.Postdom as C
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Reg as Reg
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator as C

import qualified Lang.Crucible.CFG.Generator as Gen

-- crux
import qualified Crux.Types   as Crux

-- what4
import qualified What4.Config as W4
import qualified What4.Expr.Builder as W4
import           What4.FunctionName (FunctionName, functionNameFromText, startFunctionName)
import qualified What4.Interface as W4
import           What4.ProgramLoc as W4
import           What4.Utils.StringLiteral

-- go
import            Language.Go.AST
import            Language.Go.Parser
import            Lang.Crucible.Go.Translation
import            Lang.Crucible.Go.Types

-- | Borrowed from crucible-jvm.
setSimulatorVerbosity :: (W4.IsSymExprBuilder sym) => Int -> sym -> IO ()
setSimulatorVerbosity verbosity sym = do
  verbSetting <- W4.getOptionSetting W4.verbosity (W4.getConfiguration sym)
  _ <- W4.setOpt verbSetting (toInteger verbosity)
  return ()

-- | No syntax extensions.
goExtensionImpl :: C.ExtensionImpl p sym Go
goExtensionImpl = C.ExtensionImpl (\_sym _iTypes _logFn _f x -> case x of) (\x -> case x of)

failIfNotEqual :: forall k f m a (b :: k).
                  (MonadFail m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise = fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2

mkFresh :: IsSymInterface sym =>
           String ->
           BaseTypeRepr ty ->
           -- C.OverrideSim p sym ext gret EmptyCtx (BaseToType ty) (RegValue sym (BaseToType ty))
           -- OverM sym (LLVM arch) (RegValue sym (BaseToType ty))
           Crux.OverM sym ext (RegValue sym (BaseToType ty))
mkFresh nm ty =
  do sym  <- C.getSymInterface
     name <- case W4.userSymbol nm of
               Left err -> fail (show err) -- XXX
               Right a  -> return a
     liftIO $ W4.freshConstant sym name ty

fresh_int :: (IsSymInterface sym, 1 <= w) =>
             NatRepr w ->
             -- C.OverrideSim p sym ext gret EmptyCtx (BVType w) (RegValue sym (BVType w))
             Crux.OverM sym ext (RegValue sym (BVType w))
fresh_int w = mkFresh "X" (BaseBVRepr w)

do_assume :: IsSymInterface sym =>
             C.OverrideSim p sym ext gret (SingleCtx BoolType) (StructType EmptyCtx)
             (RegValue sym (StructType EmptyCtx))
do_assume = do
  sym <- C.getSymInterface
  RegMap (Ctx.Empty Ctx.:> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addAssumption sym (LabeledPred (regValue b) (AssumptionReason loc "assume"))
  return Ctx.empty

do_assert :: IsSymInterface sym =>
             C.OverrideSim p sym ext gret (SingleCtx BoolType) (StructType EmptyCtx)
             (RegValue sym (StructType EmptyCtx))
do_assert = do
  sym <- C.getSymInterface
  RegMap (Ctx.Empty Ctx.:> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addDurableAssertion sym (LabeledPred (regValue b)
                                    (C.SimError loc $ C.AssertFailureSimError
                                     "assertion_failure" ""))
  return Ctx.empty

data SomeOverride p sym ext where
  SomeOverride :: CtxRepr args ->
                  TypeRepr ret ->
                  Override p sym ext args ret ->
                  SomeOverride p sym ext

nameOfOverride :: Override p sym ext args ret -> Text
nameOfOverride (Override { overrideName = nm }) =
  pack $ show nm

mkSomeOverride :: String -> CtxRepr args -> TypeRepr ret ->
                  (forall r. C.OverrideSim p sym ext r args ret (RegValue sym ret)) ->
                  SomeOverride p sym ext
mkSomeOverride nm argsRepr retRepr overrideSim =
  SomeOverride argsRepr retRepr $
  Override { overrideName = functionNameFromText $ pack nm
           , overrideHandler = C.runOverrideSim retRepr overrideSim }

-- go_overrides :: (IsSymInterface sym, 1 <= w) => NatRepr w -> [(SomeOverride p sym ext)]
go_overrides :: (IsSymInterface sym, 1 <= w) => NatRepr w -> [(SomeOverride (Crux.Model sym) sym ext)]
go_overrides w =
  [ mkSomeOverride "fresh_int" Ctx.empty                (BVRepr w)             (fresh_int w)
  , mkSomeOverride "assume"    (Ctx.singleton BoolRepr) (StructRepr Ctx.empty) do_assume
  , mkSomeOverride "assert"    (Ctx.singleton BoolRepr) (StructRepr Ctx.empty) do_assert ]

-- | Given a list of overrides, a function environment, and
-- FunctionBindings, allocate new function handles for the overrides
-- and produce updated environment and FunctionBindings which include
-- the overrides.
addOverrides :: HandleAllocator ->
                [SomeOverride p sym ext] ->
                FnEnv ->
                IO (FnEnv, FunctionBindings p sym ext)
addOverrides _ [] env = return (env, emptyHandleMap)
addOverrides ha (SomeOverride argsRepr retRepr override : overrides) env = do
  (env', binds) <- addOverrides ha overrides env
  h <- mkHandle' ha (functionNameFromText nm) argsRepr retRepr
  return $ (insertFnEnv nm (SomeHandle h) env', insertHandleMap h (UseOverride override) binds)
  where
    nm = nameOfOverride override

-- | Existentially packaged positive natural number.
data PosNat = forall w. PosNat (NatRepr w) (LeqProof 1 w)

intToPosNat :: Int -> Maybe PosNat
intToPosNat i = do
  Some w <- someNat (fromIntegral i)
  LeqProof <- isPosNat w
  return $ PosNat w LeqProof

-- | Given a function environment (containing pre-allocated handles for
-- every function in the file) and a list of the toplevel definitions
-- of the file, translate all of the functions and produce a
-- FunctionBindings mapping handles to translated CFGs.
translateFuns :: (IsSymInterface sym, IsSyntaxExtension ext, ?machineWordWidth :: Int) =>
                 FnEnv ->
                 FunctionBindings p sym ext ->
                 [TopLevel SourceRange] ->
                 IO (FunctionBindings p sym ext)
translateFuns _ binds [] = return binds
translateFuns env binds (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
  binds' <- translateFuns env binds toplevels
  flip (maybe $ error $ "translateFuns: handle for function " ++ unpack fnm ++ " not found")
    (lookupFnEnv fnm env) $ \(SomeHandle h) -> do
    SomeCFG cfg <- translateFunction h env fName params returns body
    putStrLn $ "Translating function " ++ show (() <$ fName)
    putStrLn $ show cfg
    return $ insertHandleMap h (UseCFG cfg $ C.postdomInfo cfg) binds'
translateFuns env binds (_ : toplevels) = translateFuns env binds toplevels

setupCrucibleGoCrux :: forall sym args.
  (IsSymInterface sym, KnownRepr CtxRepr args, ?machineWordWidth :: Int)
  => File SourceRange
  -> Int               -- ^ Verbosity level
  -> sym               -- ^ Simulator state
  -- -> p                 -- ^ Personality
  -> Crux.Model sym    -- ^ Personality
  -> C.RegMap sym args -- ^ Arguments
  -> IO (C.ExecState (Crux.Model sym) sym Go (C.RegEntry sym UnitType))
setupCrucibleGoCrux (File _ fileName pkgName _imports toplevels) verbosity sym p args = do
  
  when (verbosity > 2) $
    putStrLn "starting setupCrucibleGoCrux"
  setSimulatorVerbosity verbosity sym
  halloc <- newHandleAllocator
  
  case intToPosNat ?machineWordWidth of
    Nothing -> error "machineWordWidth should be >= 1"
    Just (PosNat w LeqProof) -> do
      env <- mkInitialFnEnv halloc toplevels
      let mainHandle = lookupFnEnv (pack "main") env

      flip (maybe (error "expected a 'main' function")) mainHandle $ \(SomeHandle h) -> do
        Refl <- failIfNotEqual (handleArgTypes h) (knownRepr :: CtxRepr args) $
                "Checking argument types for main"
        Refl <- failIfNotEqual (handleReturnType h) (StructRepr Ctx.empty) $
                "Checking return type for main"

        (env', bindings) <- addOverrides halloc (go_overrides w) env
        bindings' <- translateFuns env' bindings toplevels

        -- Ignore the function's return value (which we know can only
        -- be the single inhabitant of 'StructType EmptyCtx') and
        -- return unit instead to appease crux.
        let k = C.runOverrideSim UnitRepr $ C.callFnVal (C.HandleFnVal h) args >> return ()

        -- Set up initial simulator state to call the translated
        -- function.
        let intrinsics = emptyIntrinsicTypes
        let simctx = initSimContext sym intrinsics halloc stdout bindings' goExtensionImpl p
        let simGlobals = emptyGlobals
        let abortHandler = C.defaultAbortHandler
        return $ C.InitialState simctx simGlobals abortHandler knownRepr k
