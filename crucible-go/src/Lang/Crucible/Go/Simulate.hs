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

module Lang.Crucible.Go.Simulate (setupCrucibleGoCrux) where

-- import           Control.Lens
import           Control.Monad
import           Control.Monad.Fail (MonadFail)
import           Control.Monad.Identity
import           Control.Monad.State

import           Data.Default.Class
import           Data.Functor.Const
import qualified Data.HashMap.Strict as HM
import           Data.Text (Text, pack, unpack)

import           System.IO

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce

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
import           What4.FunctionName (startFunctionName)
import qualified What4.Interface as W4
import           What4.ProgramLoc as W4
import           What4.Utils.StringLiteral

-- go
import            Language.Go.AST
import            Language.Go.Parser
import            Lang.Crucible.Go.Translation
import            Lang.Crucible.Go.Types

-- Borrowed from crucible-jvm.
setSimulatorVerbosity :: (W4.IsSymExprBuilder sym) => Int -> sym -> IO ()
setSimulatorVerbosity verbosity sym = do
  verbSetting <- W4.getOptionSetting W4.verbosity (W4.getConfiguration sym)
  _ <- W4.setOpt verbSetting (toInteger verbosity)
  return ()

-- No syntax extensions.
goExtensionImpl :: C.ExtensionImpl p sym Go
goExtensionImpl = C.ExtensionImpl (\_sym _iTypes _logFn _f x -> case x of) (\x -> case x of)

failIfNotEqual :: forall k f m a (b :: k).
                  (MonadFail m, Show (f a), Show (f b), TestEquality f)
               => f a -> f b -> String -> m (a :~: b)
failIfNotEqual r1 r2 str
  | Just Refl <- testEquality r1 r2 = return Refl
  | otherwise = fail $ str ++ ": mismatch between " ++ show r1 ++ " and " ++ show r2


-- Translate a list of top-level function definitions and associate
-- each one with a function handle. Return the handle to 'main' if it
-- exists.
-- mkBindings :: forall p sym.
--      HandleAllocator
--   -> [TopLevel SourceRange]
--   -> IO (FunctionBindings p sym Go, Maybe SomeHandle)
-- mkBindings _ [] = return (emptyHandleMap, Nothing)
-- mkBindings halloc (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
--   (bindings, mainHandle) <- mkBindings halloc toplevels
--   AnyCFG (cfg@(CFG { cfgHandle = h })) <-
--     let ?machineWordWidth = 32 in translateFunction halloc fName params returns body
--   putStrLn $ "Translating function " ++ show (() <$ fName)
--   putStrLn $ show cfg
--   let bindings' = insertHandleMap h (UseCFG cfg $ C.postdomInfo cfg) bindings
--   case (unpack fnm, mainHandle) of
--     ("main", Just _)  -> error "multiple definitions of 'main'"
--     ("main", Nothing) -> return (bindings', Just $ SomeHandle h)
--     _                 -> return (bindings', mainHandle)


-- translateFuns :: (?machineWordWidth :: Int)
--               => HM.HashMap Text SomeHandle
--               -> [TopLevel SourceRange]
--               -> StateT [Int] IO (FunctionBindings p sym Go)
-- translateFuns _ [] = return emptyHandleMap
-- translateFuns env (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
--   bindings <- translateFuns env toplevels
--   flip (maybe $ error $ "translateFuns: function " ++ unpack fnm ++ " not found")
--     (HM.lookup fnm env) $ \(SomeHandle h) -> do
--     SomeCFG cfg <- lift $ translateFunction h env undefined fName params returns body
--     lift $ putStrLn $ "Translating function " ++ show (() <$ fName)
--     lift $ putStrLn $ show cfg
--     return $ insertHandleMap h (UseCFG cfg $ C.postdomInfo cfg) bindings

-- -- Given a function environment (containing pre-allocated handles for
-- -- every function in the file) and a list of the toplevel definitions
-- -- of the file, translate all of the functions and produce a
-- -- FunctionBindings mapping handles to translated CFGs.
-- translateFuns :: (?machineWordWidth :: Int)
--               => HM.HashMap Text SomeHandle
--               -> [TopLevel SourceRange]
--               -> State [ReprAndValue] (IO (FunctionBindings p sym Go))
-- translateFuns _ [] = return $ return emptyHandleMap
-- translateFuns env (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
--   binds_action <- translateFuns env toplevels  
--   flip (maybe $ error $ "translateFuns: handle for function " ++ unpack fnm ++ " not found")
--     (HM.lookup fnm env) $ \(SomeHandle h) -> return $ do
--     SomeCFG cfg <- translateFunction h env undefined fName params returns body
--     putStrLn $ "Translating function " ++ show (() <$ fName)
--     putStrLn $ show cfg
--     binds <- binds_action
--     return $ insertHandleMap h (UseCFG cfg $ C.postdomInfo cfg) binds
-- translateFuns env (_ : toplevels) = translateFuns env toplevels

-- Given a function environment (containing pre-allocated handles for
-- every function in the file) and a list of the toplevel definitions
-- of the file, translate all of the functions and produce a
-- FunctionBindings mapping handles to translated CFGs.
-- translateFuns :: (?machineWordWidth :: Int)
--               => HM.HashMap Text SomeHandle
--               -> [TopLevel SourceRange]
--               -> StateT [ReprAndValue] IO (FunctionBindings p sym Go)
-- translateFuns _ [] = return emptyHandleMap
-- translateFuns env (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
--   bindings <- translateFuns env toplevels
--   nils <- get
--   flip (maybe $ error $ "translateFuns: handle for function " ++ unpack fnm ++ " not found")
--     (HM.lookup fnm env) $ \(SomeHandle h) -> do
--     (SomeCFG cfg, nils') <- lift $ translateFunction h env undefined fName params returns body
--     lift $ putStrLn $ "Translating function " ++ show (() <$ fName)
--     lift $ putStrLn $ show cfg
--     return $ insertHandleMap h (UseCFG cfg $ C.postdomInfo cfg) bindings
-- translateFuns env (_ : toplevels) = translateFuns env toplevels

translateFuns :: (?machineWordWidth :: Int)
              => HM.HashMap Text SomeHandle
              -> [TopLevel SourceRange]
              -> IO (FunctionBindings p sym Go)
translateFuns _ [] = return emptyHandleMap
translateFuns env (FunctionDecl _ fName@(Id _ _ fnm) params returns (Just body) : toplevels) = do
  bindings <- translateFuns env toplevels
  flip (maybe $ error $ "translateFuns: handle for function " ++ unpack fnm ++ " not found")
    (HM.lookup fnm env) $ \(SomeHandle h) -> do
    SomeCFG cfg <- translateFunction h env fName params returns body
    putStrLn $ "Translating function " ++ show (() <$ fName)
    putStrLn $ show cfg
    return $ insertHandleMap h (UseCFG cfg $ C.postdomInfo cfg) bindings
translateFuns env (_ : toplevels) = translateFuns env toplevels


-- do_assume ::
--   (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
--   GlobalVar Mem ->
--   sym ->
--   Assignment (RegEntry sym) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) ->
--   OverM sym (LLVM arch) (RegValue sym UnitType)
-- do_assume mvar sym (Empty :> p :> pFile :> line) =
--   do cond <- liftIO $ bvIsNonzero sym (regValue p)
--      file <- lookupString mvar pFile
--      l <- case asUnsignedBV (regValue line) of
--             Just l  -> return (fromInteger l)
--             Nothing -> return 0
--      let pos = SourcePos (T.pack file) l 0
--      loc <- liftIO $ getCurrentProgramLoc sym
--      let loc' = loc{ plSourceLoc = pos }
--      let msg = AssumptionReason loc' "crucible_assume"
--      liftIO $ addAssumption sym (LabeledPred cond msg)

-- fresh_var :: IsSymInterface sym =>
--              BaseTypeRepr ty ->
--              C.OverrideSim p sym ext gret EmptyCtx ret (RegValue sym (BaseToType ty))
-- fresh_var = do
--   sym <- C.getSymInterface
--   RegMap (Ctx.Empty Ctx.:> b) <- C.getOverrideArgs
--   loc <- liftIO $ W4.getCurrentProgramLoc sym
--   liftIO $ addAssumption sym (LabeledPred (regValue b) (AssumptionReason loc "assume"))

do_assume :: IsSymInterface sym =>
             C.OverrideSim p sym ext gret (SingleCtx BoolType) ret (RegValue sym UnitType)
do_assume = do
  sym <- C.getSymInterface
  RegMap (Ctx.Empty Ctx.:> b) <- C.getOverrideArgs
  loc <- liftIO $ W4.getCurrentProgramLoc sym
  liftIO $ addAssumption sym (LabeledPred (regValue b) (AssumptionReason loc "assume"))

-- do_assert ::
--   (ArchOk arch, IsSymInterface sym, HasLLVMAnn sym) =>
--   GlobalVar Mem ->
--   sym ->
--   Assignment (RegEntry sym) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) ->
--   OverM sym (LLVM arch) (RegValue sym UnitType)
-- do_assert mvar sym (Empty :> p :> pFile :> line) =
--   do cond <- liftIO $ bvIsNonzero sym (regValue p)
--      file <- lookupString mvar pFile
--      l <- case asUnsignedBV (regValue line) of
--             Just l  -> return (fromInteger l)
--             Nothing -> return 0
--      let pos = SourcePos (T.pack file) l 0
--      loc <- liftIO $ getCurrentProgramLoc sym
--      let loc' = loc{ plSourceLoc = pos }
--      let msg = GenericSimError "crucible_assert"
--      liftIO $ addDurableAssertion sym (LabeledPred cond (SimError loc' msg))


setupCrucibleGoCrux :: forall sym args p.
  (IsSymInterface sym, KnownRepr CtxRepr args, ?machineWordWidth :: Int)
  => File SourceRange
  -> Int               -- ^ Verbosity level
  -> sym               -- ^ Simulator state
  -> p                 -- ^ Personality
  -> C.RegMap sym args -- ^ Arguments
  -> IO (C.ExecState p sym Go (C.RegEntry sym UnitType))
setupCrucibleGoCrux (File _ fileName pkgName _imports toplevels) verbosity sym p args = do
  
  when (verbosity > 2) $
    putStrLn "starting setupCrucibleGoCrux"
  setSimulatorVerbosity verbosity sym
  halloc <- newHandleAllocator

  env <- mkFnEnv halloc toplevels

  -- bindings <- evalStateT (translateFuns @p @sym env toplevels) []
  bindings <- translateFuns @p @sym env toplevels
  let mainHandle = HM.lookup (pack "main") env
  
  flip (maybe (error "expected a 'main' function")) mainHandle $ \(SomeHandle h) -> do
    Refl <- failIfNotEqual (handleArgTypes h) (knownRepr :: CtxRepr args) $
            "Checking argument types for main"
    Refl <- failIfNotEqual (handleReturnType h) (StructRepr Ctx.empty) $
            "Checking return type for main"

    -- Ignore the function's return value (which we know can only be
    -- the single inhabitant of 'StructType EmptyCtx') and return
    -- unit instead to appease crux.
    let k = C.runOverrideSim UnitRepr $ C.callFnVal (C.HandleFnVal h) args >> return ()

    -- Set up initial simulator state to call the translated function.      
    let intrinsics = emptyIntrinsicTypes
    let simctx = initSimContext sym intrinsics halloc stdout bindings goExtensionImpl p
    let simGlobals = emptyGlobals
    let abortHandler = C.defaultAbortHandler
    return $ C.InitialState simctx simGlobals abortHandler knownRepr k
