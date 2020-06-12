{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.Go.Simulate (setupCrucibleGoCrux) where

import           Control.Monad
import           Control.Monad.Fail (MonadFail)

import           System.IO

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes

-- crucible
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Types

import           Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator as C

-- what4
import qualified What4.Config as W4
import qualified What4.Interface as W4

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


-- This function receives the parsed Go file (assumed to contain only
-- a single top-level function), translates it to a crucible CFG, and
-- sets up the initial simulator state to call the translated function
-- with the provided arguments.

-- NOTE: we call the function handle 'cfgHandle' from the CFG produced
-- by 'translateFunction', which I think represents the entry point
-- into the CFG, but perhaps that isn't right.
setupCrucibleGoCrux :: forall sym args ret p.
  (IsSymInterface sym, KnownRepr CtxRepr args, KnownRepr TypeRepr ret)
  => File SourceRange
  -> Int               -- ^ Verbosity level
  -> sym               -- ^ Simulator state
  -> p                 -- ^ Personality
  -> C.RegMap sym args -- ^ Arguments
  -> IO (C.ExecState p sym Go (C.RegEntry sym ret))
setupCrucibleGoCrux (File _ fileName pkgName _imports toplevels) verbosity sym p args = do
  
  when (verbosity > 2) $
    putStrLn "starting setupCrucibleGoCrux"
  setSimulatorVerbosity verbosity sym
  halloc <- newHandleAllocator

  case toplevels of
    -- For now we just expect a single top-level function declaration.
    FunctionDecl _ fName params returns (Just body) : _ -> do
      AnyCFG (CFG { cfgHandle = h }) <- let ?machineWordWidth = 32 in
                                          translateFunction fName params returns body :: IO (AnyCFG Go)
      -- Check argument and return types.
      Refl <- failIfNotEqual (handleArgTypes h) (knownRepr :: CtxRepr args) $
              "Checking argument types for function " ++ show fName
      Refl <- failIfNotEqual (handleReturnType h) (knownRepr :: TypeRepr ret) $
              "Checking return type for function " ++ show fName

      -- Set up initial simulator state to call the translated function.
      let k = C.runOverrideSim (handleReturnType h) $ C.regValue <$> C.callFnVal (C.HandleFnVal h) args
      let intrinsics = emptyIntrinsicTypes
      let fnBindings = emptyHandleMap
      let simctx = initSimContext sym intrinsics halloc stdout fnBindings goExtensionImpl p
      let simGlobals = emptyGlobals
      let abortHandler = C.defaultAbortHandler
      return $ C.InitialState simctx simGlobals abortHandler (knownRepr :: TypeRepr ret) k

    _ -> error "expected a top-level function declaration"
