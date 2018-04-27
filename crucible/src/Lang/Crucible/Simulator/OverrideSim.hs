{-|
Module      : Lang.Crucible.Simulator.OverrideSim
Description : The main simulation monad
Copyright   : (c) Galois, Inc 2014-2016
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

Define the main simulation monad 'OverrideSim' and basic operations on it.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.OverrideSim
  ( -- * Monad definition
    OverrideSim(..)
  , runOverrideSim
  , initSimState
    -- * Monad operations
  , withSimContext
  , getContext
  , getSymInterface
  , getPathConditions
  , bindFnHandle
  , exitExecution
  , getOverrideArgs
    -- * Function calls
  , callCFG
  , callFnVal
  , callFnVal'
    -- * Global variables
  , readGlobal
  , writeGlobal
  , readGlobals
  , writeGlobals
    -- * References
  , newRef
  , readRef
  , writeRef
    -- * Function bindings
  , FnBinding(..)
  , fnBindingsFromList
  , registerFnBinding
  , AnyFnBindings(..)
    -- * Overrides
  , mkOverride
  , mkOverride'
    -- * Intrinsic implementations
  , IntrinsicImpl
  , mkIntrinsic
  , useIntrinsic
    -- * Re-exports
  , Lang.Crucible.Simulator.ExecutionTree.Override
  ) where

import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.List (foldl')
import qualified Data.Parameterized.Context as Ctx
import           Data.Proxy
import           System.Exit
import           System.IO
import           System.IO.Error

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.Config
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Simulator.CallFns
import           Lang.Crucible.Simulator.CallFrame (mkCallFrame)
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Frame
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.BoolInterface
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Utils.MonadST
import           Lang.Crucible.Utils.MonadVerbosity
import           Lang.Crucible.Utils.StateContT

------------------------------------------------------------------------
-- OverrideSim

-- | Monad for running symbolic simulator.
--
-- Type parameters:
--
--   * 'p'    the "personality", i.e. user-defined state parameterized by @sym@
--   * 'sym'  the symbolic backend
--   * 'ext'  the syntax extension ("Lang.Crucible.CFG.Extension")
--   * 'rtp'  global return type
--   * 'args' argument types for the current frame
--   * 'ret'  return type of the current frame
--   * 'a'    the value type
--
newtype OverrideSim (p :: * -> *) sym ext rtp (args :: Ctx CrucibleType) (ret :: CrucibleType) a
      = Sim { unSim :: StateContT (SimState p sym ext rtp (OverrideLang args ret) 'Nothing)
                                  (ExecResult p sym ext rtp)
                                  IO
                                  a
            }
  deriving ( Functor
           , Applicative
           )

-- | Exit from the current execution by ignoring the continuation
--   and immediately returning an aborted execution result.
exitExecution :: IsSymInterface sym => ExitCode -> OverrideSim p sym ext rtp args r a
exitExecution ec = Sim $ StateContT $ \_c s -> do
  return $ AbortedResult (s^.stateContext) (AbortedExit ec)

returnOverrideSim :: a -> OverrideSim p sym ext rtp args r a
returnOverrideSim v = Sim $ return v
{-# INLINE returnOverrideSim #-}

bindOverrideSim :: OverrideSim p sym ext rtp args r a
          -> (a -> OverrideSim p sym ext rtp args r b)
          -> OverrideSim p sym ext rtp args r b
bindOverrideSim (Sim m) h = Sim $ unSim . h =<< m
{-# INLINE bindOverrideSim #-}

instance Monad (OverrideSim p sym ext rtp args r) where
  return = returnOverrideSim
  (>>=) = bindOverrideSim
  fail msg = Sim $ StateContT $ \_c s -> mssRunGenericErrorHandler s msg

deriving instance MonadState (SimState p sym ext rtp (OverrideLang args ret) 'Nothing)
                             (OverrideSim p sym ext rtp args ret)

instance MonadIO (OverrideSim p sym ext rtp args ret) where
  liftIO m = do
     Sim $ StateContT $ \c s -> do
       r <- try m
       case r of
         Left e0
           -- IO Exception
           | Just e <- fromException e0
           , isUserError e ->
             mssRunGenericErrorHandler s (ioeGetErrorString e)
             -- SimError
           | Just e <- fromException e0 ->
             mssRunErrorHandler s e
             -- Default case
           | otherwise ->
             throwIO e0
         Right v -> c v s

instance MonadST RealWorld (OverrideSim p sym ext rtp args ret) where
  liftST m = liftIO $ stToIO m

instance MonadCont (OverrideSim p sym ext rtp args ret) where
  callCC f = Sim $ callCC (\k -> unSim (f (\a -> Sim (k a))))

getContext :: OverrideSim p sym ext rtp args ret (SimContext p sym ext)
getContext = use stateContext
{-# INLINE getContext #-}

getSymInterface :: OverrideSim p sym ext rtp args ret sym
getSymInterface = gets stateSymInterface

-- | Return predicates that must be satisfiable for path to be feasible.
getPathConditions :: OverrideSim p sym ext rtp a ret [Pred sym]
getPathConditions = do
  s <- get
  return (pathConditions (s^.stateTree^.actContext))

instance MonadVerbosity (OverrideSim p sym ext rtp args ret) where
  getVerbosity = do
    ctx <- getContext
    let cfg = ctxSolverProof ctx (getConfiguration (ctx^.ctxSymInterface))
    v <- liftIO (getOpt =<< getOptionSetting verbosity cfg)
    return (fromInteger v)

  getLogFunction = do
    h <- printHandle <$> getContext
    verb <- getVerbosity
    return $ \n msg -> do
      when (n <= verb) $ do
        hPutStr h msg
        hFlush h
  showWarning msg = do
    h <- printHandle <$> getContext
    liftIO $ do
    hPutStrLn h msg
    hFlush h

-- | Associate a definition (either an 'Override' or a 'CFG') with the given handle.
bindFnHandle -- :: (KnownCtx TypeRepr args, KnownRepr TypeRepr ret)
                  :: FnHandle args ret
                  -> FnState p sym ext args ret
                  -> OverrideSim p sym ext rtp a r ()
bindFnHandle h s = do
  stateContext . functionBindings %= insertHandleMap h s

------------------------------------------------------------------------
-- Mutable variables

-- | Read the whole sym global state.
readGlobals :: OverrideSim p sym ext rtp args ret (SymGlobalState sym)
readGlobals = use (stateTree . actFrame . gpGlobals)

-- | Overwrite the whole sym global state
writeGlobals :: SymGlobalState sym -> OverrideSim p sym ext rtp args ret ()
writeGlobals g = stateTree . actFrame . gpGlobals .= g

-- | Read a particular global variable from the global variable state.
readGlobal ::
  GlobalVar tp                                     {- ^ global variable -} ->
  OverrideSim p sym ext rtp args ret (RegValue sym tp) {- ^ current value   -}
readGlobal k =
  do globals <- readGlobals
     case lookupGlobal k globals of
       Just v  -> return v
       Nothing -> fail ("Attempt to read undefined global " ++ show k)

-- | Set the value of a particular global variable.
writeGlobal ::
  GlobalVar tp    {- ^ global variable -} ->
  RegValue sym tp {- ^ new value       -} ->
  OverrideSim p sym ext rtp args ret ()
writeGlobal g v = stateTree . actFrame . gpGlobals %= insertGlobal g v


newRef :: IsSymInterface sym
       => TypeRepr tp
       -> RegValue sym tp
       -> OverrideSim p sym ext rtp args ret (RefCell tp)
newRef tpr v = do
   s <- get
   let halloc = simHandleAllocator (s^.stateContext)
   r <- liftST (freshRefCell halloc tpr)
   writeRef r v
   return r

readRef :: IsSymInterface sym
        => RefCell tp
        -> OverrideSim p sym ext rtp args ret (RegValue sym tp)
readRef r = do
   sym <- getSymInterface
   globals <- use $ stateTree . actFrame . gpGlobals
   let msg = ReadBeforeWriteSimError "Attempt to read undefined reference cell"
   liftIO $ readPartExpr sym (lookupRef r globals) msg

writeRef :: IsSymInterface sym
         => RefCell tp
         -> RegValue sym tp
         -> OverrideSim p sym ext rtp args ret ()
writeRef r v =
  do sym <- getSymInterface
     stateTree . actFrame . gpGlobals %= insertRef sym r v

------------------------------------------------------------------------
-- Override utilities

-- | Run an override sim.
runOverrideSim :: SimState p sym ext rtp (OverrideLang args tp) 'Nothing
                  -- ^ initial state
               -> TypeRepr tp
                  -- ^ return type
               -> OverrideSim p sym ext rtp args tp (RegValue sym tp)
                  -- ^ action to run
               -> IO (ExecResult p sym ext rtp)
runOverrideSim s0 tp m = do
  runStateContT (unSim m) (\v s -> returnValue s (RegEntry tp v)) s0

-- | Create an initial 'SimState'.
initSimState :: SimContext p sym ext
             -> SymGlobalState sym
             -- ^ state of global variables
             -> ErrorHandler p sym ext (RegEntry sym ret)
             -> SimState p sym ext (RegEntry sym ret) (OverrideLang EmptyCtx ret) 'Nothing
initSimState ctx globals eh =
  let startFrame = OverrideFrame { override = startFunctionName
                                 , overrideRegMap = emptyRegMap
                                 }
      ae = GlobalPair (OF startFrame) globals
   in SimState { _stateContext = ctx
               , _errorHandler = eh
               , _stateTree = singletonTree ae
               }

-- | Create an override from an explicit return type and definition using `OverrideSim`.
mkOverride' :: FunctionName
            -> TypeRepr ret
            -> (forall r . OverrideSim p sym ext r args ret (RegValue sym ret))
            -> Override p sym ext args ret
mkOverride' nm tp f =
  Override { overrideName = nm
           , overrideHandler = \s -> runOverrideSim s tp f
           }

-- | Create an override from a statically inferrable return type and definition using `OverrideSim`.
mkOverride :: KnownRepr TypeRepr ret
           => FunctionName
           -> (forall r . OverrideSim p sym ext r args ret (RegValue sym ret))
           -> Override p sym ext args ret
mkOverride nm = mkOverride' nm knownRepr

-- | Return override arguments.
getOverrideArgs :: OverrideSim p sym ext rtp args ret (RegMap sym args)
getOverrideArgs = overrideRegMap <$> use stateOverrideFrame

withSimContext :: StateT (SimContext p sym ext) IO a -> OverrideSim p sym ext rtp args ret a
withSimContext m = do
  ctx <- use stateContext
  (r,ctx') <- liftIO $ runStateT m ctx
  stateContext .= ctx'
  return r

-- | Call a function with the given arguments.
callFnVal :: IsSyntaxExtension ext
          => FnVal sym args ret
          -> RegMap sym args
          -> OverrideSim p sym ext rtp a r (RegEntry sym ret)
callFnVal cl args = do
  Sim $ StateContT $ \c s -> do
    let bindings = s^.stateContext^.functionBindings
    case resolveCallFrame bindings cl args of
      SomeOF o f -> do
        overrideHandler o $ s & stateTree %~ callFn (returnToOverride c) (OF f)
      SomeCF f -> do
        loopCrucible $ s & stateTree %~ callFn (returnToOverride c) (MF f)

-- | Call a function with the given arguments.  Provide the arguments as an
--   @Assignment@ instead of as a @RegMap@.
callFnVal' ::
  IsSyntaxExtension ext =>
  FnVal sym args ret ->
  Ctx.Assignment (RegValue' sym) args ->
  OverrideSim p sym ext rtp a r (RegValue sym ret)
callFnVal' cl args =
  do let FunctionHandleRepr tps _ = fnValType cl
     let args' = Ctx.zipWith (\tp (RV x) -> RegEntry tp x) tps args
     regValue <$> callFnVal cl (RegMap args')

-- | Call a control flow graph from OverrideSim.
--
-- Note that this computes the postdominator information, so there is some
-- performance overhead in the call.
callCFG  :: IsSyntaxExtension ext
         => CFG ext blocks init ret
         -> RegMap sym init
         -> OverrideSim p sym ext rtp a r (RegEntry sym ret)
callCFG cfg args = do
  Sim $ StateContT $ \c s -> do
    let f = mkCallFrame cfg (postdomInfo cfg) args
    loopCrucible $ s & stateTree %~ callFn (returnToOverride c) (MF f)

--------------------------------------------------------------------------------
-- FnBinding

-- | A pair containing a handle and the state associated to execute it.
data FnBinding p sym ext where
  FnBinding :: FnHandle args ret
            -> FnState p sym ext args ret
            -> FnBinding p sym ext

-- | Add function binding to map.
insertFnBinding :: FunctionBindings p sym ext
                -> FnBinding p sym ext
                -> FunctionBindings p sym ext
insertFnBinding m (FnBinding h s) = insertHandleMap h s m

-- | Build a map of function bindings from a list of
--   handle/binding pairs.
fnBindingsFromList :: [FnBinding p sym ext] -> FunctionBindings p sym ext
fnBindingsFromList = foldl' insertFnBinding emptyHandleMap

registerFnBinding :: FnBinding p sym ext
                   -> OverrideSim p sym ext rtp a r ()
registerFnBinding (FnBinding h s) = bindFnHandle h s

--------------------------------------------------------------------------------
-- AnyFnBindings

-- | This quantifies over function bindings that can work for any symbolic interface.
data AnyFnBindings ext = AnyFnBindings (forall p sym . IsSymInterface sym => [FnBinding p sym ext])

--------------------------------------------------------------------------------
-- Intrinsic utility definitions

type IntrinsicImpl p sym ext args ret =
  IsSymInterface sym => FnHandle args ret -> Override p sym ext args ret

useIntrinsic :: FnHandle args ret
             -> (FnHandle args ret -> Override p sym ext args ret)
             -> FnBinding p sym ext
useIntrinsic hdl impl = FnBinding hdl (UseOverride (impl hdl))

-- | Make an IntrinsicImpl from an explicit implementation
mkIntrinsic
    :: forall p sym ext args ret
     . (Ctx.CurryAssignmentClass args)
    => (forall r. Proxy r
               -> sym
               -> Ctx.CurryAssignment args
                    (RegEntry sym)
                    (OverrideSim p sym ext r args ret (RegValue sym ret)))
        -- ^ Override implementation, given a proxy value to fix the type, a
        -- reference to the symbolic engine, and a curried arguments
    -> FnHandle args ret
    -> Override p sym ext args ret
mkIntrinsic m hdl = mkOverride' (handleName hdl) (handleReturnType hdl) ovr
 where
   ovr :: forall r. OverrideSim p sym ext r args ret (RegValue sym ret)
   ovr = do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (m (Proxy :: Proxy r) sym) args
