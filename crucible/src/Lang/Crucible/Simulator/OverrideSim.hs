{-|
Module      : Lang.Crucible.Simulator.OverrideSim
Description : The main simulation monad
Copyright   : (c) Galois, Inc 2014-2018
License     : BSD3
Maintainer  : Joe Hendrix <jhendrix@galois.com>

Define the main simulation monad 'OverrideSim' and basic operations on it.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
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
    -- * Monad operations
  , withSimContext
  , getContext
  , getSymInterface
  , bindFnHandle
  , exitExecution
  , getOverrideArgs
  , overrideError
  , overrideAbort
  , symbolicBranch
  , symbolicBranches
  , overrideReturn
  , overrideReturn'
    -- * Function calls
  , callFnVal
  , callFnVal'
  , callCFG
  , callBlock
  , callOverride
    -- * Global variables
  , readGlobal
  , writeGlobal
  , readGlobals
  , writeGlobals
  , modifyGlobal
    -- * References
  , newRef
  , newEmptyRef
  , readRef
  , writeRef
  , modifyRef
  , readMuxTreeRef
  , writeMuxTreeRef
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
import           Control.Monad hiding (fail)
#if !(MIN_VERSION_base(4,13,0))
import qualified Control.Monad.Fail as Fail (fail)
import           Control.Monad.Fail (MonadFail)
#endif
import qualified Control.Monad.Catch as X
import           Control.Monad.Reader hiding (fail)
import           Control.Monad.ST
import           Control.Monad.State.Strict hiding (fail)
import           Data.List (foldl')
import qualified Data.Parameterized.Context as Ctx
import           Data.Proxy
import qualified Data.Text as T
import           System.Exit
import           System.IO
import           System.IO.Error

import           What4.Config
import           What4.Interface
import           What4.Partial (justPartExpr)
import           What4.Utils.MonadST

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Panic(panic)

import           Lang.Crucible.Backend
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import qualified Lang.Crucible.Simulator.EvalStmt as EvalStmt (readRef, alterRef)
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Operations
                   ( runGenericErrorHandler, runErrorHandler, runAbortHandler
                   , returnValue, callFunction, overrideSymbolicBranch )
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Utils.MonadVerbosity
import           Lang.Crucible.Utils.MuxTree (MuxTree)
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
newtype OverrideSim p sym ext rtp (args :: Ctx CrucibleType) (ret :: CrucibleType) a
      = Sim { unSim :: StateContT (SimState p sym ext rtp (OverrideLang ret) ('Just args))
                                  (ExecState p sym ext rtp)
                                  IO
                                  a
            }
  deriving ( Functor
           , Applicative
           )

-- | Exit from the current execution by ignoring the continuation
--   and immediately returning an aborted execution result.
exitExecution :: IsSymInterface sym => ExitCode -> OverrideSim p sym ext rtp args r a
exitExecution ec = Sim $ StateContT $ \_c s ->
  return $ ResultState $ AbortedResult (s^.stateContext) (AbortedExit ec)

returnOverrideSim :: a -> OverrideSim p sym ext rtp args r a
returnOverrideSim v = Sim $ return v
{-# INLINE returnOverrideSim #-}

bindOverrideSim ::
  OverrideSim p sym ext rtp args r a ->
  (a -> OverrideSim p sym ext rtp args r b) ->
  OverrideSim p sym ext rtp args r b
bindOverrideSim (Sim m) h = Sim $ unSim . h =<< m
{-# INLINE bindOverrideSim #-}

instance Monad (OverrideSim p sym ext rtp args r) where
  return = returnOverrideSim
  (>>=) = bindOverrideSim
#if !(MIN_VERSION_base(4,13,0))
  fail = Fail.fail
#endif

deriving instance MonadState (SimState p sym ext rtp (OverrideLang ret) ('Just args))
                             (OverrideSim p sym ext rtp args ret)

instance MonadFail (OverrideSim p sym ext rtp args ret) where
  fail msg = Sim $ StateContT $ \_c -> runGenericErrorHandler msg


instance MonadIO (OverrideSim p sym ext rtp args ret) where
  liftIO m = do
     Sim $ StateContT $ \c s -> do
       -- FIXME, should we be doing this exception handling here, or should
       -- we just continue to let it bubble upward?
       r <- try m
       case r of
         Left e0
           -- IO Exception
           | Just e <- fromException e0
           , isUserError e ->
             runGenericErrorHandler (ioeGetErrorString e) s
             -- AbortReason
           | Just e <- fromException e0 ->
             runAbortHandler e s
             -- Default case
           | otherwise ->
             throwIO e0
         Right v -> c v s

instance MonadST RealWorld (OverrideSim p sym ext rtp args ret) where
  liftST m = liftIO $ stToIO m

instance MonadCont (OverrideSim p sym ext rtp args ret) where
  callCC f = Sim $ callCC (\k -> unSim (f (\a -> Sim (k a))))

instance X.MonadThrow (OverrideSim p sym ext rtp args ret) where
  throwM = liftIO . throwIO

getContext :: OverrideSim p sym ext rtp args ret (SimContext p sym ext)
getContext = use stateContext
{-# INLINE getContext #-}

getSymInterface :: OverrideSim p sym ext rtp args ret sym
getSymInterface = use stateSymInterface

instance MonadVerbosity (OverrideSim p sym ext rtp args ret) where
  getVerbosity =
    do ctx <- getContext
       let cfg = ctxSolverProof ctx (getConfiguration (ctx^.ctxSymInterface))
       v <- liftIO (getOpt =<< getOptionSetting verbosity cfg)
       return (fromInteger v)

  getLogFunction =
    do h <- printHandle <$> getContext
       verb <- getVerbosity
       return $ \n msg -> do
         when (n <= verb) $ do
           hPutStr h msg
           hFlush h
  showWarning msg =
    do h <- printHandle <$> getContext
       liftIO $
         do hPutStrLn h msg
            hFlush h

-- | Associate a definition (either an 'Override' or a 'CFG') with the given handle.
bindFnHandle ::
  FnHandle args ret ->
  FnState p sym ext args ret ->
  OverrideSim p sym ext rtp a r ()
bindFnHandle h s =
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
  IsSymInterface sym =>
  GlobalVar tp                                     {- ^ global variable -} ->
  OverrideSim p sym ext rtp args ret (RegValue sym tp) {- ^ current value   -}
readGlobal k =
  do globals <- use (stateTree . actFrame . gpGlobals)
     case lookupGlobal k globals of
       Just v  -> return v
       Nothing -> panic "OverrideSim.readGlobal"
                          [ "Attempt to read undefined global."
                          , "*** Global name: " ++ show k
                          ]

-- | Set the value of a particular global variable.
writeGlobal ::
  GlobalVar tp    {- ^ global variable -} ->
  RegValue sym tp {- ^ new value       -} ->
  OverrideSim p sym ext rtp args ret ()
writeGlobal g v = stateTree . actFrame . gpGlobals %= insertGlobal g v


-- | Run an action to compute the new value of a global.
modifyGlobal ::
  IsSymInterface sym =>
  GlobalVar tp    {- ^ global variable to modify -} ->
  (RegValue sym tp ->
    OverrideSim p sym ext rtp args ret (a, RegValue sym tp)) {- ^ modification action -} ->
  OverrideSim p sym ext rtp args ret a
modifyGlobal gv f =
  do x <- readGlobal gv
     (a, x') <- f x
     writeGlobal gv x'
     return a

-- | Create a new reference cell.
newRef ::
  IsSymInterface sym =>
  TypeRepr tp {- ^ Type of the reference cell -} ->
  RegValue sym tp {- ^ Initial value of the cell -} ->
  OverrideSim p sym ext rtp args ret (RefCell tp)
newRef tpr v =
  do r <- newEmptyRef tpr
     writeRef r v
     return r

-- | Create a new reference cell with no contents.
newEmptyRef ::
  TypeRepr tp {- ^ Type of the reference cell -} ->
  OverrideSim p sym ext rtp args ret (RefCell tp)
newEmptyRef tpr =
  do halloc <- use (stateContext . to simHandleAllocator)
     liftIO $ freshRefCell halloc tpr

-- | Read the current value of a reference cell.
readRef ::
  IsSymInterface sym =>
  RefCell tp {- ^ Reference cell to read -} ->
  OverrideSim p sym ext rtp args ret (RegValue sym tp)
readRef r =
  do sym <- getSymInterface
     globals <- use (stateTree . actFrame . gpGlobals)
     let msg = ReadBeforeWriteSimError "Attempt to read undefined reference cell"
     liftIO $ readPartExpr sym (lookupRef r globals) msg

-- | Write a value into a reference cell.
writeRef ::
  IsSymInterface sym =>
  RefCell tp {- ^ Reference cell to write -} ->
  RegValue sym tp {- ^ Value to write into the cell -} ->
  OverrideSim p sym ext rtp args ret ()
writeRef r v =
  do sym <- getSymInterface
     stateTree . actFrame . gpGlobals %= insertRef sym r v

modifyRef ::
  IsSymInterface sym =>
  RefCell tp {- ^ Reference cell to modify -} ->
  (RegValue sym tp ->
    OverrideSim p sym ext rtp args ret (a, RegValue sym tp)) {- ^ modification action -} ->
  OverrideSim p sym ext rtp args ret a
modifyRef ref f =
  do x <- readRef ref
     (a, x') <- f x
     writeRef ref x'
     return a


-- | Read the current value of a mux tree of reference cells.
readMuxTreeRef ::
  IsSymInterface sym =>
  TypeRepr tp ->
  MuxTree sym (RefCell tp) {- ^ Reference cell to read -} ->
  OverrideSim p sym ext rtp args ret (RegValue sym tp)
readMuxTreeRef tpr r =
  do sym <- getSymInterface
     iTypes <- ctxIntrinsicTypes <$> use stateContext
     globals <- use (stateTree . actFrame . gpGlobals)
     liftIO $ EvalStmt.readRef sym iTypes tpr r globals

-- | Write a value into a mux tree of reference cells.
writeMuxTreeRef ::
  IsSymInterface sym =>
  TypeRepr tp ->
  MuxTree sym (RefCell tp) {- ^ Reference cell to write -} ->
  RegValue sym tp {- ^ Value to write into the cell -} ->
  OverrideSim p sym ext rtp args ret ()
writeMuxTreeRef tpr r v =
  do sym <- getSymInterface
     iTypes <- ctxIntrinsicTypes <$> use stateContext
     globals <- use (stateTree . actFrame . gpGlobals)
     globals' <- liftIO $ EvalStmt.alterRef sym iTypes tpr r (justPartExpr sym v) globals
     stateTree . actFrame . gpGlobals .= globals'


-- | Turn an 'OverrideSim' action into an 'ExecCont' that can be executed
--   using standard Crucible execution primitives like 'executeCrucible'.
runOverrideSim ::
  TypeRepr tp {- ^ return type -} ->
  OverrideSim p sym ext rtp args tp (RegValue sym tp) {- ^ action to execute  -} ->
  ExecCont p sym ext rtp (OverrideLang tp) ('Just args)
runOverrideSim tp m = ReaderT $ \s0 -> stateSolverProof s0 $
  runStateContT (unSim m) (\v -> runReaderT (returnValue (RegEntry tp v))) s0


-- | Create an override from an explicit return type and definition using 'OverrideSim'.
mkOverride' ::
  FunctionName ->
  TypeRepr ret ->
  (forall r . OverrideSim p sym ext r args ret (RegValue sym ret)) ->
  Override p sym ext args ret
mkOverride' nm tp f =
  Override { overrideName = nm
           , overrideHandler = runOverrideSim tp f
           }

-- | Create an override from a statically inferrable return type and definition using 'OverrideSim'.
mkOverride ::
  KnownRepr TypeRepr ret =>
  FunctionName ->
  (forall r . OverrideSim p sym ext r args ret (RegValue sym ret)) ->
  Override p sym ext args ret
mkOverride nm = mkOverride' nm knownRepr

-- | Return override arguments.
getOverrideArgs :: OverrideSim p sym ext rtp args ret (RegMap sym args)
getOverrideArgs = use (stateOverrideFrame.overrideRegMap)

withSimContext :: StateT (SimContext p sym ext) IO a -> OverrideSim p sym ext rtp args ret a
withSimContext m =
  do ctx <- use stateContext
     (r,ctx') <- liftIO $ runStateT m ctx
     stateContext .= ctx'
     return r

-- | Call a function with the given arguments.
callFnVal ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  FnVal sym args ret {- ^ Function to call -} ->
  RegMap sym args {- ^ Arguments to the function -} ->
  OverrideSim p sym ext rtp a r (RegEntry sym ret)
callFnVal cl args =
  Sim $ StateContT $ \c -> runReaderT $ do
    sym <- view stateSymInterface
    loc <- liftIO $ getCurrentProgramLoc sym
    callFunction cl args (ReturnToOverride c) loc

-- | Call a function with the given arguments.  Provide the arguments as an
--   @Assignment@ instead of as a @RegMap@.
callFnVal' ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  FnVal sym args ret {- ^ Function to call -} ->
  Ctx.Assignment (RegValue' sym) args {- ^ Arguments to the function -} ->
  OverrideSim p sym ext rtp a r (RegValue sym ret)
callFnVal' cl args =
  do let FunctionHandleRepr tps _ = fnValType cl
     let args' = Ctx.zipWith (\tp (RV x) -> RegEntry tp x) tps args
     regValue <$> callFnVal cl (RegMap args')

-- | Call a control flow graph from 'OverrideSim'.
--
-- Note that this computes the postdominator information, so there is some
-- performance overhead in the call.
callCFG ::
  IsSyntaxExtension ext =>
  CFG ext blocks init ret {- ^ Function to run -} ->
  RegMap sym init {- ^ Arguments to the function -} ->
  OverrideSim p sym ext rtp a r (RegEntry sym ret)
callCFG cfg = callBlock cfg (cfgEntryBlockID cfg)

-- | Call a block of a control flow graph from 'OverrideSim'.
--
-- Note that this computes the postdominator information, so there is some
-- performance overhead in the call.
callBlock ::
  IsSyntaxExtension ext =>
  CFG ext blocks init ret {- ^ Function to run -} ->
  BlockID blocks args {- ^ Block to run -} ->
  RegMap sym args {- ^ Arguments to the block -} ->
  OverrideSim p sym ext rtp a r (RegEntry sym ret)
callBlock cfg bid args =
  Sim $ StateContT $ \c -> runReaderT $
    let f = mkBlockFrame cfg bid (postdomInfo cfg) args in
    ReaderT $ return . CallState (ReturnToOverride c) (CrucibleCall bid f)

-- | Call an override in a new call frame.
callOverride ::
  FnHandle args ret ->
  Override p sym ext args ret ->
  RegMap sym args ->
  OverrideSim p sym ext rtp a r (RegEntry sym ret)
callOverride h ovr args =
  Sim $ StateContT $ \c -> runReaderT $
    let f = OverrideFrame (overrideName ovr) (SomeHandle h) args in
    ReaderT $ return . CallState (ReturnToOverride c) (OverrideCall ovr f)


-- | Add a failed assertion.  This aborts execution along the current
-- evaluation path, and adds a proof obligation ensuring that we can't get here
-- in the first place.
overrideError :: IsSymInterface sym => SimErrorReason -> OverrideSim p sym ext rtp args res a
overrideError err = Sim $ StateContT $ \_ -> runErrorHandler err


-- | Abort the current thread of execution for the given reason.  Unlike @overrideError@,
--   this operation will not add proof obligation, even if the given abort reason
--   is due to an assertion failure.  Use @overrideError@ instead if a proof obligation
--   should be generated.
overrideAbort :: AbortExecReason -> OverrideSim p sym ext rtp args res a
overrideAbort abt = Sim $ StateContT $ \_ -> runAbortHandler abt

overrideReturn :: KnownRepr TypeRepr res => RegValue sym res -> OverrideSim p sym ext rtp args res a
overrideReturn v = Sim $ StateContT $ \_ -> runReaderT $ returnValue (RegEntry knownRepr v)

overrideReturn' :: RegEntry sym res -> OverrideSim p sym ext rtp args res a
overrideReturn' v = Sim $ StateContT $ \_ -> runReaderT $ returnValue v

-- | Perform a symbolic branch on the given predicate.  If we can determine
--   that the predicate must be either true or false, we will exeucte only
--   the "then" or the "else" branch.  Otherwise, both branches will be executed
--   and the results merged when a value is returned from the override.  NOTE!
--   this means the code following this symbolic branch may be executed more than
--   once; in particular, side effects may happen more than once.
--
--   In order to ensure that push/abort/mux bookeeping is done properly, all
--   symbolic values that will be used in the branches should be inserted into
--   the @RegMap@ argument of this function, and retrieved in the branches using
--   the @getOverrideArgs@ function.  Otherwise mux errors may later occur, which
--   will be very confusing.  In other words, don't directly use symbolic values
--   computed before calling this function; you must instead first put them into
--   the @RegMap@ and get them out again later.
symbolicBranch ::
  IsSymInterface sym =>
  Pred sym {- ^ Predicate to branch on -} ->

  RegMap sym then_args {- ^ argument values for the then branch -} ->
  OverrideSim p sym ext rtp then_args res a {- ^ then branch -} ->
  Maybe Position {- ^ optional location for then branch -} ->

  RegMap sym else_args {- ^ argument values for the else branch -} ->
  OverrideSim p sym ext rtp else_args res a {- ^ else branch -} ->
  Maybe Position {- ^ optional location for else branch -} ->

  OverrideSim p sym ext rtp args res a
symbolicBranch p thn_args thn thn_pos els_args els els_pos =
  Sim $ StateContT $ \c -> runReaderT $
    do old_args <- view (stateTree.actFrame.overrideTopFrame.overrideRegMap)
       let thn' = ReaderT (runStateContT
                            (unSim thn)
                            (\x st -> c x (st & stateTree.actFrame.overrideTopFrame.overrideRegMap .~ old_args)))
       let els' = ReaderT (runStateContT
                            (unSim els)
                            (\x st -> c x (st & stateTree.actFrame.overrideTopFrame.overrideRegMap .~ old_args)))
       overrideSymbolicBranch p thn_args thn' thn_pos els_args els' els_pos

-- | Perform a series of symbolic branches.  This operation will evaluate a
--   series of branches, one for each element of the list.  The semantics of
--   this construct is that the predicates are evaluated in order, until
--   the first one that evaluates true; this branch will be the taken branch.
--   If no predicate is true, the construct will abort with a @VariantOptionsExhausted@
--   reason.  If you wish to report an error condition instead, you should add a
--   final default case with a true predicate that calls @overrideError@.
--   As with @symbolicBranch@, be aware that code following this operation may be
--   called several times, and side effects may occur more than once.
--
--   As with @symbolicBranch@, any symbolic values needed by the branches should be
--   placed into the @RegMap@ argument and retrieved when needed.  See the comment
--   on @symbolicBranch@.
symbolicBranches :: forall p sym ext rtp args new_args res a.
  IsSymInterface sym =>
  RegMap sym new_args {- ^ argument values for the branches -} ->
  [(Pred sym, OverrideSim p sym ext rtp (args <+> new_args) res a, Maybe Position)]
   {- ^ Branches to consider -} ->
  OverrideSim p sym ext rtp args res a
symbolicBranches new_args xs0 =
  Sim $ StateContT $ \c -> runReaderT $
    do sym <- view stateSymInterface
       top_loc <- liftIO $ getCurrentProgramLoc sym
       old_args <- view (stateTree.actFrame.overrideTopFrame.overrideRegMap)
       let all_args = appendRegs old_args new_args
       let c' x st = c x (st & stateTree.actFrame.overrideTopFrame.overrideRegMap .~ old_args)
       let go _ [] = ReaderT $ runAbortHandler (VariantOptionsExhausted top_loc)
           go !i ((p,m,mpos):xs) =
             let msg = T.pack ("after branch " ++ show i)
                 m'  = ReaderT (runStateContT (unSim m) c')
              in overrideSymbolicBranch p all_args m' mpos old_args (go (i+1) xs) (Just (OtherPos msg))
       go (0::Integer) xs0

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

useIntrinsic ::
  FnHandle args ret ->
  (FnHandle args ret -> Override p sym ext args ret) ->
  FnBinding p sym ext
useIntrinsic hdl impl = FnBinding hdl (UseOverride (impl hdl))

-- | Make an IntrinsicImpl from an explicit implementation
mkIntrinsic :: forall p sym ext args ret.
  Ctx.CurryAssignmentClass args =>
  (forall r. Proxy r
               -> sym
               -> Ctx.CurryAssignment args
                    (RegEntry sym)
                    (OverrideSim p sym ext r args ret (RegValue sym ret)))
    {- ^ Override implementation, given a proxy value to fix the type, a
         reference to the symbolic engine, and a curried arguments -} ->
  FnHandle args ret ->
  Override p sym ext args ret
mkIntrinsic m hdl = mkOverride' (handleName hdl) (handleReturnType hdl) ovr
 where
   ovr :: forall r. OverrideSim p sym ext r args ret (RegValue sym ret)
   ovr = do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (m (Proxy :: Proxy r) sym) args
