------------------------------------------------------------------------
-- |
-- Module      : Lang.Crucible.Simulator.MSSim
-- Description : Definition of the simulator monad
-- Copyright   : (c) Galois, Inc 2014
-- Maintainer  : Joe Hendrix <jhendrix@galois.com>
-- Stability   : provisional
-- License     : BSD3
--
-- Here we define the main simulation monad MSSim and basic operations on it.
------------------------------------------------------------------------
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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.MSSim
  ( -- * MSSim
    MSSim(..)
  , init_MSS_State
  , runMSSim
  , SimResult
  , getContext
  , getSymInterface
  , getPathConditions
  , registerFnBinding
  , registerFnBinding'
  , runWithFallback
    -- * Simulator context
  , SimContext
  , ctxIntrinsicMuxFns
  , initSimContext
  , printHandle
  , SimConfigMonad
  , SimConfig
  , simConfig
  , simHandleAllocator
  , ctxSymInterface
  , isSolverProof
  , IsSymInterfaceProof
  , FunctionBindings
  , functionBindings
  , errorHandler
    -- * Simulator state
  , SimState(..)
  , MSS_State
  , stateContext
  , stateConfig
  , mssRunErrorHandler
  , mssRunGenericErrorHandler
  , MSSBranchTarget(..)
    -- * GlobalVariables
  , SymGlobalState
  , emptyGlobals
  , lookupGlobal
  , insertGlobal
  , readGlobal
  , writeGlobal
    -- * Reference cells
  , newRef
  , writeRef
  , readRef
  , insertRef
  , lookupRef
    -- * SimFrame
  , SimFrame(..)
    -- * Function state
  , FnState(..)
    -- * Record for variables created.
  , VarRecord(..)
  , varRecordToValue
    -- * Error handler
  , ErrorHandler(..)
    -- * Crucible execution
  , CrucibleLang
    -- * Function bindings
  , FnBinding(..)
  , insertFnBinding
  , fnBindingsFromList
    -- * Overrides
  , OverrideLang
  , OverrideFrame(..)
  , OverrideSim
  , runOverrideSim
  , run
  , stateOverrideFrame
  , Override(..)
  , mkOverride
  , mkOverride'
  , getOverrideArgs
  , withSimContext
    -- * Intrinsic implementations
  , IntrinsicImpl
  , useIntrinsic
  , mkIntrinsic
  , AnyFnBindings(..)
  , filterCrucibleFrames
  , ppExceptionContext
  ) where

import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.List (foldl')
import qualified Data.Parameterized.Map as MapF
import           Data.Proxy
import           System.IO
import           System.IO.Error
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Parameterized.Context as Ctx

import           Lang.Crucible.Config
import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Simulator.VarRecord
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Utils.MonadST
import           Lang.Crucible.Utils.MonadVerbosity
import           Lang.Crucible.Utils.StateContT


------------------------------------------------------------------------
-- SimState

-- | An MSS_State contains the execution context, an error handler, and
-- the current execution tree.
data SimState ctx sym rtp f (args :: Maybe (Ctx CrucibleType))
   = SimState { _stateContext :: !(ctx sym)
               , returnAbortFn :: !(sym -> rtp -> IO rtp)
               , returnMergeFn :: !(sym -> MuxFn (Pred sym) rtp)
                 -- ^ Describes how to merge the ultimate return value.
               , _errorHandler :: !(ErrorHandler ctx sym rtp)
               , _stateTree :: !(ActiveTree (SimState ctx sym) rtp rtp f args)
               }

newtype ErrorHandler ctx sym rtp
      = EH { runEH :: forall l args
                   . SimError
                   -> SimState ctx sym rtp l args
                   -> IO (ExecResult (SimState ctx sym) rtp)
           }

type instance Solver (SimState ctx sym) = sym
type instance Frame (SimState ctx sym) = SimFrame sym
type instance StateResult (SimState ctx sym) = ctx sym
type instance GlobalState (SimState ctx sym) = SymGlobalState sym

------------------------------------------------------------------------
-- SimState lens

-- | View a sim context.
stateContext :: Simple Lens (SimState ctx s r f a) (ctx s)
stateContext = lens _stateContext (\s v -> s { _stateContext = v })
{-# INLINE stateContext #-}

errorHandler :: Simple Lens (SimState ctx s r f a) (ErrorHandler ctx s r)
errorHandler = lens _errorHandler (\s v -> s { _errorHandler = v })

------------------------------------------------------------------------
-- FnState

-- | State used to indicate what to do when function is called.
data FnState sym (args :: Ctx CrucibleType) (ret :: CrucibleType)
   = UseOverride !(Override sym args ret)
   | forall blocks . UseCFG !(CFG blocks args ret) !(CFGPostdom blocks)

------------------------------------------------------------------------
-- CrucibleLang

-- | Nominal type for defining type of Crucible frames.
data CrucibleLang (blocks :: Ctx (Ctx CrucibleType)) (ret :: CrucibleType)

type instance BranchTarget (CrucibleLang blocks ret) = MSSBranchTarget blocks ret

data MSSBranchTarget blocks (ret :: CrucibleType) (args :: Maybe (Ctx CrucibleType)) where
   BlockTarget  :: BlockID blocks args -> MSSBranchTarget blocks ret ('Just args)
   ReturnTarget :: MSSBranchTarget blocks ret 'Nothing

instance TestEquality (MSSBranchTarget blocks ret) where
  testEquality (BlockTarget x) (BlockTarget y) =
    case testEquality x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  testEquality (ReturnTarget ) (ReturnTarget ) = Just Refl
  testEquality _ _ = Nothing

------------------------------------------------------------------------
-- Override

-- | Nominal type for identifying override frames in execution tree.
data OverrideLang (args :: Ctx CrucibleType) (ret :: CrucibleType)

-- | A definition of function semantics.
data Override sym (args :: Ctx CrucibleType) ret
   = Override { overrideName :: FunctionName
              , overrideHandler
                  :: forall r
                   . MSS_State sym r (OverrideLang args ret) 'Nothing
                  -> IO (SimResult sym r)
              }

------------------------------------------------------------------------
-- SimContext

-- | Global context for state.
data SimContext sym
   = SimContext { _ctxSymInterface       :: !sym
                , ctxIntrinsicMuxFns     :: !(IntrinsicTypes sym)
                , isSolverProof          :: !(forall a . IsSymInterfaceProof sym a)
                , simConfig              :: !(SimConfig sym)
                  -- | Allocator for function handles
                , simHandleAllocator     :: !(HandleAllocator RealWorld)
                  -- | Handle to write messages to.
                , printHandle            :: !Handle
                , _functionBindings      :: !(FunctionBindings sym)
                }

type IsSymInterfaceProof sym a = (IsSymInterface sym => a) -> a

type FunctionBindings sym = FnHandleMap (FnState sym)

-- | Create a new simContext with the given bindings
initSimContext :: IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> SimConfig sym
               -> HandleAllocator RealWorld
               -> Handle -- ^ Handle to write output to
               -> FunctionBindings sym
               -> SimContext sym
initSimContext sym intMuxFns cfg halloc h bindings =
  SimContext { _ctxSymInterface       = sym
             , ctxIntrinsicMuxFns     = intMuxFns
             , isSolverProof          = \a -> a
             , simConfig              = cfg
             , simHandleAllocator     = halloc
             , printHandle            = h
             , _functionBindings      = bindings
             }

-- | A map from function handles to their semantics.
ctxSymInterface :: Simple Lens (SimContext sym) sym
ctxSymInterface = lens _ctxSymInterface (\s v -> s { _ctxSymInterface = v })
{-# INLINE ctxSymInterface #-}

-- | A map from function handles to their semantics.
functionBindings :: Simple Lens (SimContext sym) (FunctionBindings sym)
functionBindings = lens _functionBindings (\s v -> s { _functionBindings = v })

------------------------------------------------------------------------
-- SimConfig

type SimConfigMonad sym = StateT (SimContext sym) IO

type SimConfig sym = Config (SimConfigMonad sym)

instance MonadVerbosity (StateT (SimContext sym) IO) where
  getVerbosity = do
    cfg <- gets simConfig
    liftIO $ getConfigValue verbosity cfg

  getLogFunction = do
    h <- gets printHandle
    verb <- getVerbosity
    return $ \n msg -> do
      when (n <= verb) $ do
        hPutStr h msg
        hFlush h
  showWarning msg = do
    h <- gets printHandle
    liftIO $ hPutStrLn h msg
    liftIO $ hFlush h


------------------------------------------------------------------------
-- OverrideFrame

-- | Frame in call to override.
data OverrideFrame sym (ret :: CrucibleType) args
   = OverrideFrame { override :: !FunctionName
                   , overrideRegMap :: !(RegMap sym args)
                     -- ^ Arguments to override.
--                   , overrideCont :: !(s r (OverrideLang args ret) a -> IO (ExecResult s r))
--                     -- ^ Function to run to resume override.
                   }

------------------------------------------------------------------------
-- SimFrame

data SimFrame sym l (args :: Maybe (Ctx CrucibleType)) where
  OF :: OverrideFrame sym ret args
     -> SimFrame sym (OverrideLang args ret) 'Nothing
  MF :: CallFrame sym blocks ret args
     -> SimFrame sym (CrucibleLang blocks ret) ('Just args)
  RF :: RegEntry sym ret
     -> SimFrame sym (CrucibleLang blocks ret) 'Nothing

overrideSimFrame :: Lens (SimFrame sym (OverrideLang a r) 'Nothing)
                         (SimFrame sym (OverrideLang a r) 'Nothing)
                         (OverrideFrame sym r a)
                         (OverrideFrame sym r a)
overrideSimFrame f (OF g) = OF <$> f g

------------------------------------------------------------------------
-- SymGlobalState

-- | A map from global variables to their value.
--   The integer value is the number of symbolic branches
--   currently pending.  We use this primarily as a sanity check
--   to help find bugs where we fail to match up calls to
--   globalPushBranch with globalAbortBranch/globalMuxFn
data SymGlobalState sym =
  GlobalState
  { _globalPendingBranches :: Int
  , globalMap             :: MapF.MapF GlobalVar (GlobalEntry sym)
  , globalReferenceMap    :: MapF.MapF RefCell (GlobalEntry sym)
  }

newtype GlobalEntry sym tp = GlobalEntry { globalEntryValue :: RegValue sym tp }

-- | The empty set of global variable bindings
emptyGlobals :: SymGlobalState sym
emptyGlobals = GlobalState 0 MapF.empty MapF.empty

-- | Lookup a global in the state
lookupGlobal :: GlobalVar tp -> SymGlobalState sym -> Maybe (RegValue sym tp)
lookupGlobal g gst = globalEntryValue <$> MapF.lookup g (globalMap gst)

-- | Set the value of a global in the state.
insertGlobal :: GlobalVar tp
             -> RegValue sym tp
             -> SymGlobalState sym
             -> SymGlobalState sym
insertGlobal g v gst = gst{ globalMap = MapF.insert g (GlobalEntry v) (globalMap gst) }

-- | Lookup the value of a reference cell in the state
lookupRef :: RefCell tp -> SymGlobalState sym -> Maybe (RegValue sym tp)
lookupRef r gst = globalEntryValue <$> MapF.lookup r (globalReferenceMap gst)

-- | Set the value of a reference cell in the state
insertRef :: RefCell tp
          -> RegValue sym tp
          -> SymGlobalState sym
          -> SymGlobalState sym
insertRef r v gst =
   gst{ globalReferenceMap = MapF.insert r (GlobalEntry v) (globalReferenceMap gst) }


readGlobal :: GlobalVar tp
           -> MSSim sym rtp l args (RegValue sym tp)
readGlobal g = do
   s <- get
   let t  = getSimTree s
   let globals = t^.actFrame^.gpGlobals
   case lookupGlobal g globals of
     Just v -> return v
     Nothing -> fail $ "Attempt to read undefined global " ++ show g

writeGlobal :: GlobalVar tp
            -> RegValue sym tp
            -> MSSim sym rtp l args ()
writeGlobal g v = do
   s <- get
   let t  = getSimTree s
   let t' = t & actFrame . gpGlobals %~ insertGlobal g v
   let s' = setSimTree t' s
   put s'


newRef :: TypeRepr tp
       -> RegValue sym tp
       -> MSSim sym rtp l args (RefCell tp)
newRef tpr v = do
   s <- get
   let halloc = simHandleAllocator (s^.stateContext)
   r <- liftST (freshRefCell halloc tpr)
   writeRef r v
   return r

writeRef :: RefCell tp
         -> RegValue sym tp
         -> MSSim sym rtp l args ()
writeRef r v = do
   s <- get
   let t  = getSimTree s
   let t' = t & actFrame . gpGlobals %~ insertRef r v
   let s' = setSimTree t' s
   put s'

readRef :: RefCell tp
        -> MSSim sym rtp l args (RegValue sym tp)
readRef r = do
   s <- get
   let t  = getSimTree s
   let globals = t^.actFrame^.gpGlobals
   case lookupRef r globals of
     Just v -> return v
     Nothing -> fail $ "Attempt to read undefined reference cell"


muxGlobalState :: forall sym
                . IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> Pred sym
               -> SymGlobalState sym
               -> SymGlobalState sym
               -> IO (SymGlobalState sym)
muxGlobalState sym iteFns c (GlobalState dx x refs_x) (GlobalState dy y refs_y)
 | dx > 0 && dx == dy = do
      GlobalState (dx - 1) <$> MapF.mergeWithKeyM muxEntry checkNullMap checkNullMap x y
                           <*> MapF.mergeWithKeyM muxRef return return refs_x refs_y

    where muxEntry :: GlobalVar tp
                   -> GlobalEntry sym tp
                   -> GlobalEntry sym tp
                   -> IO (Maybe (GlobalEntry sym tp))
          muxEntry g (GlobalEntry u) (GlobalEntry v) =
            Just . GlobalEntry <$> muxRegForType sym iteFns (globalType g) c u v

          muxRef :: RefCell tp
                 -> GlobalEntry sym tp
                 -> GlobalEntry sym tp
                 -> IO (Maybe (GlobalEntry sym tp))
          muxRef r (GlobalEntry u) (GlobalEntry v) =
            Just . GlobalEntry <$> muxRegForType sym iteFns (refType r) c u v

          checkNullMap :: MapF.MapF GlobalVar (GlobalEntry sym)
                       -> IO (MapF.MapF GlobalVar (GlobalEntry sym))
          checkNullMap m
            | MapF.null m = return m
            | otherwise = fail "Different global variables in each branch."

muxGlobalState sym _ _ (GlobalState dx _ _) (GlobalState dy _ _) = do
  loc <- getCurrentProgramLoc sym
  fail $ unwords
     ["Attempting to merge global states of incorrect branch depths: "
     , show dx
     , show dy
     , show $ plSourceLoc loc
     ]

pushBranchGlobalState :: forall sym
                . IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> SymGlobalState sym
               -> IO (SymGlobalState sym)
pushBranchGlobalState sym iTypes (GlobalState d g refs) = do
  g' <- MapF.traverseWithKey
         (\v e -> GlobalEntry <$>
                   pushBranchForType sym iTypes
                     (globalType v)
                     (globalEntryValue e))
         g
  refs' <- MapF.traverseWithKey
            (\r e -> GlobalEntry <$>
                     pushBranchForType sym iTypes
                       (refType r)
                       (globalEntryValue e))
           refs

  --loc <- getCurrentProgramLoc sym
  --putStrLn $ unwords ["PUSH BRANCH:", show d, show $ plSourceLoc loc]
  return (GlobalState (d+1) g' refs')

abortBranchGlobalState :: forall sym
                . IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> SymGlobalState sym
               -> IO (SymGlobalState sym)
abortBranchGlobalState sym iTypes (GlobalState d g refs)
  | d > 0 = do
      g' <- MapF.traverseWithKey
             (\v e -> GlobalEntry <$>
                       abortBranchForType sym iTypes
                         (globalType v)
                         (globalEntryValue e))
             g
      refs' <- MapF.traverseWithKey
                (\r e -> GlobalEntry <$>
                       abortBranchForType sym iTypes
                         (refType r)
                         (globalEntryValue e))
                refs

      --loc <- getCurrentProgramLoc sym
      --putStrLn $ unwords ["ABORT BRANCH:", show (d-1), show $ plSourceLoc loc]
      return (GlobalState (d-1) g' refs')

  | otherwise = do
      loc <- getCurrentProgramLoc sym
      fail $ unwords
         ["Attempting to commit global changes at incorrect branch depth"
         , show d
         , show $ plSourceLoc loc
         ]

filterCrucibleFrames :: SomeFrame (SimFrame sym)
                     -> Maybe ProgramLoc
filterCrucibleFrames (SomeFrame (MF f)) = Just (frameProgramLoc f)
filterCrucibleFrames _ = Nothing

-- | Print the exception
ppExceptionContext :: [SomeFrame (SimFrame sym)] -> SimError -> Doc
ppExceptionContext frames e =
  case frames of
    [_] -> ppSimError e
    SomeFrame (OF f):_ ->
        text ("When calling " ++ show nm ++ ":") <$$>
        indent 2 (ppSimError e)
      where nm = override f
    _ -> ppSimError e

--------------------------------------------------------------------------
-- FnBinding

-- | A pair containing a handle and the state associated to execute it.
data FnBinding sym where
  FnBinding :: FnHandle args ret
            -> FnState sym args ret
            -> FnBinding sym

-- | Add function binding to map.
insertFnBinding :: FunctionBindings sym
                -> FnBinding sym
                -> FunctionBindings sym
insertFnBinding m (FnBinding h s) = insertHandleMap h s m

-- | Build a map of function bindings from a list of
--   handle/binding pairs.
fnBindingsFromList :: [FnBinding sym] -> FunctionBindings sym
fnBindingsFromList = foldl' insertFnBinding emptyHandleMap

------------------------------------------------------------------------
-- MSS_State

type family FrameRetType (f :: *) :: CrucibleType where
  FrameRetType (CrucibleLang b r) = r
  FrameRetType (OverrideLang b r) = r

type instance ReturnType (SimState ctx sym) f = RegEntry sym (FrameRetType f)

-- | An MSS_State contains the execution context, an error handler, and
-- the current execution tree.
type MSS_State = SimState SimContext

instance HasSimState (MSS_State sym) where
  stateSymInterface s = s^.stateContext^.ctxSymInterface
  getSimTree = _stateTree
  setSimTree v s = s { _stateTree = v }

  stateResult s = s^.stateContext

  globalMuxFn s =
      isSolverProof ctx $
        muxGlobalState (ctx^.ctxSymInterface) (ctxIntrinsicMuxFns ctx)
    where ctx = s^.stateContext

  globalPushBranch s =
      isSolverProof ctx $
        pushBranchGlobalState (ctx^.ctxSymInterface) (ctxIntrinsicMuxFns ctx)
    where ctx = s^.stateContext

  globalAbortBranch s =
      isSolverProof ctx $
        abortBranchGlobalState (ctx^.ctxSymInterface) (ctxIntrinsicMuxFns ctx)
    where ctx = s^.stateContext


  returnAbortBranch s =
      isSolverProof ctx $
        abortBranchRegEntry (ctx^.ctxSymInterface) (ctxIntrinsicMuxFns ctx)
    where ctx = s^.stateContext

  returnMuxFn s =
      isSolverProof ctx $
        muxRegEntry (ctx^.ctxSymInterface) (ctxIntrinsicMuxFns ctx)
    where ctx = s^.stateContext


-- | Return config associated with state.
stateConfig :: MSS_State sym rtp f args -> SimConfig sym
stateConfig s = simConfig (s^.stateContext)

------------------------------------------------------------------------
-- MSSim

type SimResult sym = ExecResult (MSS_State sym)

-- | Monad for running symbolic simulator.
newtype MSSim sym rtp l args a
      = Sim { unSim :: StateContT (MSS_State sym rtp l args) (SimResult sym rtp) IO a }
  deriving ( Functor
           , Applicative
           , MonadState (MSS_State sym rtp l args)
           )

runMSSim :: MSSim sym rtp l args a
         -> (a -> MSS_State sym rtp l args -> IO (SimResult sym rtp))
         -> MSS_State sym rtp l args
         -> IO (SimResult sym rtp)
runMSSim (Sim m) c s = runStateContT m c s

returnMSSim :: a -> MSSim sym rtp f args a
returnMSSim v = Sim $ return v
{-# INLINE returnMSSim #-}

bindMSSim :: MSSim sym rtp f args a
          -> (a -> MSSim sym rtp f args b)
          -> MSSim sym rtp f args b
bindMSSim (Sim m) h = Sim $ unSim . h =<< m
{-# INLINE bindMSSim #-}

-- | Start running the error handler.
mssRunErrorHandler :: MSS_State sym rtp l args
                   -> SimError
                   -> IO (SimResult sym rtp)
mssRunErrorHandler s err = runEH (s^.errorHandler) err s

mssRunGenericErrorHandler
     :: MSS_State sym rtp l args
     -> String
     -> IO (SimResult sym rtp)
mssRunGenericErrorHandler s msg = do
  let sym = s^.stateContext^.ctxSymInterface
  loc <- isSolverProof (s^.stateContext) $ do
            getCurrentProgramLoc sym
  let err = SimError loc (GenericSimError msg)
  mssRunErrorHandler s err

instance Monad (MSSim sym rtp f args) where
  return = returnMSSim
  (>>=) = bindMSSim
  fail msg = Sim $ StateContT $ \_c s -> mssRunGenericErrorHandler s msg

instance MonadST RealWorld (MSSim sym rtp f args) where
  liftST m = liftIO $ stToIO m

instance MonadIO (MSSim sym rtp f args) where
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

getContext :: MSSim sym rtp f args (SimContext sym)
getContext = Sim $ use stateContext
{-# INLINE getContext #-}

getSymInterface :: MSSim sym rtp f args sym
getSymInterface = Sim $ use (stateContext . ctxSymInterface)

-- | Return predicates that must be satisfiable for path to be feasible.
getPathConditions :: MSSim sym rtp l a [Pred sym]
getPathConditions = do
  s <- get
  return (pathConditions (s^.simTree^.actContext))

-- | Associate a definition with the given handle.
registerFnBinding -- :: (KnownCtx TypeRepr args, KnownRepr TypeRepr ret)
                  :: FnHandle args ret
                  -> FnState sym args ret
                  -> MSSim sym rtp l a ()
registerFnBinding h s = do
  stateContext . functionBindings %= insertHandleMap h s

registerFnBinding' :: FnBinding sym
                   -> MSSim sym rtp l a ()
registerFnBinding' (FnBinding h s) = registerFnBinding h s

instance MonadVerbosity (MSSim sym rtp f args) where
  getVerbosity = do
    cfg <- simConfig <$> getContext
    liftIO $ getConfigValue verbosity cfg
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

runWithFallback :: forall sym rtp l args
                 . MSSim sym rtp l args ()
                -> (forall r l' args' . SimError -> MSS_State sym r l' args' -> IO ())
                -> MSSim sym rtp l args ()
runWithFallback action fallback = do
  Sim $ StateContT $ \c s -> do
    let oldEH = s^.errorHandler
    let onError :: ErrorHandler SimContext sym rtp
        onError = EH $ \e s0 -> do
          let s' = s0 & errorHandler .~ oldEH
          -- If this was the last execution path, then print out a message and return.
          if isSingleCont (s'^.simTree^.actContext) then do
            fallback e s'
            c () s
           else
            -- Otherwise, we let MSS do whatever it would normally do,
            -- in the absence of the REPL.
            runEH oldEH e s'
    -- Try to run the code
    let cont v s' = c v $ s' & errorHandler .~ oldEH
    runMSSim action cont $ s & errorHandler .~ onError

------------------------------------------------------------------------
-- Override utilities

type OverrideSim sym rtp args ret = MSSim sym rtp (OverrideLang args ret) 'Nothing

runOverrideSim :: TypeRepr tp
               -> OverrideSim sym rtp args tp (RegValue sym tp)
               -> MSS_State sym rtp (OverrideLang args tp) 'Nothing
               -> IO (SimResult sym rtp)
runOverrideSim tp (Sim (StateContT m)) s0 = do
  isSolverProof (s0^.stateContext) $ m (\v s -> returnValue s (RegEntry tp v)) s0

-- | Run an override sim.
init_MSS_State :: SimContext sym
               -> SymGlobalState sym
                  -- ^ Global state
               -> ErrorHandler SimContext sym (RegEntry sym ret)
               -> MSS_State sym (RegEntry sym ret) (OverrideLang EmptyCtx ret) 'Nothing
init_MSS_State ctx globals eh = isSolverProof ctx $
  let startFrame = OverrideFrame { override = startFunctionName
                                 , overrideRegMap = emptyRegMap
                                 }
      ae = GlobalPair (OF startFrame) globals
   in SimState { _stateContext = ctx
               , returnMergeFn = \sym ->
                 muxRegEntry sym (ctxIntrinsicMuxFns ctx)
               , returnAbortFn = \sym ->
                 abortBranchRegEntry sym (ctxIntrinsicMuxFns ctx)
               , _errorHandler = eh
               , _stateTree = singletonTree ae
               }

-- | Run an override sim.
run :: SimContext sym
    -> SymGlobalState sym
       -- ^ Global state
    -> ErrorHandler SimContext sym (RegEntry sym rtp)
    -> TypeRepr rtp
    -> OverrideSim sym (RegEntry sym rtp) EmptyCtx rtp (RegValue sym rtp)
    -> IO (SimResult sym (RegEntry sym rtp))
run ctx globals eh rtp code = do
  let active_state = init_MSS_State ctx globals eh
  runOverrideSim rtp code active_state

mkOverride' :: FunctionName
           -> TypeRepr ret
           -> (forall r
               . IsSymInterface sym
               => OverrideSim sym r args ret (RegValue sym ret))
           -> Override sym args ret
mkOverride' nm tp f = Override nm $ \s ->
  isSolverProof (s^.stateContext) $ runOverrideSim tp f s


mkOverride :: KnownRepr TypeRepr ret
           => FunctionName
           -> (forall r
               . IsSymInterface sym
               => OverrideSim sym r args ret (RegValue sym ret))
           -> Override sym args ret
mkOverride nm = mkOverride' nm knownRepr

-- | View a sim context.
stateOverrideFrame :: Lens (MSS_State s q (OverrideLang a r) 'Nothing)
                           (MSS_State s q (OverrideLang a r) 'Nothing)
                           (OverrideFrame s r a)
                           (OverrideFrame s r a)
stateOverrideFrame = simTree . actFrame . gpValue . overrideSimFrame

-- | Return override arguments.
getOverrideArgs :: OverrideSim sym rtp args ret (RegMap sym args)
getOverrideArgs = overrideRegMap <$> use stateOverrideFrame

withSimContext :: StateT (SimContext sym) IO a -> MSSim sym rtp f args a
withSimContext m = do
  ctx <- use stateContext
  (r,ctx') <- liftIO $ runStateT m ctx
  stateContext .= ctx'
  return r

--------------------------------------------------------------------------------
-- Intrinsic utility definitions

data AnyFnBindings = AnyFnBindings (forall sym . IsSymInterface sym => [FnBinding sym])

type IntrinsicImpl sym args ret =
  IsSymInterface sym => FnHandle args ret -> Override sym args ret

useIntrinsic :: FnHandle args ret
             -> (FnHandle args ret -> Override sym args ret)
             -> FnBinding sym
useIntrinsic hdl impl = FnBinding hdl (UseOverride (impl hdl))

-- | Make an IntrinsicImpl from an explicit implementation
mkIntrinsic
    :: forall sym args ret
     . (Ctx.CurryAssignmentClass args, KnownRepr TypeRepr ret)
    => (forall r. Proxy r
               -> sym
               -> Ctx.CurryAssignment args
                    (RegEntry sym)
                    (OverrideSim sym r args ret (RegValue sym ret)))
        -- ^ Override implementation, given a proxy value to fix the type, a
        -- reference to the symbolic engine, and a curried arguments
    -> FnHandle args ret
    -> Override sym args ret
mkIntrinsic m hdl = mkOverride (handleName hdl) ovr
 where
   ovr :: forall r. OverrideSim sym r args ret (RegValue sym ret)
   ovr = do
       sym <- getSymInterface
       (RegMap args) <- getOverrideArgs
       Ctx.uncurryAssignment (m (Proxy :: Proxy r) sym) args
