-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.ExecutionTree
-- Description      : Data structure the execution state of the simulator
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Execution trees record the state of the simulator as it explores
-- execution paths through a program.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}
module Lang.Crucible.Simulator.ExecutionTree
  ( -- * GlobalPair
    GlobalPair(..)
  , gpValue
  , gpGlobals
  , TopFrame
    -- * AbortedResult
  , AbortedResult(..)
    -- * PartialResult
  , PartialResult(..)
    -- * Frames
  , SomeFrame(..)
  , filterCrucibleFrames
  , arFrames
  , ppExceptionContext
  , abortTree
  , defaultErrorHandler
    -- * ExecResult
  , ExecResult(..)
  , ExecCont
    -- * ActiveTree
  , ActiveTree(ActiveTree)
  , singletonTree
  , actContext
  , activeFrames
    -- ** Active tree helpers.
  , actFrame
    -- ** ValueFromFrame
  , ReturnHandler
  , isSingleCont
  , pathConditions
    -- * Branch information
  , PausedValue(..)
  , PausedFrame(..)
    -- ** Branch and merge at return
  , intra_branch
  , completed_branch
    -- * High level operations.
  , replaceTailFrame
  , getIntraFrameBranchTarget
  , checkForIntraFrameMerge
  , callFn
  , returnValue
  , abortExec
  , extractCurrentPath
  , branchConditions
    -- * SimState
  , SimState(..)
  , stateTree
  , IsSymInterfaceProof
  , ErrorHandler(..)
  , CrucibleBranchTarget(..)
  , errorHandler
  , stateContext
    -- * SimContext
  , Override(..)
  , SimContext(..)
  , initSimContext
  , ctxSymInterface
  , functionBindings
  , cruciblePersonality
  , SimConfig
  , SimConfigMonad
  , FunctionBindings
  , FnState(..)
    -- * Utilities
  , stateSymInterface
  , stateSolverProof
  , stateIntrinsicTypes
  , stateOverrideFrame
  , mssRunErrorHandler
  , mssRunGenericErrorHandler
  ) where

import           Control.Lens
import           Control.Monad.ST (RealWorld)
import           Control.Monad.State.Strict
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Type.Equality hiding (sym)
import           System.Exit (ExitCode)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lang.Crucible.Config
import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle (FnHandleMap, HandleAllocator)
import           Lang.Crucible.FunctionName (FunctionName)
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Frame
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.BoolInterface
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Utils.MonadVerbosity


-- | @swap_unless b (x,y)@ returns @(x,y)@ when @b@ is @True@ and
-- @(y,x)@ when @b@ if @False@.
swap_unless :: Bool -> (a, a) -> (a,a)
swap_unless True p = p
swap_unless False (x,y) = (y,x)
{-# INLINE swap_unless #-}

-- | Return assertion where predicate equals a constant
predEqConst :: IsBoolExprBuilder sym => sym -> Pred sym -> Bool -> IO (Pred sym)
predEqConst _   p True  = return p
predEqConst sym p False = notPred sym p

------------------------------------------------------------------------
-- CrucibleBranchTarget

data CrucibleBranchTarget blocks (args :: Maybe (Ctx CrucibleType)) where
   BlockTarget  :: !(BlockID blocks args)
                -> CrucibleBranchTarget blocks ('Just args)
   ReturnTarget :: CrucibleBranchTarget blocks 'Nothing

instance TestEquality (CrucibleBranchTarget blocks) where
  testEquality (BlockTarget x) (BlockTarget y) =
    case testEquality x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing
  testEquality (ReturnTarget ) (ReturnTarget ) = Just Refl
  testEquality _ _ = Nothing

ppBranchTarget :: CrucibleBranchTarget blocks args -> String
ppBranchTarget (BlockTarget b) = "merge: " ++ show b
ppBranchTarget ReturnTarget = "return"


------------------------------------------------------------------------
-- GlobalPair

-- | A value with a global state associated.
data GlobalPair sym (v :: *) =
   GlobalPair { _gpValue :: !v
              , _gpGlobals :: !(SymGlobalState sym)
              }

-- | The value stored in the global pair.
gpValue :: Lens (GlobalPair sym u) (GlobalPair sym v) u v
gpValue = lens _gpValue (\s v -> s { _gpValue = v })

-- | The globals stored in the global pair.
gpGlobals :: Simple Lens (GlobalPair sym u) (SymGlobalState sym)
gpGlobals = lens _gpGlobals (\s v -> s { _gpGlobals = v })

-- | Merge two globals together.
mergeGlobalPair :: MuxFn p v
                -> MuxFn p (SymGlobalState sym)
                -> MuxFn p (GlobalPair sym v)
mergeGlobalPair merge_fn global_fn c x y =
  GlobalPair <$> merge_fn  c (x^.gpValue) (y^.gpValue)
             <*> global_fn c (x^.gpGlobals) (y^.gpGlobals)

------------------------------------------------------------------------
-- TopFrame

-- | A frame plus the global state associated with it.
type TopFrame sym f a = GlobalPair sym (SimFrame sym f a)

------------------------------------------------------------------------
-- SomeFrame

-- | This represents an execution frame.
data SomeFrame (f :: fk -> argk -> *) = forall l a . SomeFrame !(f l a)

filterCrucibleFrames :: SomeFrame (SimFrame sym)
                     -> Maybe ProgramLoc
filterCrucibleFrames (SomeFrame (MF f)) = Just (frameProgramLoc f)
filterCrucibleFrames _ = Nothing

------------------------------------------------------------------------
-- AbortedResult

-- | An execution that was prematurely aborted.
data AbortedResult sym where
  -- A single aborted execution with the execution state at time of error,
  -- and the reason for the error.
  AbortedExec :: !SimError
              -> !(GlobalPair sym (SimFrame sym l args))
              -> AbortedResult sym
  -- An aborted execution that was ended by a call to 'exit'
  AbortedExit :: !ExitCode
              -> AbortedResult sym

  -- An aborted exeuction that was ended because path conditions became infeasible
  AbortedInfeasible :: AbortedResult sym

  -- An entire aborted branch.
  AbortedBranch :: !(Pred sym)
                -> !(AbortedResult sym)
                -> !(AbortedResult sym)
                -> AbortedResult sym

-- | Iterate over frames in the result.
arFrames :: Simple Traversal (AbortedResult sym) (SomeFrame (SimFrame sym))
arFrames h (AbortedExec e p) =
  (\(SomeFrame f') -> AbortedExec e (p & gpValue .~ f'))
     <$> h (SomeFrame (p^.gpValue))
arFrames _ (AbortedExit ec) = pure (AbortedExit ec)
arFrames _ (AbortedInfeasible) = pure (AbortedInfeasible)
arFrames h (AbortedBranch p r s) =
  AbortedBranch p <$> arFrames h r
                  <*> arFrames h s

-- | Print the exception
ppExceptionContext :: [SomeFrame (SimFrame sym)] -> PP.Doc
ppExceptionContext [] = PP.empty
ppExceptionContext frames = PP.vcat (map pp (init frames))
 where
   pp :: SomeFrame (SimFrame sym) -> PP.Doc
   pp (SomeFrame (OF f)) =
      PP.text ("When calling " ++ show (override f))
   pp (SomeFrame (MF f)) =
      PP.text "In" PP.<+> PP.text (show (frameHandle f)) PP.<+>
      PP.text "at" PP.<+> PP.pretty (plSourceLoc (frameProgramLoc f))
   pp (SomeFrame (RF _v)) =
      PP.text ("While returning value")

-- | Abort the current execution.
abortTree :: SimError -> SimState p sym rtp f args -> IO (ExecResult p sym rtp)
abortTree e s = do
  let t = s^.stateTree
  v <- getConfigValue verbosity (simConfig (s^.stateContext))
  when (v > 0) $ do
    let frames = activeFrames t
    let msg = ppSimError e PP.<$$> PP.indent 2 (ppExceptionContext frames)
    -- Print error message.
    hPrint (printHandle (s^.stateContext)) $ msg
  -- Switch to new frame.
  abortExec e s

defaultErrorHandler :: ErrorHandler p sym rtp
defaultErrorHandler = EH abortTree

------------------------------------------------------------------------
-- PartialResult

-- | 'PartialResult' contains a value and global variables along with an
-- optional aborted result.
data PartialResult sym (v :: *)
   = TotalRes !(GlobalPair sym v)
     -- A partial result, the predicate indicates what must be true to avoid the aborted cases
   | PartialRes !(Pred sym) !(GlobalPair sym v) !(AbortedResult sym)

-- | View the value stored in the partial result.
partialValue :: Lens (PartialResult sym u)
                     (PartialResult sym v)
                     (GlobalPair sym u)
                     (GlobalPair sym v)
partialValue f (TotalRes x) = TotalRes <$> f x
partialValue f (PartialRes p x r) = (\y -> PartialRes p y r) <$> f x
{-# INLINE partialValue #-}

mergeAbortedBranch :: Pred sym
                   -> AbortedResult sym
                   -> AbortedResult sym
                   -> AbortedResult sym
mergeAbortedBranch _ (AbortedExit ec) _ = AbortedExit ec
mergeAbortedBranch _ _ (AbortedExit ec) = AbortedExit ec
mergeAbortedBranch c q r = AbortedBranch c q r

mergePartialAndAbortedResult :: IsBoolExprBuilder sym
                             => sym
                             -> Pred sym
                             -> PartialResult sym v
                             -> AbortedResult sym
                             -> IO (PartialResult sym v)
mergePartialAndAbortedResult sym c ar r =
  case ar of
    TotalRes gp ->
      return $! PartialRes c gp r
    PartialRes d gp q -> do
      e <- andPred sym c d
      return $! PartialRes e gp (mergeAbortedBranch c q r)

mergePartialResult :: forall p sym f root args blocks ret
                   .  SimState p sym f root args
                   -> CrucibleBranchTarget blocks args
                   -> MuxFn (Pred sym)
                        (PartialResult sym (SimFrame sym (CrucibleLang blocks ret) args))
mergePartialResult s tgt pp x y = stateSolverProof s $ do
  let sym = stateSymInterface s
  let iteFns = stateIntrinsicTypes s
  let merge_val = mergeCrucibleFrame sym iteFns tgt
  let merge_fn = mergeGlobalPair merge_val (globalMuxFn sym iteFns)
  case x of
    TotalRes cx ->
      case y of
        TotalRes cy -> do
          TotalRes <$> merge_fn pp cx cy
        PartialRes py cy fy -> do
          PartialRes <$> orPred sym pp py
                     <*> merge_fn pp cx cy
                     ?? fy
    PartialRes px cx fx -> do
      case y of
        TotalRes cy -> do
          pc <- notPred sym pp
          PartialRes <$> orPred sym pc px
                     <*> merge_fn pp cx cy
                     ?? fx
        PartialRes py cy fy -> do
          PartialRes <$> itePred sym pp px py
                     <*> merge_fn pp cx cy
                     ?? AbortedBranch pp fx fy

------------------------------------------------------------------------
-- ExecResult

-- | Executions that have completed either due to (partial or total) successful execution
--   completion or by an error.
--
--   The included predicate indicates the path condition that resulted in the
--   given result.  The final sequence of ExecResult computations are continuations
--   which, if invoked, will explore alternate execution paths.
--
--   In the extreme case where we merge paths at every opportunity, the resulting path condition
--   will just be true and the sequence of continuations will be empty.  In the other extreme,
--   where paths are never merged, each ExecResult will correspond to exactly one path and the
--   returned sequence of continuations represents the current fringe of unexplored paths.
--   Exaustively exeucting each of the continuations will eventually explore the entire path space.
--
--   The sequence of continuations is arranged such that continuations nearer to the front diverge
--   from the returned result least (i.e., have the longest path condition in common).  Entering continuations
--   from the front toward the back should thus require the least amount of state backtracking.
data ExecResult p sym (r :: *)
   = FinishedExecution !(SimContext p sym) !(PartialResult sym r)
   | AbortedResult     !(SimContext p sym) !(AbortedResult sym)

------------------------------------------------------------------------
-- A Paused value and ExecCont

-- | An action with will construct an ExecResult given a global state.
type ExecCont p sym r f a = SimState p sym r f a -> IO (ExecResult p sym r)

-- | This is essentially a closure denoting a type of continuation that needs a
-- global state to run, but currently has a value that it will use to generate
-- the state, along with a solver state used to configure the state of the
-- solver interface.
data PausedValue p sym root f args v
   = PausedValue { _pausedValue :: !v
                 , savedStateInfo :: !(SymPathState sym)
                   -- ^ Saved state information
                 , resume :: !(ExecCont p sym root f args)
                   -- ^ Function to run.
                 }

pausedValue :: Lens (PausedValue p sym root f a u)
                    (PausedValue p sym root f a v)
                    u
                    v
pausedValue = lens _pausedValue (\s v -> s { _pausedValue = v })

prependPausedAction :: (sym -> IO ())
                    -> PausedValue p sym r f a u
                    -> PausedValue p sym r f a u
prependPausedAction m v = v { resume = \s -> m (stateSymInterface s) >> resume v s }

------------------------------------------------------------------------
-- ReurnHandler and CallerCont

-- | This function is used to get a new frame and the continuation
-- containing what to do next when returning from a function.
type ReturnHandler p sym r f new_args
   = (SimFrame sym f new_args, ExecCont p sym r f new_args)

------------------------------------------------------------------------
-- Recursive data types

type PausedPartialFrame p sym root f args
   = PausedValue p sym root f args (PartialResult sym (SimFrame sym f args))

-- | An active execution tree contains at least one active execution.
-- The data structure is organized so that the current execution
-- can be accessed rapidly.
data ActiveTree p sym root f args
   = ActiveTree { _actContext :: !(ValueFromFrame p sym root f)
                , _actResult  :: !(PartialResult sym (SimFrame sym f args))
                }

-- | This describes what to do in an inactive path.
data VFFOtherPath p sym root f args
   = forall o_args
   . VFFActivePath !(PausedPartialFrame p sym root f o_args)
     -- ^ This is a active execution and includes the current frame.
     -- Note: this would need to be made more generic
     -- if we want to be able paths concurrently.
   | VFFCompletePath !(PausedPartialFrame p sym root f args)
     -- ^ This is a completed execution path.


-- | Return saved state info associated with other path.
vffSavedStateInfo :: VFFOtherPath p sym root f args -> SymPathState sym
vffSavedStateInfo (VFFActivePath   p) = savedStateInfo p
vffSavedStateInfo (VFFCompletePath p) = savedStateInfo p

-- | @ValueFromFrame p sym root ret f@ contains the context for a simulator with state @s@,
-- global return type @root@, and top frame with type @f@.
data ValueFromFrame p sym (root :: *) f where
  -- A Branch is a branch where both execution paths still contains
  -- executions that need to continue before merge.
  -- VFFBranch ctx b t denotes @ctx[[] <b> t]@.
  VFFBranch :: !(ValueFromFrame p sym ret (CrucibleLang blocks a))
               -- /\ Outer context.
            -> !(SymPathState sym)
               -- /\ State before this branch
            -> !(Pred sym)
               -- /\ Assertion of current branch
            -> !(VFFOtherPath p sym ret (CrucibleLang blocks a) args)
               -- /\ Other computation
            -> !(CrucibleBranchTarget blocks args)
               -- /\ Identifies where the merge should occur.
            -> ValueFromFrame p sym ret (CrucibleLang blocks a)

  -- A branch where the other child has been aborted.
  -- VFFPartial ctx p r denotes @ctx[[] <p> r]@.
  VFFPartial :: (f ~ CrucibleLang b a)
             => !(ValueFromFrame p sym ret f)
             -> !(Pred sym)
             -> !(AbortedResult sym)
             -> !Bool -- should we abort the sibling branch when it merges with us?
             -> ValueFromFrame p sym ret f

  -- VFFEnd denotes that when the function terminates we should just return
  -- from the function.
  VFFEnd :: !(ValueFromValue p sym root (RegEntry sym (FrameRetType f)))
         -> ValueFromFrame p sym root f

-- | value from value denotes
data ValueFromValue p sym (root :: *) (top_return :: *) where
  -- VFVCall denotes a return to a given frame.
  VFVCall :: !(ValueFromFrame p sym ret caller)
             -- Previous context
          -> !(SimFrame sym caller args)
             -- Frame of caller.
          -> !(top_return -> SimFrame sym caller args -> ReturnHandler p sym ret caller new_args)
             -- Continuation to run.
          -> ValueFromValue p sym ret top_return

  -- A branch where the other child has been aborted.
  -- VFVPartial ctx p r denotes @ctx[[] <p> r]@.
  VFVPartial :: !(ValueFromValue p sym ret top_return)
             -> !(Pred sym)
             -> !(AbortedResult sym)
             -> ValueFromValue p sym ret top_return

  -- The top return value.
  VFVEnd :: ValueFromValue p sym root root

instance PP.Pretty (ValueFromValue p sym root rp) where
  pretty = ppValueFromValue

instance PP.Pretty (ValueFromFrame p sym ret f) where
  pretty = ppValueFromFrame

instance PP.Pretty (VFFOtherPath ctx sym r f a) where
  pretty (VFFActivePath _)   = PP.text "active_path"
  pretty (VFFCompletePath _) = PP.text "complete_path"

ppValueFromFrame :: ValueFromFrame p sym ret f -> PP.Doc
ppValueFromFrame vff =
  case vff of
    VFFBranch ctx _ _ other mp ->
      PP.text "intra_branch" PP.<$$>
      PP.indent 2 (PP.pretty other) PP.<$$>
      PP.indent 2 (PP.text (ppBranchTarget mp)) PP.<$$>
      PP.pretty ctx
    VFFPartial ctx _ _ _ ->
      PP.text "intra_partial" PP.<$$>
      PP.pretty ctx
    VFFEnd ctx ->
      PP.pretty ctx

ppValueFromValue :: ValueFromValue p sym root tp -> PP.Doc
ppValueFromValue vfv =
  case vfv of
    VFVCall ctx _ _ ->
      PP.text "call" PP.<$$>
      PP.pretty ctx
    VFVPartial ctx _ _ ->
      PP.text "inter_partial" PP.<$$>
      PP.pretty ctx
    VFVEnd -> PP.text "root"

------------------------------------------------------------------------
-- parentFrames

-- | Return parents frames in reverse order.
parentFrames :: ValueFromFrame p sym r a -> [SomeFrame (SimFrame sym)]
parentFrames c0 =
  case c0 of
    VFFBranch c _ _ _ _ -> parentFrames c
    VFFPartial c _ _ _ -> parentFrames c
    VFFEnd vfv -> vfvParents vfv

vfvParents :: ValueFromValue p sym r a -> [SomeFrame (SimFrame sym)]
vfvParents c0 =
  case c0 of
    VFVCall c f _ -> SomeFrame f : parentFrames c
    VFVPartial c _ _ -> vfvParents c
    VFVEnd -> []

------------------------------------------------------------------------
-- Utilities

pushCrucibleFrame :: forall sym b r a
                  .  IsExprBuilder sym
                  => sym
                  -> IntrinsicTypes sym
                  -> SimFrame sym (CrucibleLang b r) a
                  -> IO (SimFrame sym (CrucibleLang b r) a)
pushCrucibleFrame sym muxFns (MF x) = do
  r' <- pushBranchRegs sym muxFns (frameRegs x)
  return $! MF x{ frameRegs = r' }
pushCrucibleFrame sym muxFns (RF x) = do
  x' <- pushBranchRegEntry sym muxFns x
  return $! RF x'


popCrucibleFrame :: IsExprBuilder sym
                 => sym
                 -> IntrinsicTypes sym
                 -> SimFrame sym (CrucibleLang b r') a'
                 -> IO (SimFrame sym (CrucibleLang b r') a')
popCrucibleFrame sym intrinsicFns (MF x') = do
  r' <- abortBranchRegs sym intrinsicFns (frameRegs x')
  return $! MF x' { frameRegs = r' }
popCrucibleFrame sym intrinsicFns (RF x') =
  RF <$> abortBranchRegEntry sym intrinsicFns x'

fromJustCallFrame :: SimFrame sym (CrucibleLang b r) ('Just a)
                  -> CallFrame sym b r a
fromJustCallFrame (MF x) = x

fromNothingCallFrame :: SimFrame sym (CrucibleLang b r) 'Nothing
                     -> RegEntry sym r
fromNothingCallFrame (RF x) = x


mergeCrucibleFrame :: IsExprBuilder sym
                   => sym
                   -> IntrinsicTypes sym
                   -> CrucibleBranchTarget blocks args -- ^ Target of branch
                   -> MuxFn (Pred sym) (SimFrame sym (CrucibleLang blocks ret) args)
mergeCrucibleFrame sym muxFns tgt p x0 y0 =
  case tgt of
    BlockTarget _b_id -> do
      let x = fromJustCallFrame x0
      let y = fromJustCallFrame y0
      z <- mergeRegs sym muxFns p (frameRegs x) (frameRegs y)
      pure $! MF (x { frameRegs = z })
    ReturnTarget -> do
      let x = fromNothingCallFrame x0
      let y = fromNothingCallFrame y0
      RF <$> muxRegEntry sym muxFns p x y

------------------------------------------------------------------------
-- pathConditions

-- | Return list of conditions along current execution path.
pathConditions :: ValueFromFrame p sym r a
               -> [Pred sym]
pathConditions c0 =
  case c0 of
    VFFBranch   c _ p _ _ -> p : pathConditions c
    VFFPartial  c p _ _   -> p : pathConditions c
    VFFEnd vfv            -> vfvConditions vfv

-- | Get the path conditions from the valueFromValue context
vfvConditions :: ValueFromValue p sym r a
              -> [Pred sym]
vfvConditions c0 =
  case c0 of
    VFVCall c _ _ -> pathConditions c
    VFVPartial c p _ -> p : vfvConditions c
    VFVEnd -> []

------------------------------------------------------------------------
-- Resuming frames

-- | Resume a paused frame.
resumeFrame :: SimState p sym r g b
            -> PausedPartialFrame p sym r f a
            -> ValueFromFrame p sym r f
            -> IO (ExecResult p sym r)
resumeFrame s pv ctx = resume pv $ s & stateTree .~ ActiveTree ctx er
  where er = pv^.pausedValue
{-# INLINABLE resumeFrame #-}

------------------------------------------------------------------------
-- | Checking for intra-frame merge.

-- | Return branch target if there is one.
getIntraFrameBranchTarget :: ValueFromFrame p sym root (CrucibleLang b a)
                          -> Maybe (Some (CrucibleBranchTarget b))
getIntraFrameBranchTarget vff0 =
  case vff0 of
  VFFBranch _ _ _ _ tgt -> Just (Some tgt)
  VFFPartial ctx _ _ _ -> getIntraFrameBranchTarget ctx
  VFFEnd{} -> Nothing

abortPartialResult
   :: SimState p sym r f args
   -> PartialResult sym (SimFrame sym (CrucibleLang b r') a')
   -> IO (PartialResult sym (SimFrame sym (CrucibleLang b r') a'))
abortPartialResult s pr = stateSolverProof s $ do
  let sym = stateSymInterface s
  let muxFns = stateIntrinsicTypes s
  let abtGp (GlobalPair v g) =
        GlobalPair <$> popCrucibleFrame sym muxFns v
                   <*> globalAbortBranch sym muxFns g
  partialValue abtGp pr

-- | Checks for the opportunity to merge within a frame.
--
-- This should be called everytime the current control flow location changes.
-- It will return the computation to run after merging.
checkForIntraFrameMerge
  :: forall p sym root b r args
   . ExecCont p sym root (CrucibleLang b r) args
     -- ^ What to run for next computation
  -> CrucibleBranchTarget b args
     -- ^ The location of the current block.
  -> SimState p sym root (CrucibleLang b r) args
    -- ^ Current tree.
  -> IO (ExecResult p sym root)
checkForIntraFrameMerge active_cont tgt s = stateSolverProof s $ do
  let ActiveTree ctx0 er = s^.stateTree
  let sym = stateSymInterface s
  case ctx0 of
    VFFBranch ctx old_state p some_next tgt'
      | Just Refl <- testEquality tgt tgt' -> do
        -- Adjust state info.
        -- Merge the two results together.
        case some_next of
          VFFActivePath next -> do
            sym_state <- getCurrentState sym
            pnot <- notPred sym p
            switchCurrentState sym old_state (savedStateInfo next)
            let paused_res :: PausedPartialFrame p sym root (CrucibleLang b r) args
                paused_res = PausedValue { _pausedValue = er
                                         , savedStateInfo = sym_state
                                         , resume = active_cont
                                         }
            resumeFrame s next (VFFBranch ctx old_state pnot (VFFCompletePath paused_res) tgt)
          VFFCompletePath other -> do
            -- Get location where branch occured
            -- Merge results together
            ar <- mergePartialResult s tgt p er (other^.pausedValue)
            -- Check for more potential merge targets.
            let s' = s & stateTree .~ ActiveTree ctx ar
            checkForIntraFrameMerge active_cont tgt s'

    VFFPartial ctx p ar shouldAbort -> do
      er'  <- if shouldAbort then
                abortPartialResult s er
              else
                return er
      er'' <- mergePartialAndAbortedResult sym p er' ar
      let s' = s & stateTree .~ ActiveTree ctx er''
      checkForIntraFrameMerge active_cont tgt s'
    _ -> active_cont s


--------------------------------------------------------------------------------
-- Branching

newtype PausedFrame p sym root f args
      = PausedFrame (PausedValue p sym root f args (TopFrame sym f args))

runWithCurrentState :: SimState p sym r f a
                    -> ValueFromFrame p sym r f
                    -> Some (PausedFrame p sym r f)
                    -> IO (ExecResult p sym r)
runWithCurrentState s ctx (Some (PausedFrame pf)) = do
  resume pf $ s & stateTree .~ ActiveTree ctx (TotalRes (pf^.pausedValue))
{-# INLINABLE runWithCurrentState #-}

pushBranchVal :: (f ~ CrucibleLang b a)
              => SimState p sym root f ma
              -> PausedFrame p sym root f args
              -> IO (PausedFrame p sym root f args)
pushBranchVal s (PausedFrame pv) = stateSolverProof s $ do
  let sym = stateSymInterface s
  let iTypes = stateIntrinsicTypes s
  let GlobalPair v gs = pv^.pausedValue
  v' <- pushCrucibleFrame sym iTypes v
  gs' <- globalPushBranch sym iTypes gs
  return $! PausedFrame (pv & pausedValue .~ GlobalPair v' gs')

-- | Branch with a merge point inside this frame.
--
-- The false branch is known to be at the merge point.
-- This may merge frames, and will call the error handler if merging fails.
completed_branch :: SimState p sym r (CrucibleLang b a) dc_args
                    -- ^ Current state
                 -> Pred sym
                    -- ^ Predicate on current branch
                 -> (SymPathState sym -> Some (PausedFrame p sym r (CrucibleLang b a)))
                    -- ^ Returns exec for true branch.
                 -> (SymPathState sym -> PausedFrame p sym r (CrucibleLang b a) args)
                    -- ^ Returns exec for false branch.
                 -> CrucibleBranchTarget  b args
                    -- ^ Target to merge at.
                 -> IO (ExecResult p sym r)
completed_branch s p t_fn f_fn tgt = stateSolverProof s $ do
  let ctx = asContFrame (s^.stateTree)
  let sym = stateSymInterface s
  r <- evalBranch sym p
  -- Get current state
  cur_state <- getCurrentState sym
  case r of
    -- If we are symbolic, then we ignore chosen_branch.
    -- f_fn has already reached the merge point, and thus we must run t_fn next.
    SymbolicBranch _ -> do
      -- Pause result.
      active_frame <- traverseSome (pushBranchVal s) $ t_fn cur_state
      PausedFrame paused_frame <- pushBranchVal s $ f_fn cur_state

      let set_f sym' = pushBranchPred sym' =<< notPred sym' p
      let paused_res  = paused_frame & prependPausedAction set_f
                                     & pausedValue %~ TotalRes
      -- Mark branch as completed.
      let ctx' = VFFBranch ctx cur_state p (VFFCompletePath paused_res) tgt
      -- Execute on true branch.
      pushBranchPred sym p
      runWithCurrentState s ctx' active_frame

    NoBranch True -> do
      sym_state <- getCurrentState sym
      runWithCurrentState s ctx (t_fn sym_state)

    NoBranch False -> do
      sym_state <- getCurrentState sym
      let PausedFrame pf = f_fn sym_state
      let s' = s & stateTree .~ ActiveTree ctx (TotalRes (pf^.pausedValue))
      checkForIntraFrameMerge (resume pf) tgt s'
    InfeasibleBranch ->
      resumeValueFromFrameAbort s ctx AbortedInfeasible
{-# INLINABLE completed_branch #-}

-- | Branch with a merge point inside this frame.
intra_branch :: SimState p sym r (CrucibleLang b a) dc_args
                -- ^ Current execution state
             -> Pred sym
                -- ^ Information about branch
             -> (SymPathState sym -> Some (PausedFrame p sym r (CrucibleLang b a)))
                -- ^ true branch.
             -> (SymPathState sym -> Some (PausedFrame p sym r (CrucibleLang b a)))
                -- ^ false branch.
             -> CrucibleBranchTarget b (args :: Maybe (Ctx CrucibleType))
                -- ^ Information for merge
             -> IO (ExecResult p sym r)
intra_branch s p t_fn f_fn tgt = stateSolverProof s $ do
  let ctx = asContFrame (s^.stateTree)
  let sym = stateSymInterface s
  r <- evalBranch sym p
  cur_state <- getCurrentState sym
  case r of
    SymbolicBranch chosen_branch -> do
      -- Get correct predicate
      p' <- predEqConst sym p chosen_branch
      -- Get current state
      t_frame <- traverseSome (pushBranchVal s) $ t_fn cur_state
      f_frame <- traverseSome (pushBranchVal s) $ f_fn cur_state

      -- Select correct branch
      case swap_unless chosen_branch (t_frame, f_frame) of
        (a_state, Some (PausedFrame o_frame)) -> do
          -- Create context for paused frame.
          let set_f sym' = pushBranchPred sym' =<< notPred sym' p'
          let o_tree = o_frame & prependPausedAction set_f
                               & pausedValue %~ TotalRes
          let ctx' = VFFBranch ctx cur_state p' (VFFActivePath o_tree) tgt
          -- Start a_state (where branch pred is p')
          pushBranchPred sym p'
          runWithCurrentState s ctx' a_state

    NoBranch chosen_branch -> do
      -- Execute on active branch.
      let a_state | chosen_branch = t_fn cur_state
                  | otherwise     = f_fn cur_state
      runWithCurrentState s ctx a_state
    InfeasibleBranch ->
      resumeValueFromFrameAbort s ctx AbortedInfeasible
{-# INLINABLE intra_branch #-}

------------------------------------------------------------------------
-- ValueFromFrame

-- | Returns true if tree contains a single non-aborted execution.
isSingleCont :: ValueFromFrame p sym root a -> Bool
isSingleCont c0 =
  case c0 of
    VFFBranch{} -> False
    VFFPartial c _ _ _ -> isSingleCont c
    VFFEnd vfv -> isSingleVFV vfv

isSingleVFV :: ValueFromValue p sym r a -> Bool
isSingleVFV c0 = do
  case c0 of
    VFVCall c _ _ -> isSingleCont c
    VFVPartial c _ _ -> isSingleVFV c
    VFVEnd -> True

-- | Attempt to unwind a frame context into a value context.
--   This succeeds only if there are no pending symbolic
--   merges.
unwindContext :: ValueFromFrame p sym root f
              -> Maybe (ValueFromValue p sym root (RegEntry sym (FrameRetType f)))
unwindContext c0 =
    case c0 of
      VFFBranch{} -> Nothing
      VFFPartial _ _ _ True -> Nothing
      VFFPartial d p ar False ->
        (\d' -> VFVPartial d' p ar) <$> unwindContext d
      VFFEnd vfv -> return vfv

-- | Get the context for when returning (assumes no
-- intra-procedural merges are possible).
returnContext :: ValueFromFrame ctx sym root f
              -> ValueFromValue ctx sym root (RegEntry sym (FrameRetType f))
returnContext c0 =
    case unwindContext c0 of
      Just vfv -> vfv
      Nothing -> errorMsg
  where errorMsg =
          error $ "Unexpected attempt to exit function before all "
               ++ "intra-procedural merges are complete.\n"
               ++ "The call stack was:\n"
               ++ show (PP.pretty c0)

-- | Replace the given frame with a new frame.  Succeeds
--   only if there are no pending symbolic merge points.
replaceTailFrame :: forall p sym a b c args args'
                  . FrameRetType a ~ FrameRetType c
                 => ActiveTree p sym b a args
                 -> SimFrame sym c args'
                 -> Maybe (ActiveTree p sym b c args')
replaceTailFrame (ActiveTree c er) f = do
    vfv <- unwindContext c
    return $ ActiveTree (VFFEnd vfv) (er & partialValue . gpValue .~ f)

------------------------------------------------------------------------
-- ActiveTree

-- | Create a tree with a single top frame.
singletonTree :: TopFrame sym f args
              -> ActiveTree p
                            sym
                            (RegEntry sym (FrameRetType f))
                            f
                            args
singletonTree f = ActiveTree { _actContext = VFFEnd VFVEnd
                             , _actResult = TotalRes f
                             }

actContext :: Lens (ActiveTree p sym b a a_args)
                   (ActiveTree p sym b a a_args)
                   (ValueFromFrame p sym b a)
                   (ValueFromFrame p sym b a)
actContext = lens _actContext (\s v -> s { _actContext = v })

actResult :: Lens (ActiveTree p sym root b args0)
                  (ActiveTree p sym root b args1)
                  (PartialResult sym (SimFrame sym b args0))
                  (PartialResult sym (SimFrame sym b args1))
actResult = lens _actResult setter
  where setter s v = ActiveTree { _actContext = _actContext s
                                , _actResult = v
                                }
{-# INLINE actResult #-}

actFrame :: Lens (ActiveTree p sym root b args)
                 (ActiveTree p sym root b args')
                 (TopFrame sym b args)
                 (TopFrame sym b args')
actFrame = actResult . partialValue
{-# INLINE actFrame #-}

-- | Return the context of the current top frame.
asContFrame :: (f ~ CrucibleLang b a)
            => ActiveTree     p sym ret f args
            -> ValueFromFrame p sym ret f
asContFrame (ActiveTree ctx active_res) =
  case active_res of
    TotalRes{} -> ctx
    PartialRes p _ex ar -> VFFPartial ctx p ar False

activeFrames :: ActiveTree ctx sym root a args -> [SomeFrame (SimFrame sym)]
activeFrames (ActiveTree ctx ar) =
  SomeFrame (ar^.partialValue^.gpValue) : parentFrames ctx

callFn :: (RegEntry sym (FrameRetType a)
           -> SimFrame sym f old_args
           -> ReturnHandler p sym r f new_args)
       -> SimFrame sym a args
       -> ActiveTree p sym r f old_args
       -> ActiveTree p sym r a args
callFn h f' (ActiveTree ctx er) =
    ActiveTree (VFFEnd (VFVCall ctx old_frame h)) $ er'
  where old_frame   = er^.partialValue^.gpValue
        er' = er & partialValue . gpValue .~ f'

------------------------------------------------------------------------
-- Return a value

-- | Return value from current execution.
--
-- NOTE: All symbolic branching must be resolved before calling `returnValue`.
returnValue :: SimState p sym r f a
            -> RegEntry sym (FrameRetType f)
            -> IO (ExecResult p sym r)
returnValue s v = do
  let ActiveTree ctx er = s^.stateTree
  handleSimReturn s (returnContext ctx) $ er & partialValue . gpValue .~ v

handleSimReturn :: SimState p sym r f a
                -> ValueFromValue p sym r ret
                   -- ^ Context to return to.
                -> PartialResult sym ret
                   -- ^ Value that is being returned.
                -> IO (ExecResult p sym r)
handleSimReturn s ctx0 return_value = stateSolverProof s $ do
  case ctx0 of
    VFVCall ctx g h -> do
      let vt = return_value^.partialValue
      let (f, c) = h (vt^.gpValue) g
      let s' = s & stateTree .~ ActiveTree ctx (return_value & partialValue . gpValue .~ f)
      c $! s'
    VFVPartial ctx p r -> stateSolverProof s $ do
      updated_return_value <- mergePartialAndAbortedResult (stateSymInterface s) p return_value r
      handleSimReturn s ctx updated_return_value
    VFVEnd -> return $! FinishedExecution (stateResult s) return_value

------------------------------------------------------------------------
-- Aborting an execution.

-- | Abort the current execution, and either return or switch to next
-- execution path and run it.
abortExec :: SimError
          -> SimState p sym (r :: *) f args
          -> IO (ExecResult p sym r)
abortExec rsn s = do
  let ActiveTree ctx ar0 = s^.stateTree
  -- Get aborted result from active result.
  let ar = case ar0 of
             TotalRes e -> AbortedExec rsn e
             PartialRes c ex ar1 -> AbortedBranch c (AbortedExec rsn ex) ar1
  resumeValueFromFrameAbort s ctx ar

-- | Resolve the fact that the top execution is now aborted.
--
-- This may merge frames, and will throw a user error if merging fails.
resumeValueFromFrameAbort :: SimState p sym r g args
                          -> ValueFromFrame p sym r f
                          -> AbortedResult sym
                             -- ^ The execution that is being aborted.
                          -> IO (ExecResult p sym r)
resumeValueFromFrameAbort s ctx0 ar0 = stateSolverProof s $ do
  let sym = stateSymInterface s
  case ctx0 of
    VFFBranch ctx old_state p some_next tgt -> do
      -- Restore the old state.
      switchCurrentState sym old_state (vffSavedStateInfo some_next)
      -- Negate branch condition and add to context.
      pnot <- notPred sym p
      let nextCtx = VFFPartial ctx pnot ar0 True

      -- Add assertion that path condition holds
      addAssertion sym pnot FailedPathSimError

      -- Resume other branch.
      case some_next of
        VFFActivePath   n -> do
          resumeFrame s n nextCtx
        VFFCompletePath pv -> do
          let er = pv^.pausedValue
          let s' = s & stateTree .~ ActiveTree nextCtx er
          checkForIntraFrameMerge (resume pv) tgt s'
    VFFPartial ctx p ay _ -> do
      resumeValueFromFrameAbort s ctx (AbortedBranch p ar0 ay)
    VFFEnd ctx -> do
      resumeValueFromValueAbort s ctx ar0

-- | Run rest of execution given a value from value context and an aborted
-- result.
resumeValueFromValueAbort :: IsSymInterface sym
                          => SimState p sym (r :: *) f a
                          -> ValueFromValue p sym r ret'
                          -> AbortedResult sym
                          -> IO (ExecResult p sym r)
resumeValueFromValueAbort s ctx0 ar0 = do
  case ctx0 of
    VFVCall ctx _ _ -> do
      -- Pop out of call context.
      resumeValueFromFrameAbort s ctx ar0
    VFVPartial ctx p ay -> do
      resumeValueFromValueAbort s ctx (AbortedBranch p ar0 ay)
    VFVEnd -> return $ AbortedResult (stateResult s) ar0

------------------------------------------------------------------------
-- extractCurrentPath

-- | Create a tree that contains just a single path with no branches.
--
-- All branch conditions are converted to assertions.
extractCurrentPath :: ActiveTree p sym ret f args
                   -> ActiveTree p sym ret f args
extractCurrentPath t =
  ActiveTree (vffSingleContext (t^.actContext))
             (TotalRes (t^.actResult^.partialValue))

vffSingleContext :: ValueFromFrame p sym ret f
                 -> ValueFromFrame p sym ret f
vffSingleContext ctx0 =
  case ctx0 of
    VFFBranch ctx _ _ _ _   -> vffSingleContext ctx
    VFFPartial ctx _ _ _    -> vffSingleContext ctx
    VFFEnd ctx              -> VFFEnd (vfvSingleContext ctx)

vfvSingleContext :: ValueFromValue p sym root top_ret
                 -> ValueFromValue p sym root top_ret
vfvSingleContext ctx0 =
  case ctx0 of
    VFVCall ctx f h         -> VFVCall (vffSingleContext ctx) f h
    VFVPartial ctx _ _      -> vfvSingleContext ctx
    VFVEnd                  -> VFVEnd

------------------------------------------------------------------------
-- branchConditions

-- | Return all branch conditions along path to this node.
branchConditions :: ActiveTree ctx sym ret f args -> [Pred sym]
branchConditions t =
  case t^.actResult of
    TotalRes _ -> vffBranchConditions (t^.actContext)
    PartialRes p _ _ -> p : vffBranchConditions (t^.actContext)

vffBranchConditions :: ValueFromFrame p sym ret f
                    -> [Pred sym]
vffBranchConditions ctx0 =
  case ctx0 of
    VFFBranch   ctx _ p _ _  -> p : vffBranchConditions ctx
    VFFPartial  ctx p _ _    -> p : vffBranchConditions ctx
    VFFEnd  ctx -> vfvBranchConditions ctx

vfvBranchConditions :: ValueFromValue p sym root top_ret
                    -> [Pred sym]
vfvBranchConditions ctx0 =
  case ctx0 of
    VFVCall     ctx _ _      -> vffBranchConditions ctx
    VFVPartial  ctx p _      -> p : vfvBranchConditions ctx
    VFVEnd                   -> []


------------------------------------------------------------------------
-- FrameRetType

type family FrameRetType (f :: *) :: CrucibleType where
  FrameRetType (CrucibleLang b r) = r
  FrameRetType (OverrideLang b r) = r

-- | A map from function handles to their semantics.
type FunctionBindings p sym = FnHandleMap (FnState p sym)

------------------------------------------------------------------------
-- SimContext

-- | Global context for state.
data SimContext personality sym
   = SimContext { _ctxSymInterface       :: !sym
                , ctxSolverProof         :: !(forall a . IsSymInterfaceProof sym a)
                , ctxIntrinsicTypes :: !(IntrinsicTypes sym)

                , simConfig              :: !(SimConfig personality sym)
                  -- | Allocator for function handles
                , simHandleAllocator     :: !(HandleAllocator RealWorld)
                  -- | Handle to write messages to.
                , printHandle            :: !Handle
                , _functionBindings      :: !(FunctionBindings personality sym)

                , _cruciblePersonality   :: !(personality sym)
                }

-- | A definition of function semantics.
data Override p sym (args :: Ctx CrucibleType) ret
   = Override { overrideName :: FunctionName
              , overrideHandler
                  :: forall r
                   . SimState p sym r (OverrideLang args ret) 'Nothing
                  -> IO (ExecResult p sym r)
              }

-- | State used to indicate what to do when function is called.
data FnState p sym (args :: Ctx CrucibleType) (ret :: CrucibleType)
   = UseOverride !(Override p sym args ret)
   | forall blocks . UseCFG !(CFG blocks args ret) !(CFGPostdom blocks)

type SimConfigMonad p sym = StateT (SimContext p sym) IO
type SimConfig p sym = Config (SimConfigMonad p sym)

------------------------------------------------------------------------
-- SimContext utilities

-- | Create a new 'SimContext' with the given bindings.
initSimContext :: IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> SimConfig personality sym
               -> HandleAllocator RealWorld
               -> Handle -- ^ Handle to write output to
               -> FunctionBindings personality sym
               -> personality sym
               -> SimContext personality sym
initSimContext sym muxFns cfg halloc h bindings personality =
  SimContext { _ctxSymInterface     = sym
             , ctxSolverProof       = \a -> a
             , ctxIntrinsicTypes = muxFns
             , simConfig            = cfg
             , simHandleAllocator   = halloc
             , printHandle          = h
             , _functionBindings    = bindings
             , _cruciblePersonality = personality
             }

ctxSymInterface :: Simple Lens (SimContext p sym) sym
ctxSymInterface = lens _ctxSymInterface (\s v -> s { _ctxSymInterface = v })

-- | A map from function handles to their semantics.
functionBindings :: Simple Lens (SimContext p sym) (FunctionBindings p sym)
functionBindings = lens _functionBindings (\s v -> s { _functionBindings = v })

cruciblePersonality :: Simple Lens (SimContext p sym) (p sym)
cruciblePersonality = lens _cruciblePersonality (\s v -> s{ _cruciblePersonality = v })


------------------------------------------------------------------------
-- MonadVerbosity instance

instance MonadVerbosity (StateT (SimContext p sym) IO) where
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
-- SimState

type IsSymInterfaceProof sym a = (IsSymInterface sym => a) -> a

-- | A SimState contains the execution context, an error handler, and
-- the current execution tree.
data SimState p sym rtp f (args :: Maybe (Ctx.Ctx CrucibleType))
   = SimState { _stateContext      :: !(SimContext p sym)
              , _errorHandler      :: !(ErrorHandler p sym rtp)
              , _stateTree         :: !(ActiveTree p sym rtp f args)
              }

newtype ErrorHandler p sym rtp
      = EH { runEH :: forall (l :: *) args
                   . SimError
                   -> SimState p sym rtp l args
                   -> IO (ExecResult p sym rtp)
           }

------------------------------------------------------------------------
-- SimState lens

-- | View a sim context.
stateContext :: Simple Lens (SimState p s r f a) (SimContext p s)
stateContext = lens _stateContext (\s v -> s { _stateContext = v })
{-# INLINE stateContext #-}

errorHandler :: Simple Lens (SimState p s r f a) (ErrorHandler p s r)
errorHandler = lens _errorHandler (\s v -> s { _errorHandler = v })

-- | Access the active tree associated with a state.
stateTree :: Lens (SimState p sym rtp f a)
                  (SimState p sym rtp g b)
                  (ActiveTree p sym rtp f a)
                  (ActiveTree p sym rtp g b)
stateTree = lens _stateTree (\s v -> s { _stateTree = v })
{-# INLINE stateTree #-}

stateSymInterface :: SimState p sym r f a -> sym
stateSymInterface s = s ^. stateContext . ctxSymInterface

stateSolverProof :: SimState p sym r f args -> (forall a . IsSymInterfaceProof sym a)
stateSolverProof s = ctxSolverProof (s^.stateContext)

stateIntrinsicTypes :: SimState p sym r f args -> IntrinsicTypes sym
stateIntrinsicTypes s = ctxIntrinsicTypes (s^.stateContext)

------------------------------------------------------------------------
-- HasSimState instance

-- | Extract the global state state result from the current state.
stateResult :: SimState p sym rtp f a -> SimContext p sym
stateResult s = s^.stateContext

-- | View a sim context.
stateOverrideFrame :: Lens (SimState p s q (OverrideLang a r) 'Nothing)
                           (SimState p s q (OverrideLang a r) 'Nothing)
                           (OverrideFrame s r a)
                           (OverrideFrame s r a)
stateOverrideFrame = stateTree . actFrame . gpValue . overrideSimFrame

------------------------------------------------------------------------
-- Running error handler

-- | Start running the error handler.
mssRunErrorHandler :: SimState p sym rtp f args
                   -> SimError
                   -> IO (ExecResult p sym rtp)
mssRunErrorHandler s err = runEH (s^.errorHandler) err s

mssRunGenericErrorHandler
     :: SimState p sym rtp f args
     -> String
     -> IO (ExecResult p sym rtp)
mssRunGenericErrorHandler s msg = do
  let sym = stateSymInterface s
  loc <- stateSolverProof s $ getCurrentProgramLoc sym
  let err = SimError loc (GenericSimError msg)
  mssRunErrorHandler s err
