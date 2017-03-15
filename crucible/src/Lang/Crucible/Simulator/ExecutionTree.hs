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
  ( -- * Frame type definitions.
    Solver
  , Frame
  , SomeFrame(..)
  , BranchTarget
  , ReturnType
  , StateResult
  , GlobalState
  , PathValueFns(..)
  , PushFrameFn(..)
    -- * IsSimState
  , HasSimState(..)
  , IsSimState
  , simTree
    -- * GlobalPair
  , GlobalPair(..)
  , gpValue
  , gpGlobals
  , TopFrame
    -- * AbortedResult
  , AbortedResult(..)
  , arFrames
    -- * ExecResult
  , ExecResult(..)
  , mergeExecResult
  , ExecCont
    -- * ActiveTree
  , ActiveTree(ActiveTree)
  , singletonTree
  , actContext
  , actResult
  , activeFrames
    -- ** Active tree helpers.
  , actFrame
    -- ** PartialResult
  , PartialResult(..)
    -- ** ValueFromFrame
  , ReturnHandler
  , ValueFromFrame
  , isSingleCont
  , parentFrames
  , pathConditions
    -- * Branch information
  , PausedValue(..)
  , PausedFrame(..)
    -- ** Branch and merge at return
  , IntraProcedureMergePoint(..)
  , intra_branch
  , completed_branch
    -- * High level operations.
  , replaceTailFrame
  , getIntraFrameBranchTarget
  , checkForIntraFrameMerge
  , callFn
  , returnValue
  , abortExec
  , MuxFn
  , extractCurrentPath
  , branchConditions
  ) where

import           Control.Lens
import           Data.Parameterized.Some
import           Data.Type.Equality hiding (sym)
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.BoolInterface

-- condition and its negation.
type MuxFn p v = p -> v -> v -> IO v

-- | Information about state persisted between executions.
type SolverState s = SymPathState (Solver s)

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
-- Classes

-- | A solver for a sim state.
-- The parameters for the sim state are:
--   * The type returned at the top frame by the simulator.
--   * The type of the current frame (e.g., Crucible or Override
--   * The arguments in the current frame (used for merging within frames).
type family Solver (s :: * -> fk -> argk -> *) :: *

-- | The actual frame value for an active execution frame.
type family Frame (s :: * -> fk -> argk -> *) :: fk -> argk -> *

-- | Target for branches.
type family BranchTarget (f :: fk) :: argk -> *

-- | Type of return value of a given frame.
type family ReturnType (s :: * -> fk -> argk -> *) (f :: fk) :: *

-- | Information about the state that we wish to return when execution completes.
type family StateResult (s :: * -> fk -> argk -> *) :: *

-- | Type for global state associated with current path.
type family GlobalState (s :: * -> fk -> argk -> *) :: *

------------------------------------------------------------------------
-- GlobalPair

-- | A value with a global state associated.
data GlobalPair (s :: * -> fk -> argk -> *) (v :: *) =
   GlobalPair { _gpValue :: !v
              , _gpGlobals :: !(GlobalState s)
              }

-- | The value stored in the global pair.
gpValue :: Lens (GlobalPair s u) (GlobalPair s v) u v
gpValue = lens _gpValue (\s v -> s { _gpValue = v })

-- | The globals stored in the global pair.
gpGlobals :: Simple Lens (GlobalPair s u) (GlobalState s)
gpGlobals = lens _gpGlobals (\s v -> s { _gpGlobals = v })

-- | Merge two globals together.
mergeGlobalPair :: MuxFn p v
                -> MuxFn p (GlobalState s)
                -> MuxFn p (GlobalPair s v)
mergeGlobalPair merge_fn global_fn c x y =
  GlobalPair <$> merge_fn  c (x^.gpValue) (y^.gpValue)
             <*> global_fn c (x^.gpGlobals) (y^.gpGlobals)

------------------------------------------------------------------------
-- TopFrame

-- | A frame plus the global state associated with it.
type TopFrame s f a = GlobalPair s (Frame s f a)

------------------------------------------------------------------------
-- SomeFrame

-- | This represents an execution frame.
data SomeFrame (f :: fk -> argk -> *) = forall l a . SomeFrame !(f l a)

------------------------------------------------------------------------
-- AbortedResult

-- | An execution that was prematurely aborted.
data AbortedResult (s :: * -> fk -> argk -> *) where
  -- A single aborted execution with the execution state at time of error,
  -- and the reason for the error.
  AbortedExec :: !SimError
              -> !(GlobalPair s (Frame s l args))
              -> AbortedResult s
  -- An entire aborted branch.
  AbortedBranch :: !(Pred (Solver s))
                -> !(AbortedResult s)
                -> !(AbortedResult s)
                -> AbortedResult s

-- | Iterate over frames in the result.
arFrames :: Simple Traversal (AbortedResult s) (SomeFrame (Frame s))
arFrames h (AbortedExec e p) =
  (\(SomeFrame f') -> AbortedExec e (p & gpValue .~ f'))
     <$> h (SomeFrame (p^.gpValue))
arFrames h (AbortedBranch p r s) =
  AbortedBranch p <$> arFrames h r
                  <*> arFrames h s

------------------------------------------------------------------------
-- PartialResult

-- | An active result is either a value or a mux of a value and an
-- aborted result.
data PartialResult (s :: * -> fk -> argk -> *) (v :: *)
   = TotalRes !(GlobalPair s v)
     -- A partial result, the predicate must hold for v to be true.
   | PartialRes !(Pred (Solver s)) !(GlobalPair s v) !(AbortedResult s)

-- | View the value stored in the partial result.
partialValue :: Lens (PartialResult s u)
                     (PartialResult s v)
                     (GlobalPair s u)
                     (GlobalPair s v)
partialValue f (TotalRes x) = TotalRes <$> f x
partialValue f (PartialRes p x r) = (\y -> PartialRes p y r) <$> f x
{-# INLINE partialValue #-}

abortPartialResult
   :: IsSimState s
   => s r f args
   -> (v -> IO v)
   -> PartialResult s v
   -> IO (PartialResult s v)
abortPartialResult s abt pr = do
    let abtGp (GlobalPair v g) = GlobalPair <$> abt v <*> globalAbortBranch s g
    partialValue abtGp pr

mergePartialAndAbortedResult :: IsSimState s
                             => s r f args
                             -> Pred (Solver s)
                             -> PartialResult s v
                             -> AbortedResult s
                             -> IO (PartialResult s v)
mergePartialAndAbortedResult s c ar r = do
  let sym = stateSymInterface s
  case ar of
    TotalRes gp -> return $ PartialRes c gp r
    PartialRes d gp q -> do
      e <- andPred sym c d
      return $ PartialRes e gp (AbortedBranch c q r)

mergePartialResult :: forall s f r args v
                    . ( IsSimState s
                      )
                   => s f r args
                   -> MuxFn (Pred (Solver s)) v
                        -- ^ Function for merging partial results.
                   -> MuxFn (Pred (Solver s)) (PartialResult s v)
mergePartialResult s merge_val pp x y = do
  let sym = stateSymInterface s
  let merge_fn :: MuxFn (Pred (Solver s)) (GlobalPair s v)
      merge_fn = mergeGlobalPair merge_val (globalMuxFn s)
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

-- | Executions that have completed due to an error or execution completion.
data ExecResult (s :: * -> fk -> argk -> *) (r :: *)
   = FinishedExecution !(StateResult s) !(PartialResult s r)
   | AbortedResult !(StateResult s) !(AbortedResult s)

-- | Merge a partial and aborted result.
mergeExecResult :: ( IsSimState s
                   )
                => s r f args
                -> MuxFn (Pred (Solver s)) (StateResult s)
                -> (r -> IO r)
                -> MuxFn (Pred (Solver s)) r
                -> MuxFn (Pred (Solver s)) (ExecResult s r)
mergeExecResult s srMux _ rMux c (FinishedExecution xs xr) (FinishedExecution ys yr) = do
  FinishedExecution <$> srMux c xs ys
                    <*> mergePartialResult s rMux c xr yr
mergeExecResult s srMux rAbt _ c (FinishedExecution xs xr) (AbortedResult ys yr) = do
  xr' <- abortPartialResult s rAbt xr
  FinishedExecution <$> srMux c xs ys
                    <*> mergePartialAndAbortedResult s c xr' yr
mergeExecResult s srMux rAbt _ c (AbortedResult xs xr) (FinishedExecution ys yr) = do
  let sym = stateSymInterface s
  cnot <- notPred sym c
  yr' <- abortPartialResult s rAbt yr
  FinishedExecution <$> srMux c xs ys
                    <*> mergePartialAndAbortedResult s cnot yr' xr
mergeExecResult _ srMux _ _ c (AbortedResult xs xr) (AbortedResult ys yr) = do
  AbortedResult <$> srMux c xs ys
                <*> return (AbortedBranch c xr yr)

------------------------------------------------------------------------
-- A Paused value and ExecCont

-- | An action with will construct an ExecResult given a global state.
type ExecCont s r (f::fk) (a::argk) = s r f a -> IO (ExecResult s r)

-- | This is essentially a closure denoting a type of continuation that needs a
-- global state to run, but currently has a value that it will use to generate
-- the state, along with a solver state used to configure the state of the
-- solver interface.
data PausedValue (s :: * -> fk -> argk -> *) root (f::fk) args v
   = PausedValue { _pausedValue :: !v
                 , savedStateInfo :: !(SolverState s)
                   -- ^ Saved state information
                 , resume :: !(ExecCont s root f args)
                   -- ^ Function to run.
                 }

pausedValue :: Lens (PausedValue s root f a u) (PausedValue s root f a v) u v
pausedValue = lens _pausedValue (\s v -> s { _pausedValue = v })

prependPausedAction :: HasSimState s
                    => (Solver s -> IO ())
                    -> PausedValue s r f a u
                    -> PausedValue s r f a u
prependPausedAction m v = v { resume = \s -> m (stateSymInterface s) >> resume v s }

------------------------------------------------------------------------
-- ReurnHandler and CallerCont

-- | This function is used to get a new frame and the continuation
-- containing what to do next when returning from a function.
type ReturnHandler s r f new_args
   = (Frame s f new_args, ExecCont s r f new_args)

------------------------------------------------------------------------
-- Recursive data types

type PausedPartialFrame (s :: * -> fk -> argk -> *) root f args
   = PausedValue s root f args (PartialResult s (Frame s f args))

-- | An active execution tree contains at least one active execution.
-- The data structure is organized so that the current execution
-- can be accessed rapidly.
data ActiveTree (s :: * -> fk -> argk -> *) ret (f::fk) (args :: argk)
   = ActiveTree { _actContext :: !(ValueFromFrame s ret f)
                , _actResult  :: !(PartialResult s (Frame s f args))
                }

-- | This describes what to do in an inactive path.
data VFFOtherPath (s :: * -> fk -> argk -> *) root f args
   = forall o_args
   . VFFActivePath !(PausedPartialFrame s root f o_args)
     -- ^ This is a active execution and includes the current frame.
     -- Note: this would need to be made more generic
     -- if we want to be able paths concurrently.
   | VFFCompletePath !(PausedPartialFrame s root f args)
     -- ^ This is a completed execution path.


-- | Return saved state info associated with other path.
vffSavedStateInfo :: VFFOtherPath s root f args -> SolverState s
vffSavedStateInfo (VFFActivePath   p) = savedStateInfo p
vffSavedStateInfo (VFFCompletePath p) = savedStateInfo p

-- | @ValueFromFrame s root ret f@ contains the context for a simulator with state @s@,
-- global return type @root@, return type for this stack @ret@, and top frame with type
-- @f@.
  -- A Branch is a branch where both execution paths still contains
  -- executions that need to continue before mergine.
data ValueFromFrame (s :: * -> fk -> argk -> *) (ret :: *) (f :: fk) where
  -- IntraBranch ctx b t denotes @ctx[[] <b> t]@.
  VFFBranch :: !(ValueFromFrame s ret f)
               -- /\ Outer context.
            -> !(SymPathState (Solver s))
               -- /\ State before this branch
            -> !(Pred (Solver s))
               -- /\ Assertion of current branch
            -> !(VFFOtherPath s ret f (args :: argk))
               -- /\ Other computation
            -> !(IntraProcedureMergePoint s f args)
               -- /\ merge handler
            -> ValueFromFrame (s :: * -> fk -> argk -> *) ret f

  -- A branch where the other child has been aborted.
  -- VFFPartial ctx p r denotes @ctx[[] <p> r]@.
  VFFPartial :: !(ValueFromFrame s ret f)
             -> !(Pred (Solver s))
             -> !(AbortedResult s)
             -> !Bool -- should we abort the sibling branch when it merges with us?
             -> ValueFromFrame s ret f

  -- VFFEnd denotes that when the function terminates we should just return
  -- from the function.
  VFFEnd :: !(ValueFromValue s ret (ReturnType s f))
         -> ValueFromFrame s ret f

-- | value from value denotes
data ValueFromValue (s :: * -> fk -> argk -> *) (ret :: *) (top_return :: *) where
  -- VFVCall denotes a return to a given frame.
  VFVCall :: !(ValueFromFrame s ret caller)
             -- Previous context
          -> !(Frame s caller args)
             -- Frame of caller.
          -> !(top_return -> Frame s caller args -> ReturnHandler s ret caller new_args)
             -- Continuation to run.
          -> ValueFromValue s ret top_return

  -- A branch where the other child has been aborted.
  -- VFVPartial ctx p r denotes @ctx[[] <p> r]@.
  VFVPartial :: !(ValueFromValue s ret top_return)
             -> !(Pred (Solver s))
             -> !(AbortedResult s)
             -> ValueFromValue s ret top_return

  -- The top return value.
  VFVEnd :: ValueFromValue s ret ret

instance PP.Pretty (ValueFromValue s ret rp) where
  pretty = ppValueFromValue

instance PP.Pretty (ValueFromFrame s ret f) where
  pretty = ppValueFromFrame

instance PP.Pretty (VFFOtherPath s r f a) where
  pretty (VFFActivePath _)   = PP.text "active_path"
  pretty (VFFCompletePath _) = PP.text "complete_path"

ppValueFromFrame :: ValueFromFrame s ret f -> PP.Doc
ppValueFromFrame vff =
  case vff of
    VFFBranch ctx _ _ other mp ->
      PP.text "intra_branch" PP.<$$>
      PP.indent 2 (PP.pretty other) PP.<$$>
      PP.indent 2 (mergePointName mp) PP.<$$>
      PP.pretty ctx
    VFFPartial ctx _ _ _ ->
      PP.text "intra_partial" PP.<$$>
      PP.pretty ctx
    VFFEnd ctx ->
      PP.pretty ctx

ppValueFromValue :: ValueFromValue s ret tp -> PP.Doc
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
parentFrames :: ValueFromFrame s r a -> [SomeFrame (Frame s)]
parentFrames c0 =
  case c0 of
    VFFBranch c _ _ _ _ -> parentFrames c
    VFFPartial c _ _ _ -> parentFrames c
    VFFEnd vfv -> vfvParents vfv

vfvParents :: ValueFromValue s r a -> [SomeFrame (Frame s)]
vfvParents c0 =
  case c0 of
    VFVCall c f _ -> SomeFrame f : parentFrames c
    VFVPartial c _ _ -> vfvParents c
    VFVEnd -> []

------------------------------------------------------------------------
-- IsSimState

-- | Interface that SimState should export.
class HasSimState (s :: * -> fk -> argk -> *) where
  stateSymInterface :: s rtp f args -> Solver s
  -- | Get tree in state
  getSimTree :: s rtp f a -> ActiveTree s rtp f a
  -- | Set tree in state
  setSimTree :: ActiveTree s rtp g b -> s rtp f a -> s rtp g b
  -- | Extract the global state state result from the current state.
  stateResult :: s rtp f a -> StateResult s

  globalPushBranch  :: s rtp f a -> GlobalState s -> IO (GlobalState s)
  globalMuxFn :: s rtp f a -> MuxFn (Pred (Solver s)) (GlobalState s)
  globalAbortBranch :: s rtp f a -> GlobalState s -> IO (GlobalState s)

  returnMuxFn       :: s rtp f a -> MuxFn (Pred (Solver s)) (ReturnType s f)
  returnAbortBranch :: s rtp f a -> ReturnType s f -> IO (ReturnType s f)


-- | This is called to push a branch to a parameterized value.
data PushFrameFn f = PushFrameFn !(forall a . f a -> IO (f a))


-- | This describes how to merge values or record that the other path
-- was aborted.
data PathValueFns p v = PathValueFns { muxPathValue :: !(MuxFn p v)
                                       -- ^ Merge values along different paths.
                                       --
                                       -- This should throw a user error if mux fials.
                                     , popPathValue :: !(v -> IO v)
                                     }

-- | Interface that SimState should export.
type IsSimState s
   = ( IsBoolExprBuilder (Solver s)
     , IsBoolSolver (Solver s)
     , HasSimState s
     )

-- | Create lens for state tree
-- N.B. This is implemented this way so that lens may be inlined.
simTree :: HasSimState s
        => Lens (s rtp f a)
                (s rtp g b)
                (ActiveTree s rtp f a)
                (ActiveTree s rtp g b)
simTree = lens getSimTree (flip setSimTree)
{-# INLINE simTree #-}

------------------------------------------------------------------------
-- pathConditions

-- | Return list of conditions along current execution path.
pathConditions :: ValueFromFrame s r a
               -> [Pred (Solver s)]
pathConditions c0 =
  case c0 of
    VFFBranch   c _ p _ _ -> p : pathConditions c
    VFFPartial  c p _ _   -> p : pathConditions c
    VFFEnd vfv            -> vfvConditions vfv

-- | Get the path conditions from the valueFromValue context
vfvConditions :: ValueFromValue s r a
              -> [Pred (Solver s)]
vfvConditions c0 =
  case c0 of
    VFVCall c _ _ -> pathConditions c
    VFVPartial c p _ -> p : vfvConditions c
    VFVEnd -> []

------------------------------------------------------------------------
-- Resuming frames

-- | Resume a paused frame.
resumeFrame :: IsSimState s
            => s r g b
            -> PausedPartialFrame s r f a
            -> ValueFromFrame s r f
            -> IO (ExecResult s r)
resumeFrame s pv ctx = resume pv $ s & simTree .~ ActiveTree ctx er
  where er = pv^.pausedValue
{-# INLINABLE resumeFrame #-}

------------------------------------------------------------------------
-- IntraProcedureMergePoint

-- | Information for a merge within a frame.
--
-- The type parameter s is not used, but it helps enforce kind restrictions in other
-- functions such as 'getIntraFrameBranchTarget'.
data IntraProcedureMergePoint (s :: * -> fk -> argk -> *) (f :: fk) (args :: argk)
   = IntraProcedureMergePoint {
         mergePointName :: !PP.Doc
         -- ^ Name of merge point for debugging purposes.
       , branchTarget :: !(BranchTarget f (args :: argk))
         -- ^ Branch target
       , mergeFunctions :: !(PathValueFns (Pred (Solver s)) (Frame s f args))
         -- ^ Functions for merging frame.
       , withFrameEquality :: !(forall a . ((TestEquality (BranchTarget f :: argk -> *)) => a) -> a)
       }

------------------------------------------------------------------------
-- | Checking for intra-frame merge.

-- | Return branch target if there is one.
getIntraFrameBranchTarget :: ValueFromFrame s r f
                          -> Maybe (Some (IntraProcedureMergePoint s f))
getIntraFrameBranchTarget vff0 =
  case vff0 of
  VFFBranch _ _ _ _ tgt -> Just (Some tgt)
  VFFPartial ctx _ _ _ -> getIntraFrameBranchTarget ctx
  VFFEnd{} -> Nothing

-- | Checks for the opportunity to merge within a frame.
--
-- This should be called everytime the current control flow location changes.
-- It will return the computation to run after merging.
checkForIntraFrameMerge
  :: forall s r f args
   . IsSimState s
  => ExecCont s r f args
     -- ^ What to run for next computation
  -> IntraProcedureMergePoint s (f :: fk) (args :: ak)
     -- ^ The location of the current block.
  -> s r f args
    -- ^ Current tree.
  -> IO (ExecResult s r)
checkForIntraFrameMerge active_cont mp s = do
  let tgt = branchTarget mp
  let fns = mergeFunctions mp
  let t0@(ActiveTree ctx0 er) = s^.simTree
  let sym = stateSymInterface s
  withFrameEquality mp $ do
  case ctx0 of
    VFFBranch ctx old_state p some_next mh
      | Just Refl <- testEquality (branchTarget mh) tgt -> do
        -- Adjust state info.
        -- Merge the two results together.
        sym_state <- getCurrentState sym
        case some_next of
          VFFActivePath next -> do
            pnot <- notPred sym p
            switchCurrentState sym old_state (savedStateInfo next)
            let paused_res :: PausedPartialFrame s r f args
                paused_res = PausedValue { _pausedValue = er
                                         , savedStateInfo = sym_state
                                         , resume = active_cont
                                         }
            resumeFrame s next (VFFBranch ctx old_state pnot (VFFCompletePath paused_res) mh)
          VFFCompletePath next -> do
            resetCurrentState sym old_state
            mergeState sym p sym_state (savedStateInfo next)
            -- Merge results together
            ar <- mergePartialResult s (muxPathValue fns) p er (next^.pausedValue)
            -- Check for more potential merge targets.
            let s' = s & simTree .~ ActiveTree ctx ar
            checkForIntraFrameMerge active_cont mp s'
    VFFPartial ctx p ar shouldAbort -> do

      er'  <- if shouldAbort then
                abortPartialResult s (popPathValue fns) er
              else
                return er
      er'' <- mergePartialAndAbortedResult s p er' ar
      let s' = s & simTree .~ ActiveTree ctx er''
      checkForIntraFrameMerge active_cont mp s'
    _ -> active_cont (s & simTree .~ t0)

--------------------------------------------------------------------------------
-- Branching

newtype PausedFrame s root f args
      = PausedFrame (PausedValue s root f args (TopFrame s f args))

runWithCurrentState :: IsSimState s
                    => s r f a
                    -> ValueFromFrame s r f
                    -> Some (PausedFrame s r f)
                    -> IO (ExecResult s r)
runWithCurrentState s ctx (Some (PausedFrame pf)) = do
  resume pf $ s & simTree .~ ActiveTree ctx (TotalRes (pf^.pausedValue))
{-# INLINABLE runWithCurrentState #-}

pushBranchVal :: IsSimState s
                 => s root f a
                 -> PushFrameFn (Frame s f)
                 -> PausedFrame s root f args
                 -> IO (PausedFrame s root f args)
pushBranchVal s (PushFrameFn f) (PausedFrame pv) = do
  let GlobalPair v g = pv^.pausedValue
  v' <- f v
  g' <- globalPushBranch s g
  return $! PausedFrame (pv & pausedValue .~ GlobalPair v' g')


-- | Branch with a merge point inside this frame.
--
-- The false branch is known to be at the merge point.
-- This may merge frames, and will throw a user error if merging fails.
completed_branch :: IsSimState s
                 => s r f (dc_args :: ak)
                    -- ^ Current state
                 -> PushFrameFn (Frame s f)
                    -- ^ Push function
                 -> Pred (Solver s)
                    -- ^ Predicate on current branch
                 -> (SolverState s -> Some (PausedFrame s r f))
                    -- ^ Returns exec for true branch.
                 -> (SolverState s -> PausedFrame s r f args)
                    -- ^ Returns exec for false branch.
                 -> IntraProcedureMergePoint s f (args :: ak)
                    -- ^ information for merge
                 -> IO (ExecResult s r)
completed_branch s push_fn p t_fn f_fn tgt = do
  let ctx = asContFrame (s^.simTree)
  let sym = stateSymInterface s
  r <- evalBranch sym p
  -- Get current state
  cur_state <- getCurrentState sym
  case r of
    -- If we are symbolic, then we ignore chosen_branch because we must run t_fn
    -- next
    SymbolicBranch _ -> do
      -- Pause result.
      active_frame <- traverseSome (pushBranchVal s push_fn) $ t_fn cur_state
      PausedFrame paused_frame <- pushBranchVal s push_fn $ f_fn cur_state

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
      let s' = s & simTree .~ ActiveTree ctx (TotalRes (pf^.pausedValue))
      checkForIntraFrameMerge (resume pf) tgt s'

    InfeasibleBranch -> fail "Detected infeasible path during branch."
{-# INLINABLE completed_branch #-}

-- | Branch with a merge point inside this frame.
intra_branch :: (IsSimState s)
             => s r f (dc_args::ak)
                -- ^ Current execution state
             -> PushFrameFn (Frame s f)
                -- ^ Push function
             -> Pred (Solver s)
                -- ^ Inforamtion about branch
             -> (SolverState s -> Some (PausedFrame s r f))
                -- ^ true branch.
             -> (SolverState s -> Some (PausedFrame s r f))
                -- ^ false branch.
             -> IntraProcedureMergePoint s f (args::ak)
                -- ^ Information for merge
             -> IO (ExecResult s r)
intra_branch s push_fn p t_fn f_fn tgt = do
  let ctx = asContFrame (s^.simTree)
  let sym = stateSymInterface s
  r <- evalBranch sym p
  cur_state <- getCurrentState sym
  case r of
    SymbolicBranch chosen_branch -> do
      -- Get correct predicate
      p' <- predEqConst sym p chosen_branch
      -- Get current state
      t_frame <- traverseSome (pushBranchVal s push_fn) $ t_fn cur_state
      f_frame <- traverseSome (pushBranchVal s push_fn) $ f_fn cur_state

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
      fail "Detected infeasible path during branch."
{-# INLINABLE intra_branch #-}

------------------------------------------------------------------------
-- ValueFromFrame

-- | Returns true if tree contains a single non-aborted execution.
isSingleCont :: ValueFromFrame s r a -> Bool
isSingleCont c0 =
  case c0 of
    VFFBranch{} -> False
    VFFPartial c _ _ _ -> isSingleCont c
    VFFEnd vfv -> isSingleVFV vfv

isSingleVFV :: ValueFromValue s r a -> Bool
isSingleVFV c0 = do
  case c0 of
    VFVCall c _ _ -> isSingleCont c
    VFVPartial c _ _ -> isSingleVFV c
    VFVEnd -> True

-- | Attempt to unwind a frame context into a value context.
--   This succeeds only if there are no pending symbolic
--   merges.
unwindContext :: ValueFromFrame s ret f
              -> Maybe (ValueFromValue s ret (ReturnType s f))
unwindContext c0 =
    case c0 of
      VFFBranch{} -> Nothing
      VFFPartial _ _ _ True -> Nothing
      VFFPartial d p ar False ->
        (\d' -> VFVPartial d' p ar) <$> unwindContext d
      VFFEnd vfv -> return vfv

-- | Get the context for when returning (assumes no
-- intra-procedural merges are possible).
returnContext :: ValueFromFrame s ret f
              -> ValueFromValue s ret (ReturnType s f)
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
replaceTailFrame :: forall s a b c args args'
                  . ReturnType s a ~ ReturnType s c
                 => ActiveTree s b a args
                 -> Frame s c args'
                 -> Maybe (ActiveTree s b c args')
replaceTailFrame (ActiveTree c er) f = do
    vfv <- unwindContext c
    return $ ActiveTree (VFFEnd vfv) (er & partialValue . gpValue .~ f)

------------------------------------------------------------------------
-- ActiveTree

-- | Create a tree with a single top frame.
singletonTree :: TopFrame s f args
              -> ActiveTree s (ReturnType s f) f args
singletonTree f = ActiveTree { _actContext = VFFEnd VFVEnd
                             , _actResult = TotalRes f
                             }

actContext :: Lens (ActiveTree s b a a_args)
                   (ActiveTree s c a a_args)
                   (ValueFromFrame s b a)
                   (ValueFromFrame s c a)
actContext = lens _actContext (\s v -> s { _actContext = v })

actResult :: Lens (ActiveTree s a b args0)
                  (ActiveTree s a b args1)
                  (PartialResult s (Frame s b args0))
                  (PartialResult s (Frame s b args1))
actResult = lens _actResult setter
  where setter s v = ActiveTree { _actContext = _actContext s
                                , _actResult = v
                                }
{-# INLINE actResult #-}

actFrame :: Lens (ActiveTree s a b args)
                 (ActiveTree s a b args')
                 (TopFrame s b args)
                 (TopFrame s b args')
actFrame = actResult . partialValue
{-# INLINE actFrame #-}

-- | Return the context of the current top frame.
asContFrame :: ActiveTree     s ret a args
            -> ValueFromFrame s ret a
asContFrame (ActiveTree ctx active_res) =
  case active_res of
    TotalRes{} -> ctx
    PartialRes p _ex ar -> VFFPartial ctx p ar False

activeFrames :: ActiveTree s b a args -> [SomeFrame (Frame s)]
activeFrames (ActiveTree ctx ar) =
  SomeFrame (ar^.partialValue^.gpValue) : parentFrames ctx

callFn :: (ReturnType s a
           -> Frame s f old_args
           -> ReturnHandler s r f new_args)
       -> Frame s a args
       -> ActiveTree s r f old_args
       -> ActiveTree s r a args
callFn h f' (ActiveTree ctx er) =
    ActiveTree (VFFEnd (VFVCall ctx old_frame h)) $ er'
  where old_frame   = er^.partialValue^.gpValue
        er' = er & partialValue . gpValue .~ f'

------------------------------------------------------------------------
-- Return a value

-- | Return value from current execution.
--
-- NOTE: All symbolic branching must be resolved before calling `returnValue`.
returnValue :: IsSimState s
            => (s :: * -> fk -> argk -> *) (r :: *) (f::fk) (a :: argk)
            -> ReturnType s f
            -> IO (ExecResult s r)
returnValue s v = do
  let ActiveTree ctx er = s^.simTree
  handleSimReturn s (returnContext ctx) $ er & partialValue . gpValue .~ v

handleSimReturn :: IsSimState s
                => (s :: * -> fk -> argk -> *) (r :: *) (f :: fk) (a :: argk)
                -> ValueFromValue s r ret
                   -- ^ Context to return to.
                -> PartialResult s ret
                   -- ^ Value that is being returned.
                -> IO (ExecResult s r)
handleSimReturn s ctx0 return_value = do
  case ctx0 of
    VFVCall ctx g h -> do
      let vt = return_value^.partialValue
      let (f, c) = h (vt^.gpValue) g
      let s' = s & simTree .~ ActiveTree ctx (return_value & partialValue . gpValue .~ f)
      c s'
    VFVPartial ctx p r -> do
      updated_return_value <- mergePartialAndAbortedResult s p return_value r
      handleSimReturn s ctx updated_return_value
    VFVEnd -> return $! FinishedExecution (stateResult s) return_value

------------------------------------------------------------------------
-- Aborting an execution.

-- | Abort the current execution, and either return or switch to next
-- execution path and run it.
abortExec :: IsSimState (s :: * -> fk -> argk -> *)
          => SimError -> s (r :: *) f args
          -> IO (ExecResult s r)
abortExec rsn s = do
  let ActiveTree ctx ar0 = s^.simTree
  -- Get aborted result from active result.
  let ar = case ar0 of
             TotalRes e -> AbortedExec rsn e
             PartialRes c ex ar1 -> AbortedBranch c (AbortedExec rsn ex) ar1
  resumeValueFromFrameAbort s ctx ar

-- | Resolve the fact that the top execution is now aborted.
--
-- This may merge frames, and will throw a user error if merging fails.
resumeValueFromFrameAbort :: IsSimState s
                          => s r (g :: fk) (a :: ak)
                          -> ValueFromFrame s r (f :: fk)
                          -> AbortedResult s
                             -- ^ The execution that is being aborted.
                          -> IO (ExecResult s r)
resumeValueFromFrameAbort s ctx0 ar0 = do
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
          let s' = s & simTree .~ ActiveTree nextCtx er
          checkForIntraFrameMerge (resume pv) tgt s'
    VFFPartial ctx p ay _ -> do
      resumeValueFromFrameAbort s ctx (AbortedBranch p ar0 ay)
    VFFEnd ctx -> do
      resumeValueFromValueAbort s ctx ar0

-- | Run rest of execution given a value from value context and an aborted
-- result.
resumeValueFromValueAbort :: IsSimState s
                          => (s :: * -> fk -> ak -> *) (r :: *) (g :: fk) (a :: ak)
                          -> ValueFromValue s r ret
                          -> AbortedResult s
                          -> IO (ExecResult s r)
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
extractCurrentPath :: ActiveTree s ret f args
                   -> ActiveTree s ret f args
extractCurrentPath t =
  ActiveTree (vffSingleContext (t^.actContext))
             (TotalRes (t^.actResult^.partialValue))

vffSingleContext :: ValueFromFrame s ret f
                 -> ValueFromFrame s ret f
vffSingleContext ctx0 =
  case ctx0 of
    VFFBranch ctx _ _ _ _   -> vffSingleContext ctx
    VFFPartial ctx _ _ _    -> vffSingleContext ctx
    VFFEnd ctx              -> VFFEnd (vfvSingleContext ctx)

vfvSingleContext :: ValueFromValue s ret top_ret
                 -> ValueFromValue s ret top_ret
vfvSingleContext ctx0 =
  case ctx0 of
    VFVCall ctx f h         -> VFVCall (vffSingleContext ctx) f h
    VFVPartial ctx _ _      -> vfvSingleContext ctx
    VFVEnd                  -> VFVEnd

------------------------------------------------------------------------
-- muxActiveTree

branchConditions :: ActiveTree s ret f args -> [Pred (Solver s)]
branchConditions t =
  case t^.actResult of
    TotalRes _ -> vffBranchConditions (t^.actContext)
    PartialRes p _ _ -> p : vffBranchConditions (t^.actContext)

vffBranchConditions :: ValueFromFrame s ret f
                    -> [Pred (Solver s)]
vffBranchConditions ctx0 =
  case ctx0 of
    VFFBranch   ctx _ p _ _  -> p : vffBranchConditions ctx
    VFFPartial  ctx p _ _    -> p : vffBranchConditions ctx
    VFFEnd  ctx -> vfvBranchConditions ctx

vfvBranchConditions :: ValueFromValue s ret top_ret
                    -> [Pred (Solver s)]
vfvBranchConditions ctx0 =
  case ctx0 of
    VFVCall     ctx _ _      -> vffBranchConditions ctx
    VFVPartial  ctx p _      -> p : vfvBranchConditions ctx
    VFVEnd                   -> []


{-
------------------------------------------------------------------------
-- SimState

-- | An MSS_State contains the execution context, an error handler, and
-- the current execution tree.
--
-- Do not use due to a GHC bug in 7.10.2.
data SimState ctx sym rtp f (args :: k)
   = SimState { _stateContext :: !(ctx sym)
               , returnMergeFn :: !(sym -> MuxFn (Pred sym) rtp)
                 -- ^ Describes how to merge the ultimate return value.
               , _errorHandler :: !(ErrorHandler ctx sym rtp)
               , _stateTree :: !(ActiveTree (SimState ctx sym) rtp rtp f args)
               }

newtype ErrorHandler (ctx :: * -> *) (sym :: *) (rtp :: *)
      = EH { runEH :: forall (l :: *) (args :: k)
                   . SimError
                   -> SimState ctx sym rtp l args
                   -> IO (ExecResult (SimState ctx sym) rtp)
           }
-}
