-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.ExecutionTree
-- Description      : Data structure the execution state of the simulator
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Execution trees record the state of the simulator as it explores
-- execution paths through a program.  This module defines the
-- collection of datatypes that record the state of a running simulator
-- and basic lenses and accessors for these types. See
-- "Lang.Crucible.Simulator.Operations" for the definitions of operations
-- that manipulate these datastructures to drive them through the simulator
-- state machine.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fprint-explicit-kinds -Wall #-}
module Lang.Crucible.Simulator.ExecutionTree
  ( -- * GlobalPair
    GlobalPair(..)
  , gpValue
  , gpGlobals

    -- * TopFrame
  , TopFrame
  , crucibleTopFrame
  , overrideTopFrame

    -- * CrucibleBranchTarget
  , CrucibleBranchTarget(..)
  , ppBranchTarget

    -- * AbortedResult
  , AbortedResult(..)
  , SomeFrame(..)
  , filterCrucibleFrames
  , arFrames
  , ppExceptionContext

    -- * Partial result
  , PartialResult(..)
  , partialValue

    -- * Execution states
  , ExecResult(..)
  , ExecState(..)
  , ExecCont
  , RunningStateInfo(..)
  , ResolvedCall(..)
  , resolvedCallHandle
  , execResultContext
  , execStateContext
  , execStateSimState

    -- * Simulator context trees
    -- ** Main context data structures
  , ValueFromValue(..)
  , ValueFromFrame(..)
  , PendingPartialMerges(..)

    -- ** Paused Frames
  , ResolvedJump(..)
  , ControlResumption(..)
  , PausedFrame(..)

    -- ** Sibling paths
  , VFFOtherPath(..)
  , FrameRetType

    -- ** ReturnHandler
  , ReturnHandler(..)

    -- * ActiveTree
  , ActiveTree(..)
  , singletonTree
  , activeFrames
  , actContext
  , actFrame

    -- * Simulator context
    -- ** Function bindings
  , Override(..)
  , FnState(..)
  , FunctionBindings

    -- ** Extensions
  , ExtensionImpl(..)
  , EvalStmtFunc
  , emptyExtensionImpl

    -- ** SimContext record
  , IsSymInterfaceProof
  , SimContext(..)
  , Metric(..)
  , initSimContext
  , ctxSymInterface
  , functionBindings
  , cruciblePersonality
  , profilingMetrics

    -- * SimState
  , SimState(..)
  , SomeSimState(..)
  , initSimState
  , stateLocation

  , AbortHandler(..)
  , CrucibleState

    -- ** Lenses and accessors
  , stateTree
  , abortHandler
  , stateContext
  , stateCrucibleFrame
  , stateSymInterface
  , stateSolverProof
  , stateIntrinsicTypes
  , stateOverrideFrame
  , stateGlobals
  , stateConfiguration
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx
import           Data.Sequence (Seq)
import           Data.Text (Text)
import           System.Exit (ExitCode)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Config (Config)
import           What4.Interface (Pred, getConfiguration)

import           Lang.Crucible.Backend (IsSymInterface, AbortExecReason, FrameIdentifier, Assumption)
import           Lang.Crucible.CFG.Core (BlockID, CFG, CFGPostdom, StmtSeq)
import           Lang.Crucible.CFG.Extension (StmtExtension, ExprExtension)
import           Lang.Crucible.FunctionHandle (FnHandleMap, HandleAllocator, mkHandle')
import           Lang.Crucible.FunctionName (FunctionName, startFunctionName)
import           Lang.Crucible.ProgramLoc (ProgramLoc, plSourceLoc)

import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation (EvalAppFunc)
import           Lang.Crucible.Simulator.GlobalState (SymGlobalState)
import           Lang.Crucible.Simulator.Intrinsics (IntrinsicTypes)
import           Lang.Crucible.Simulator.RegMap (RegMap, emptyRegMap, RegValue, RegEntry)
import           Lang.Crucible.Types

------------------------------------------------------------------------
-- GlobalPair

-- | A value of some type 'v' together with a global state.
data GlobalPair sym (v :: Type) =
   GlobalPair
   { _gpValue :: !v
   , _gpGlobals :: !(SymGlobalState sym)
   }

-- | Access the value stored in the global pair.
gpValue :: Lens (GlobalPair sym u) (GlobalPair sym v) u v
gpValue = lens _gpValue (\s v -> s { _gpValue = v })

-- | Access the globals stored in the global pair.
gpGlobals :: Simple Lens (GlobalPair sym u) (SymGlobalState sym)
gpGlobals = lens _gpGlobals (\s v -> s { _gpGlobals = v })


------------------------------------------------------------------------
-- TopFrame

-- | The currently-exeucting frame plus the global state associated with it.
type TopFrame sym ext f a = GlobalPair sym (SimFrame sym ext f a)

-- | Access the Crucible call frame inside a 'TopFrame'.
crucibleTopFrame ::
  Lens (TopFrame sym ext (CrucibleLang blocks r) ('Just args))
       (TopFrame sym ext (CrucibleLang blocks r) ('Just args'))
       (CallFrame sym ext blocks r args)
       (CallFrame sym ext blocks r args')
crucibleTopFrame = gpValue . crucibleSimFrame
{-# INLINE crucibleTopFrame #-}


overrideTopFrame ::
  Lens (TopFrame sym ext (OverrideLang r) ('Just args))
       (TopFrame sym ext (OverrideLang r') ('Just args'))
       (OverrideFrame sym r args)
       (OverrideFrame sym r' args')
overrideTopFrame = gpValue . overrideSimFrame
{-# INLINE overrideTopFrame #-}

------------------------------------------------------------------------
-- AbortedResult

-- | An execution path that was prematurely aborted.  Note, an abort
--   does not necessarily indicate an error condition.  An execution
--   path might abort because it became infeasible (inconsistent path
--   conditions), because the program called an exit primitive, or
--   because of a true error condition (e.g., a failed assertion).
data AbortedResult sym ext where
  -- | A single aborted execution with the execution state at time of the abort and the reason.
  AbortedExec ::
    !AbortExecReason ->
    !(GlobalPair sym (SimFrame sym ext l args)) ->
    AbortedResult sym ext

  -- | An aborted execution that was ended by a call to 'exit'.
  AbortedExit ::
    !ExitCode ->
    AbortedResult sym ext

  -- | Two separate threads of execution aborted after a symbolic branch,
  --   possibly for different reasons.
  AbortedBranch ::
    !ProgramLoc       {- The source location of the branching control flow -} ->
    !(Pred sym)       {- The symbolic condition -} ->
    !(AbortedResult sym ext) {- The abort that occurred along the 'true' branch -} ->
    !(AbortedResult sym ext) {- The abort that occurred along the 'false' branch -} ->
    AbortedResult sym ext

------------------------------------------------------------------------
-- SomeFrame

-- | This represents an execution frame where its frame type
--   and arguments have been hidden.
data SomeFrame (f :: fk -> argk -> Type) = forall l a . SomeFrame !(f l a)

-- | Return the program locations of all the Crucible frames.
filterCrucibleFrames :: SomeFrame (SimFrame sym ext) -> Maybe ProgramLoc
filterCrucibleFrames (SomeFrame (MF f)) = Just (frameProgramLoc f)
filterCrucibleFrames _ = Nothing

-- | Iterate over frames in the result.
arFrames :: Simple Traversal (AbortedResult sym ext) (SomeFrame (SimFrame sym ext))
arFrames h (AbortedExec e p) =
  (\(SomeFrame f') -> AbortedExec e (p & gpValue .~ f'))
     <$> h (SomeFrame (p^.gpValue))
arFrames _ (AbortedExit ec) = pure (AbortedExit ec)
arFrames h (AbortedBranch predicate loc r s) =
  AbortedBranch predicate loc <$> arFrames h r
                              <*> arFrames h s

-- | Print an exception context
ppExceptionContext :: [SomeFrame (SimFrame sym ext)] -> PP.Doc
ppExceptionContext [] = PP.empty
ppExceptionContext frames = PP.vcat (map pp (init frames))
 where
   pp :: SomeFrame (SimFrame sym ext) -> PP.Doc
   pp (SomeFrame (OF f)) =
      PP.text ("When calling " ++ show (f^.override))
   pp (SomeFrame (MF f)) =
      PP.text "In" PP.<+> PP.text (show (frameHandle f)) PP.<+>
      PP.text "at" PP.<+> PP.pretty (plSourceLoc (frameProgramLoc f))
   pp (SomeFrame (RF nm _v)) =
      PP.text "While returning value from" PP.<+> PP.text (show nm)


------------------------------------------------------------------------
-- PartialResult

-- | A 'PartialResult' represents the result of a computation that
--   might be only partially defined.  If the result is a 'TotalResult',
--   the the result is fully defined; however if it is a
--   'PartialResult', then some of the computation paths that led to
--   this result aborted for some reason, and the resulting value is
--   only defined if the associated condition is true.
data PartialResult sym ext (v :: Type)

     {- | A 'TotalRes' indicates that the the global pair is always defined. -}
   = TotalRes !(GlobalPair sym v)

    {- | 'PartialRes' indicates that the global pair may be undefined
        under some circusmstances.  The predicate specifies under what
        conditions the 'GlobalPair' is defined.
        The 'AbortedResult' describes the circumstances under which
        the result would be partial.
     -}
   | PartialRes !ProgramLoc               -- location of symbolic branch point
                !(Pred sym)               -- if true, global pair is defined
                !(GlobalPair sym v)       -- the value
                !(AbortedResult sym ext)  -- failure cases (when pred. is false)



-- | Access the value stored in the partial result.
partialValue ::
  Lens (PartialResult sym ext u)
       (PartialResult sym ext v)
       (GlobalPair sym u)
       (GlobalPair sym v)
partialValue f (TotalRes x) = TotalRes <$> f x
partialValue f (PartialRes loc p x r) = (\y -> PartialRes loc p y r) <$> f x
{-# INLINE partialValue #-}

-- | The result of resolving a function call.
data ResolvedCall p sym ext ret where
  -- | A resolved function call to an override.
  OverrideCall ::
    !(Override p sym ext args ret) ->
    !(OverrideFrame sym ret args) ->
    ResolvedCall p sym ext ret

  -- | A resolved function call to a Crucible function.
  CrucibleCall ::
    !(BlockID blocks args) ->
    !(CallFrame sym ext blocks ret args) ->
    ResolvedCall p sym ext ret

resolvedCallHandle :: ResolvedCall p sym ext ret -> SomeHandle
resolvedCallHandle (OverrideCall _ frm) = frm ^. overrideHandle
resolvedCallHandle (CrucibleCall _ frm) = frameHandle frm


------------------------------------------------------------------------
-- ExecResult

-- | Executions that have completed either due to (partial or total)
--   successful completion or by some abort condition.
data ExecResult p sym ext (r :: Type)
   = -- | At least one exeuction path resulted in some return result.
     FinishedResult !(SimContext p sym ext) !(PartialResult sym ext r)
     -- | All execution paths resulted in an abort condition, and there is
     --   no result to return.
   | AbortedResult  !(SimContext p sym ext) !(AbortedResult sym ext)
     -- | An execution stopped somewhere in the middle of a run because
     --   a timeout condition occured.
   | TimeoutResult !(ExecState p sym ext r)


execResultContext :: ExecResult p sym ext r -> SimContext p sym ext
execResultContext (FinishedResult ctx _) = ctx
execResultContext (AbortedResult ctx _) = ctx
execResultContext (TimeoutResult exst) = execStateContext exst

execStateContext :: ExecState p sym ext r -> SimContext p sym ext
execStateContext = \case
  ResultState res        -> execResultContext res
  AbortState _ st        -> st^.stateContext
  UnwindCallState _ _ st -> st^.stateContext
  CallState _ _ st       -> st^.stateContext
  TailCallState _ _ st   -> st^.stateContext
  ReturnState _ _ _ st   -> st^.stateContext
  ControlTransferState _ st -> st^.stateContext
  RunningState _ st      -> st^.stateContext
  SymbolicBranchState _ _ _ _ st -> st^.stateContext
  OverrideState _ st -> st^.stateContext
  BranchMergeState _ st -> st^.stateContext
  InitialState stctx _ _ _ _ -> stctx

execStateSimState :: ExecState p sym ext r
                  -> Maybe (SomeSimState p sym ext r)
execStateSimState = \case
  ResultState _                  -> Nothing
  AbortState _ st                -> Just (SomeSimState st)
  UnwindCallState _ _ st         -> Just (SomeSimState st)
  CallState _ _ st               -> Just (SomeSimState st)
  TailCallState _ _ st           -> Just (SomeSimState st)
  ReturnState _ _ _ st           -> Just (SomeSimState st)
  ControlTransferState _ st      -> Just (SomeSimState st)
  RunningState _ st              -> Just (SomeSimState st)
  SymbolicBranchState _ _ _ _ st -> Just (SomeSimState st)
  OverrideState _ st             -> Just (SomeSimState st)
  BranchMergeState _ st          -> Just (SomeSimState st)
  InitialState _ _ _ _ _         -> Nothing

-----------------------------------------------------------------------
-- ExecState

-- | An 'ExecState' represents an intermediate state of executing a
--   Crucible program.  The Crucible simulator executes by transistioning
--   between these different states until it results in a 'ResultState',
--   indicating the program has completed.
data ExecState p sym ext (rtp :: Type)
   {- | The 'ResultState' is used to indicate that the program has completed. -}
   = ResultState
       !(ExecResult p sym ext rtp)

   {- | An abort state indicates that the included 'SimState' encountered
        an abort event while executing its next step.  The state needs to
        be unwound to its nearest enclosing branch point and resumed. -}
   | forall f a.
       AbortState
         !AbortExecReason
           {- Description of what abort condition occurred -}
         !(SimState p sym ext rtp f a)
           {- State of the simulator prior to causing the abort condition -}

   {- | An unwind call state occurs when we are about to leave the context of a
        function call because of an abort.  The included @ValueFromValue@ is the
        context of the call site we are about to unwind into, and the @AbortedResult@
        indicates the reason we are aborting.
    -}
   | forall f a r.
       UnwindCallState
         !(ValueFromValue p sym ext rtp r) {- Caller's context -}
         !(AbortedResult sym ext)          {- Abort causing the stack unwind -}
         !(SimState p sym ext rtp f a)

   {- | A call state is entered when we are about to make a function call to
        the included call frame, which has already resolved the implementation
        and arguments to the function.
    -}
   | forall f a ret.
       CallState
         !(ReturnHandler ret p sym ext rtp f a)
         !(ResolvedCall p sym ext ret)
         !(SimState p sym ext rtp f a)

   {- | A tail-call state is entered when we are about to make a function call to
        the included call frame, and this is the last action we need to take in the
        current caller. Note, we can only enter a tail-call state if there are no
        pending merge points in the caller.  This means that sometimes calls
        that appear to be in tail-call position may nonetheless have to be treated
        as ordinary calls.
    -}
   | forall f a ret.
       TailCallState
         !(ValueFromValue p sym ext rtp ret) {- Calling context to return to -}
         !(ResolvedCall p sym ext ret)       {- Function to call -}
         !(SimState p sym ext rtp f a)

   {- | A return state is entered after the final return value of a function
        is computed, and just before we resolve injecting the return value
        back into the caller's context.
    -}
   | forall f a ret.
       ReturnState
         !FunctionName {- Name of the function we are returning from -}
         !(ValueFromValue p sym ext rtp ret) {- Caller's context -}
         !(RegEntry sym ret) {- Return value -}
         !(SimState p sym ext rtp f a)

   {- | A running state indicates the included 'SimState' is ready to enter
        and execute a Crucible basic block, or to resume a basic block
        from a call site. -}
   | forall blocks r args.
       RunningState
         !(RunningStateInfo blocks args)
         !(SimState p sym ext rtp (CrucibleLang blocks r) ('Just args))

   {- | A symbolic branch state indicates that the execution needs to
        branch on a non-trivial symbolic condition.  The included @Pred@
        is the condition to branch on.  The first @PausedFrame@ is
        the path that corresponds to the @Pred@ being true, and the second
        is the false branch.
    -}
   | forall f args postdom_args.
       SymbolicBranchState
         !(Pred sym) {- predicate to branch on -}
         !(PausedFrame p sym ext rtp f) {- true path-}
         !(PausedFrame p sym ext rtp f)  {- false path -}
         !(CrucibleBranchTarget f postdom_args) {- merge point -}
         !(SimState p sym ext rtp f ('Just args))

   {- | A control transfer state is entered just prior to invoking a
        control resumption.  Control resumptions are responsible
        for transitioning from the end of one basic block to another,
        although there are also some intermediate states related to
        resolving switch statements.
    -}
   | forall f a.
       ControlTransferState
         !(ControlResumption p sym ext rtp f)
         !(SimState p sym ext rtp f ('Just a))

   {- | An override state indicates the included 'SimState' is prepared to
        execute a code override. -}
   | forall args ret.
       OverrideState
         !(Override p sym ext args ret)
           {- The override code to execute -}
         !(SimState p sym ext rtp (OverrideLang ret) ('Just args))
           {- State of the simulator prior to activating the override -}

   {- | A branch merge state occurs when the included 'SimState' is
        in the process of transfering control to the included 'CrucibleBranchTarget'.
        We enter a BranchMergeState every time we need to _check_ if there is a
        pending branch, even if no branch is pending. During this process, paths may
        have to be merged.  If several branches must merge at the same control point,
        this state may be entered several times in succession before returning
        to a 'RunningState'. -}
   | forall f args.
       BranchMergeState
         !(CrucibleBranchTarget f args)
           {- Target of the control-flow transfer -}
         !(SimState p sym ext rtp f args)
           {- State of the simulator before merging pending branches -}

   {- | An initial state indicates the state of a simulator just before execution begins.
        It specifies all the initial data necessary to begin simulating.  The given
        @ExecCont@ will be executed in a fresh @SimState@ representing the default starting
        call frame.
    -}
   | forall ret. rtp ~ RegEntry sym ret =>
       InitialState
         !(SimContext p sym ext)
            {- initial 'SimContext' state -}
         !(SymGlobalState sym)
            {- state of Crucible global variables -}
         !(AbortHandler p sym ext (RegEntry sym ret))
            {- initial abort handler -}
         !(TypeRepr ret)
            {- return type repr -}
         !(ExecCont p sym ext (RegEntry sym ret) (OverrideLang ret) ('Just EmptyCtx))
            {- Entry continuation -}

-- | An action which will construct an 'ExecState' given a current
--   'SimState'. Such continuations correspond to a single transition
--   of the simulator transition system.
type ExecCont p sym ext r f a =
  ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)

-- | Some additional information attached to a @RunningState@
--   that indicates how we got to this running state.
data RunningStateInfo blocks args
    -- | This indicates that we are now in a @RunningState@ because
    --   we transfered execution to the start of a basic block.
  = RunBlockStart !(BlockID blocks args)
    -- | This indicates that we are in a @RunningState@ because we
    --   reached the terminal statement of a basic block.
  | RunBlockEnd !(Some (BlockID blocks))
    -- | This indicates that we are in a @RunningState@ because we
    --   returned from calling the named function.
  | RunReturnFrom !FunctionName
    -- | This indicates that we are now in a @RunningState@ because
    --   we finished branch merging prior to the start of a block.
  | RunPostBranchMerge !(BlockID blocks args)

-- | A 'ResolvedJump' is a block label together with a collection of
--   actual arguments that are expected by that block.  These data
--   are sufficent to actually transfer control to the named label.
data ResolvedJump sym blocks
  = forall args.
      ResolvedJump
        !(BlockID blocks args)
        !(RegMap sym args)

-- | When a path of execution is paused by the symbolic simulator
--   (while it first explores other paths), a 'ControlResumption'
--   indicates what actions must later be taken in order to resume
--   execution of that path.
data ControlResumption p sym ext rtp f where
  {- | When resuming a paused frame with a @ContinueResumption@,
       no special work needs to be done, simply begin executing
       statements of the basic block. -}
  ContinueResumption ::
    !(ResolvedJump sym blocks) ->
    ControlResumption p sym ext rtp (CrucibleLang blocks r)

  {- | When resuming with a @CheckMergeResumption@, we must check
       for the presence of pending merge points before resuming. -}
  CheckMergeResumption ::
    !(ResolvedJump sym blocks) ->
    ControlResumption p sym ext rtp (CrucibleLang blocks r)

  {- | When resuming a paused frame with a @SwitchResumption@, we must
       continue branching to possible alternatives in a variant elmination
       statement.  In other words, we are still in the process of
       transfering control away from the current basic block (which is now
       at a final @VariantElim@ terminal statement). -}
  SwitchResumption ::
    ![(Pred sym, ResolvedJump sym blocks)] {- remaining branches -} ->
    ControlResumption p sym ext rtp (CrucibleLang blocks r)

  {- | When resuming a paused frame with an @OverrideResumption@, we
       simply return control to the included thunk, which represents
       the remaining computation for the override.
   -}
  OverrideResumption ::
    ExecCont p sym ext rtp (OverrideLang r) ('Just args) ->
    !(RegMap sym args) ->
    ControlResumption p sym ext rtp (OverrideLang r)

------------------------------------------------------------------------
-- Paused Frame

-- | A 'PausedFrame' represents a path of execution that has been postponed
--   while other paths are explored.  It consists of a (potentially partial)
--   'SimFrame' togeter with some information about how to resume execution
--   of that frame.
data PausedFrame p sym ext rtp f
   = forall old_args.
       PausedFrame
       { pausedFrame  :: !(PartialResult sym ext (SimFrame sym ext f ('Just old_args)))
       , resume       :: !(ControlResumption p sym ext rtp f)
       , pausedLoc    :: !(Maybe ProgramLoc)
       }

-- | This describes the state of the sibling path at a symbolic branch point.
--   A symbolic branch point starts with the sibling in the 'VFFActivePath'
--   state, which indicates that the sibling path still needs to be executed.
--   After the first path to be explored has reached the merge point, the
--   places of the two paths are exchanged, and the completed path is
--   stored in the 'VFFCompletePath' state until the second path also
--   reaches its merge point.  The two paths will then be merged,
--   and execution will continue beyond the merge point.
data VFFOtherPath p sym ext ret f args

     {- | This corresponds the a path that still needs to be analyzed. -}
   = VFFActivePath
        !(PausedFrame p sym ext ret f)
          {- Other branch we still need to run -}

     {- | This is a completed execution path. -}
   | VFFCompletePath
        !(Seq (Assumption sym))
          {- Assumptions that we collected while analyzing the branch -}
        !(PartialResult sym ext (SimFrame sym ext f args))
          {- Result of running the other branch -}



{- | This type contains information about the current state of the exploration
of the branching structure of a program.  The 'ValueFromFrame' states correspond
to the structure of symbolic branching that occurs within a single function call.

The type parameters have the following meanings:

  * @p@ is the personality of the simulator (i.e., custom user state).

  * @sym@ is the simulator backend being used.

  * @ext@ specifies what extensions to the Crucible language are enabled

  * @ret@ is the global return type of the entire execution.

  * @f@ is the type of the top frame.
-}

data ValueFromFrame p sym ext (ret :: Type) (f :: Type)

  {- | We are working on a branch;  this could be the first or the second
       of both branches (see the 'VFFOtherPath' field). -}
  = forall args.
    VFFBranch

      !(ValueFromFrame p sym ext ret f)
      {- The outer context---what to do once we are done with both branches -}

      !FrameIdentifier
      {- This is the frame identifier in the solver before this branch,
         so that when we are done we can pop-off the assumptions we accumulated
         while processing the branch -}

      !ProgramLoc
      {- Program location of the branch point -}

      !(Pred sym)
      {- Assertion of currently-active branch -}

      !(VFFOtherPath p sym ext ret f args)
      {- Info about the state of the other branch.
         If the other branch is "VFFActivePath", then we still
         need to process it;  if it is "VFFCompletePath", then
         it is finsihed, and so once we are done then we go back to the
         outer context. -}

      !(CrucibleBranchTarget f args)
      {- Identifies the postdominator where the two branches merge back together -}



  {- | We are on a branch where the other branch was aborted before getting
     to the merge point.  -}
  | VFFPartial

      !(ValueFromFrame p sym ext ret f)
      {- The other context--what to do once we are done with this bracnh -}

      !ProgramLoc
      {- Program location of the branch point -}

      !(Pred sym)
      {- Assertion of currently-active branch -}

      !(AbortedResult sym ext)
      {- What happened on the other branch -}

      !PendingPartialMerges
      {- should we abort the (outer) sibling branch when it merges with us? -}


  {- | When we are finished with this branch we should return from the function. -}
  | VFFEnd

      !(ValueFromValue p sym ext ret (FrameRetType f))


-- | Data about whether the surrounding context is expecting a merge to
--   occur or not.  If the context sill expects a merge, we need to
--   take some actions to indicate that the merge will not occur;
--   otherwise there is no special work to be done.
data PendingPartialMerges =
    {- | Don't indicate an abort condition in the context -}
    NoNeedToAbort

    {- | Indicate an abort condition in the context when we
         get there again. -}
  | NeedsToBeAborted


{- | This type contains information about the current state of the exploration
of the branching structure of a program.  The 'ValueFromValue' states correspond
to stack call frames in a more traditional simulator environment.

The type parameters have the following meanings:

  * @p@ is the personality of the simulator (i.e., custom user state).

  * @sym@ is the simulator backend being used.

  * @ext@ specifies what extensions to the Crucible language are enabled

  * @ret@ is the global return type of the entire computation

  * @top_return@ is the return type of the top-most call on the stack.
-}
data ValueFromValue p sym ext (ret :: Type) (top_return :: CrucibleType)

  {- | 'VFVCall' denotes a call site in the outer context, and represents
       the point to which a function higher on the stack will
       eventually return.  The three arguments are:

         * The context in which the call happened.

         * The frame of the caller

         * How to modify the current sim frame and resume execution
           when we obtain the return value
  -}
  = forall args caller.
    VFVCall

    !(ValueFromFrame p sym ext ret caller)
    -- The context in which the call happened.

    !(SimFrame sym ext caller args)
    -- The frame of the caller.

    !(ReturnHandler top_return p sym ext ret caller args)
    -- How to modify the current sim frame and resume execution
    -- when we obtain the return value

  {- | A partial value.
    The predicate indicates what needs to hold to avoid the partiality.
    The "AbortedResult" describes what could go wrong if the predicate
    does not hold. -}
  | VFVPartial
      !(ValueFromValue p sym ext ret top_return)
      !ProgramLoc
      !(Pred sym)
      !(AbortedResult sym ext)

  {- | The top return value, indicating the program termination point. -}
  | (ret ~ RegEntry sym top_return) => VFVEnd



instance PP.Pretty (ValueFromValue p ext sym root rp) where
  pretty = ppValueFromValue

instance PP.Pretty (ValueFromFrame p ext sym ret f) where
  pretty = ppValueFromFrame

instance PP.Pretty (VFFOtherPath ctx sym ext r f a) where
  pretty (VFFActivePath _)   = PP.text "active_path"
  pretty (VFFCompletePath _ _) = PP.text "complete_path"

ppValueFromFrame :: ValueFromFrame p sym ext ret f -> PP.Doc
ppValueFromFrame vff =
  case vff of
    VFFBranch ctx _ _ _ other mp ->
      PP.text "intra_branch" PP.<$$>
      PP.indent 2 (PP.pretty other) PP.<$$>
      PP.indent 2 (PP.text (ppBranchTarget mp)) PP.<$$>
      PP.pretty ctx
    VFFPartial ctx _ _ _ _ ->
      PP.text "intra_partial" PP.<$$>
      PP.pretty ctx
    VFFEnd ctx ->
      PP.pretty ctx

ppValueFromValue :: ValueFromValue p sym ext root tp -> PP.Doc
ppValueFromValue vfv =
  case vfv of
    VFVCall ctx _ _ ->
      PP.text "call" PP.<$$>
      PP.pretty ctx
    VFVPartial ctx _ _ _ ->
      PP.text "inter_partial" PP.<$$>
      PP.pretty ctx
    VFVEnd -> PP.text "root"


-----------------------------------------------------------------------
-- parentFrames

-- | Return parents frames in reverse order.
parentFrames :: ValueFromFrame p sym ext r a -> [SomeFrame (SimFrame sym ext)]
parentFrames c0 =
  case c0 of
    VFFBranch c _ _ _ _ _ -> parentFrames c
    VFFPartial c _ _ _ _ -> parentFrames c
    VFFEnd vfv -> vfvParents vfv

-- | Return parents frames in reverse order.
vfvParents :: ValueFromValue p sym ext r a -> [SomeFrame (SimFrame sym ext)]
vfvParents c0 =
  case c0 of
    VFVCall c f _ -> SomeFrame f : parentFrames c
    VFVPartial c _ _ _ -> vfvParents c
    VFVEnd -> []

------------------------------------------------------------------------
-- ReturnHandler

{- | A 'ReturnHandler' indicates what actions to take to resume
executing in a caller's context once a function call has completed and
the return value is avaliable.

The type parameters have the following meanings:

  * @top_return@ is the type of the return value that is expected.

  * @p@ is the personality of the simulator (i.e., custom user state).

  * @sym@ is the simulator backend being used.

  * @ext@ specifies what extensions to the Crucible language are enabled

  * @roor@ is the global return type of the entire computation

  * @f@ is the stack type of the caller

  * @args@ is the type of the local variables in scope prior to the call
-}
data ReturnHandler (ret :: CrucibleType) p sym ext root f args where
  {- | The 'ReturnToOverride' constructor indicates that the calling
       context is primitive code written directly in Haskell.
   -}
  ReturnToOverride ::
    (RegEntry sym ret -> SimState p sym ext root (OverrideLang r) ('Just args) -> IO (ExecState p sym ext root))
      {- Remaining override code to run when the return value becomse available -} ->
    ReturnHandler ret p sym ext root (OverrideLang r) ('Just args)

  {- | The 'ReturnToCrucible' constructor indicates that the calling context is an
       ordinary function call position from within a Crucible basic block.
       The included 'StmtSeq' is the remaining statements in the basic block to be
       executed following the return.
  -}
  ReturnToCrucible ::
    TypeRepr ret                       {- Type of the return value -} ->
    StmtSeq ext blocks r (ctx ::> ret) {- Remaining statements to execute -} ->
    ReturnHandler ret p sym ext root (CrucibleLang blocks r) ('Just ctx)

  {- | The 'TailReturnToCrucible' constructor indicates that the calling context is a
       tail call position from the end of a Crucible basic block.  Upon receiving
       the return value, that value should be immediately returned in the caller's
       context as well.
  -}
  TailReturnToCrucible ::
    (ret ~ r) =>
    ReturnHandler ret p sym ext root (CrucibleLang blocks r) ctx


------------------------------------------------------------------------
-- ActiveTree

{- | An active execution tree contains at least one active execution.
     The data structure is organized so that the current execution
     can be accessed rapidly. -}
data ActiveTree p sym ext root (f :: Type) args
   = ActiveTree
      { _actContext :: !(ValueFromFrame p sym ext root f)
      , _actResult  :: !(PartialResult sym ext (SimFrame sym ext f args))
      }

-- | Create a tree with a single top frame.
singletonTree ::
  TopFrame sym ext f args ->
  ActiveTree p sym ext (RegEntry sym (FrameRetType f)) f args
singletonTree f = ActiveTree { _actContext = VFFEnd VFVEnd
                             , _actResult = TotalRes f
                             }

-- | Access the calling context of the currently-active frame
actContext ::
  Lens (ActiveTree p sym ext root f args)
       (ActiveTree p sym ext root f args)
       (ValueFromFrame p sym ext root f)
       (ValueFromFrame p sym ext root f)
actContext = lens _actContext (\s v -> s { _actContext = v })

actResult ::
  Lens (ActiveTree p sym ext root f args0)
       (ActiveTree p sym ext root f args1)
       (PartialResult sym ext (SimFrame sym ext f args0))
       (PartialResult sym ext (SimFrame sym ext f args1))
actResult = lens _actResult setter
  where setter s v = ActiveTree { _actContext = _actContext s
                                , _actResult = v
                                }
{-# INLINE actResult #-}

-- | Access the currently-active frame
actFrame ::
  Lens (ActiveTree p sym ext root f args)
       (ActiveTree p sym ext root f args')
       (TopFrame sym ext f args)
       (TopFrame sym ext f args')
actFrame = actResult . partialValue
{-# INLINE actFrame #-}

-- | Return the call stack of all active frames, in
--   reverse activation order (i.e., with callees
--   appearing before callers).
activeFrames :: ActiveTree ctx sym ext root a args ->
                [SomeFrame (SimFrame sym ext)]
activeFrames (ActiveTree ctx ar) =
  SomeFrame (ar^.partialValue^.gpValue) : parentFrames ctx


------------------------------------------------------------------------
-- SimContext

-- | A definition of a function's semantics, given as a Haskell action.
data Override p sym ext (args :: Ctx CrucibleType) ret
   = Override { overrideName    :: FunctionName
              , overrideHandler :: forall r. ExecCont p sym ext r (OverrideLang ret) ('Just args)
              }

-- | State used to indicate what to do when function is called.  A function
--   may either be defined by writing a Haskell 'Override' or by giving
--   a Crucible control-flow graph representation.
data FnState p sym ext (args :: Ctx CrucibleType) (ret :: CrucibleType)
   = UseOverride !(Override p sym ext args ret)
   | forall blocks . UseCFG !(CFG ext blocks args ret) !(CFGPostdom blocks)

-- | A map from function handles to their semantics.
type FunctionBindings p sym ext = FnHandleMap (FnState p sym ext)

-- | The type of functions that interpret extension statements.  These
--   have access to the main simulator state, and can make fairly arbitrary
--   changes to it.
type EvalStmtFunc p sym ext =
  forall rtp blocks r ctx tp'.
    StmtExtension ext (RegEntry sym) tp' ->
    CrucibleState p sym ext rtp blocks r ctx ->
    IO (RegValue sym tp', CrucibleState p sym ext rtp blocks r ctx)

-- | In order to start executing a simulator, one must provide an implementation
--   of the extension syntax.  This includes an evaluator for the added
--   expression forms, and an evaluator for the added statement forms.
data ExtensionImpl p sym ext
  = ExtensionImpl
    { extensionEval ::
        IsSymInterface sym =>
        sym ->
        IntrinsicTypes sym ->
        (Int -> String -> IO ()) ->
        EvalAppFunc sym (ExprExtension ext)

    , extensionExec :: EvalStmtFunc p sym ext
    }

-- | Trivial implementation for the "empty" extension, which adds no
--   additional syntactic forms.
emptyExtensionImpl :: ExtensionImpl p sym ()
emptyExtensionImpl =
  ExtensionImpl
  { extensionEval = \_sym _iTypes _log _f -> \case
  , extensionExec = \case
  }

type IsSymInterfaceProof sym a = (IsSymInterface sym => a) -> a
newtype Metric p sym ext =
  Metric {
    runMetric :: forall rtp f args. SimState p sym ext rtp f args -> IO Integer
  }

-- | Top-level state record for the simulator.  The state contained in this record
--   remains persistent across all symbolic simulator actions.  In particular, it
--   is not rolled back when the simulator returns previous program points to
--   explore additional paths, etc.
data SimContext (personality :: Type) (sym :: Type) (ext :: Type)
   = SimContext { _ctxSymInterface       :: !sym
                  -- | Class dictionary for @'IsSymInterface' sym@
                , ctxSolverProof         :: !(forall a . IsSymInterfaceProof sym a)
                , ctxIntrinsicTypes      :: !(IntrinsicTypes sym)
                  -- | Allocator for function handles
                , simHandleAllocator     :: !(HandleAllocator)
                  -- | Handle to write messages to.
                , printHandle            :: !Handle
                , extensionImpl          :: ExtensionImpl personality sym ext
                , _functionBindings      :: !(FunctionBindings personality sym ext)
                , _cruciblePersonality   :: !personality
                , _profilingMetrics      :: !(Map Text (Metric personality sym ext))
                }

-- | Create a new 'SimContext' with the given bindings.
initSimContext ::
  IsSymInterface sym =>
  sym {- ^ Symbolic backend -} ->
  IntrinsicTypes sym {- ^ Implementations of intrinsic types -} ->
  HandleAllocator {- ^ Handle allocator for creating new function handles -} ->
  Handle {- ^ Handle to write output to -} ->
  FunctionBindings personality sym ext {- ^ Initial bindings for function handles -} ->
  ExtensionImpl personality sym ext {- ^ Semantics for extension syntax -} ->
  personality {- ^ Initial value for custom user state -} ->
  SimContext personality sym ext
initSimContext sym muxFns halloc h bindings extImpl personality =
  SimContext { _ctxSymInterface     = sym
             , ctxSolverProof       = \a -> a
             , ctxIntrinsicTypes    = muxFns
             , simHandleAllocator   = halloc
             , printHandle          = h
             , extensionImpl        = extImpl
             , _functionBindings    = bindings
             , _cruciblePersonality = personality
             , _profilingMetrics    = Map.empty
             }

-- | Access the symbolic backend inside a 'SimContext'.
ctxSymInterface :: Simple Lens (SimContext p sym ext) sym
ctxSymInterface = lens _ctxSymInterface (\s v -> s { _ctxSymInterface = v })

-- | A map from function handles to their semantics.
functionBindings :: Simple Lens (SimContext p sym ext) (FunctionBindings p sym ext)
functionBindings = lens _functionBindings (\s v -> s { _functionBindings = v })

-- | Access the custom user-state inside the 'SimContext'.
cruciblePersonality :: Simple Lens (SimContext p sym ext) p
cruciblePersonality = lens _cruciblePersonality (\s v -> s{ _cruciblePersonality = v })

profilingMetrics :: Simple Lens (SimContext p sym ext)
                                (Map Text (Metric p sym ext))
profilingMetrics = lens _profilingMetrics (\s v -> s { _profilingMetrics = v })

------------------------------------------------------------------------
-- SimState


-- | An abort handler indicates to the simulator what actions to take
--   when an abort occurs.  Usually, one should simply use the
--   'defaultAbortHandler' from "Lang.Crucible.Simulator", which
--   unwinds the tree context to the nearest branch point and
--   correctly resumes simulation.  However, for some use cases, it
--   may be desirable to take additional or alternate actions on abort
--   events; in which case, the libary user may replace the default
--   abort handler with their own.
newtype AbortHandler p sym ext rtp
      = AH { runAH :: forall (l :: Type) args.
                 AbortExecReason ->
                 ExecCont p sym ext rtp l args
           }

-- | A SimState contains the execution context, an error handler, and
--   the current execution tree.  It captures the entire state
--   of the symbolic simulator.
data SimState p sym ext rtp f (args :: Maybe (Ctx.Ctx CrucibleType))
   = SimState { _stateContext      :: !(SimContext p sym ext)
              , _abortHandler      :: !(AbortHandler p sym ext rtp)
              , _stateTree         :: !(ActiveTree p sym ext rtp f args)
              }

data SomeSimState p sym ext rtp =
  forall f args. SomeSimState !(SimState p sym ext rtp f args)

-- | A simulator state that is currently executing Crucible instructions.
type CrucibleState p sym ext rtp blocks ret args
   = SimState p sym ext rtp (CrucibleLang blocks ret) ('Just args)

-- | Create an initial 'SimState'
initSimState ::
  SimContext p sym ext {- ^ initial 'SimContext' state -} ->
  SymGlobalState sym  {- ^ state of Crucible global variables -} ->
  AbortHandler p sym ext (RegEntry sym ret) {- ^ initial abort handler -} ->
  TypeRepr ret ->
  IO (SimState p sym ext (RegEntry sym ret) (OverrideLang ret) ('Just EmptyCtx))
initSimState ctx globals ah ret =
  do let halloc = simHandleAllocator ctx
     h <- mkHandle' halloc startFunctionName Ctx.Empty ret
     let startFrame = OverrideFrame { _override = startFunctionName
                                    , _overrideHandle = SomeHandle h
                                    , _overrideRegMap = emptyRegMap
                                    }
     let startGP = GlobalPair (OF startFrame) globals
     return
       SimState
       { _stateContext = ctx
       , _abortHandler = ah
       , _stateTree    = singletonTree startGP
       }


stateLocation :: Getter (SimState p sym ext r f a) (Maybe ProgramLoc)
stateLocation = to f
 where
 f :: SimState p sym ext r f a -> Maybe ProgramLoc
 f st = case st^.stateTree . actFrame . gpValue of
          MF cf -> Just $! (frameProgramLoc cf)
          OF _ -> Nothing
          RF _ _ -> Nothing


-- | Access the 'SimContext' inside a 'SimState'
stateContext :: Simple Lens (SimState p sym ext r f a) (SimContext p sym ext)
stateContext = lens _stateContext (\s v -> s { _stateContext = v })
{-# INLINE stateContext #-}

-- | Access the current abort handler of a state.
abortHandler :: Simple Lens (SimState p sym ext r f a) (AbortHandler p sym ext r)
abortHandler = lens _abortHandler (\s v -> s { _abortHandler = v })

-- | Access the active tree associated with a state.
stateTree ::
  Lens (SimState p sym ext rtp f a)
       (SimState p sym ext rtp g b)
       (ActiveTree p sym ext rtp f a)
       (ActiveTree p sym ext rtp g b)
stateTree = lens _stateTree (\s v -> s { _stateTree = v })
{-# INLINE stateTree #-}

-- | Access the Crucible call frame inside a 'SimState'
stateCrucibleFrame ::
  Lens (SimState p sym ext rtp (CrucibleLang blocks r) ('Just a))
       (SimState p sym ext rtp (CrucibleLang blocks r) ('Just a'))
       (CallFrame sym ext blocks r a)
       (CallFrame sym ext blocks r a')
stateCrucibleFrame = stateTree . actFrame . crucibleTopFrame
{-# INLINE stateCrucibleFrame #-}

-- | Access the override frame inside a 'SimState'
stateOverrideFrame ::
  Lens
     (SimState p sym ext q (OverrideLang r) ('Just a))
     (SimState p sym ext q (OverrideLang r) ('Just a'))
     (OverrideFrame sym r a)
     (OverrideFrame sym r a')
stateOverrideFrame = stateTree . actFrame . gpValue . overrideSimFrame

-- | Access the globals inside a 'SimState'
stateGlobals :: Simple Lens (SimState p sym ext q f args) (SymGlobalState sym)
stateGlobals = stateTree . actFrame . gpGlobals

-- | Get the symbolic interface out of a 'SimState'
stateSymInterface :: Getter (SimState p sym ext r f a) sym
stateSymInterface = stateContext . ctxSymInterface

-- | Get the intrinsic type map out of a 'SimState'
stateIntrinsicTypes :: Getter (SimState p sym ext r f args) (IntrinsicTypes sym)
stateIntrinsicTypes = stateContext . to ctxIntrinsicTypes

-- | Get the configuration object out of a 'SimState'
stateConfiguration :: Getter (SimState p sym ext r f args) Config
stateConfiguration = to (\s -> stateSolverProof s (getConfiguration (s^.stateSymInterface)))

-- | Provide the 'IsSymInterface' typeclass dictionary from a 'SimState'
stateSolverProof :: SimState p sym ext r f args -> (forall a . IsSymInterfaceProof sym a)
stateSolverProof s = ctxSolverProof (s^.stateContext)
