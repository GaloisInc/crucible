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

    -- * Execution results
  , ExecResult(..)

    -- * Execution intermediate states
  , ExecState(..)
  , ExecCont

    -- * Simulator context trees
    -- ** Main context data structures
  , ValueFromValue(..)
  , ValueFromFrame(..)
  , PendingPartialMerges(..)

    -- ** Paused Frames
  , ResolvedJump(..)
  , ControlResumption(..)
  , PausedFrame(..)
  , pausedFrame
  , resume

    -- ** Sibling paths
  , VFFOtherPath(..)
  , FrameRetType

    -- ** ReturnHandler
  , ReturnHandler(..)
  , returnToOverride
  , returnToCrucible
  , tailReturnToCrucible


    -- * ActiveTree
  , ActiveTree(..)
  , singletonTree
  , activeFrames
  , actContext
  , actFrame
  , actResult

    -- * Simulator context
    -- ** Function bindings
  , Override(..)
  , FnState(..)
  , FunctionBindings

    -- ** Extensions
  , ExtensionImpl(..)
  , EvalStmtFunc

    -- ** SimContext record
  , IsSymInterfaceProof
  , SimContext(..)
  , initSimContext
  , ctxSymInterface
  , functionBindings
  , cruciblePersonality

    -- * SimState
  , AbortHandler(..)
  , SimState(..)
  , CrucibleState
  , initSimState

    -- ** Lenses and accessors
  , stateTree
  , abortHandler
  , stateContext
  , stateCrucibleFrame
  , stateSymInterface
  , stateSolverProof
  , stateIntrinsicTypes
  , stateOverrideFrame
  , stateGetConfiguration
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.ST (RealWorld)
import qualified Data.Parameterized.Context as Ctx
import           Data.Sequence (Seq)
import           System.Exit (ExitCode)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Config
import           What4.Interface
import           What4.FunctionName (FunctionName, startFunctionName)
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle (FnHandleMap, HandleAllocator)
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.Frame
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap


------------------------------------------------------------------------
-- GlobalPair

-- | A value of some type 'v' together with a global state.
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


------------------------------------------------------------------------
-- TopFrame

-- | The currently-exeucting frame plus the global state associated with it.
type TopFrame sym ext f a = GlobalPair sym (SimFrame sym ext f a)

-- | A lens to access the Crucible call frame inside a 'TopFrame'
crucibleTopFrame ::
  Lens (TopFrame sym ext (CrucibleLang blocks r) ('Just args))
       (TopFrame sym ext (CrucibleLang blocks r) ('Just args'))
       (CallFrame sym ext blocks r args)
       (CallFrame sym ext blocks r args')
crucibleTopFrame = gpValue . crucibleSimFrame
{-# INLINE crucibleTopFrame #-}



------------------------------------------------------------------------
-- AbortedResult

-- | An execution path that was prematurely aborted.  Note, an abort
--   does not necessarily inidicate an error condition.  An execution
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
  --   possibly for different reasons
  AbortedBranch ::
    !(Pred sym)              {- The symbolic condition -} ->
    !(AbortedResult sym ext) {- The abort that occurred along the 'true' branch -} ->
    !(AbortedResult sym ext) {- The abort that occurred along the 'false' branch -} ->
    AbortedResult sym ext

------------------------------------------------------------------------
-- SomeFrame

-- | This represents an execution frame where its frame type
--   and arguments have been hidden.
data SomeFrame (f :: fk -> argk -> *) = forall l a . SomeFrame !(f l a)

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
arFrames h (AbortedBranch p r s) =
  AbortedBranch p <$> arFrames h r
                  <*> arFrames h s

-- | Print an exception context
ppExceptionContext :: [SomeFrame (SimFrame sym ext)] -> PP.Doc
ppExceptionContext [] = PP.empty
ppExceptionContext frames = PP.vcat (map pp (init frames))
 where
   pp :: SomeFrame (SimFrame sym ext) -> PP.Doc
   pp (SomeFrame (OF f)) =
      PP.text ("When calling " ++ show (override f))
   pp (SomeFrame (MF f)) =
      PP.text "In" PP.<+> PP.text (show (frameHandle f)) PP.<+>
      PP.text "at" PP.<+> PP.pretty (plSourceLoc (frameProgramLoc f))
   pp (SomeFrame (RF _v)) =
      PP.text ("While returning value")


------------------------------------------------------------------------
-- PartialResult

-- | A 'PartialResult' represents the result of a computation that
--   might be only partially defined.  If the result is a 'TotalResult',
--   the the result is fully defined; however if it is a
--   'PartialResult', then some of the computation paths that led to
--   this result aborted for some reason, and the resulting value is
--   only defined if the associated condition is true.
data PartialResult sym ext (v :: *)

    -- | A 'TotalRes' indicates that the the global pair is always defined.
   = TotalRes !(GlobalPair sym v)

    {- | 'PartialRes' indicates that the global pair may be undefined
        under some circusmstances.  The predicate specifies under what
        conditions the 'GlobalPair' is defined.
        The 'AbortedResult' describes the circumstances under which
        the result would be partial.
     -}
   | PartialRes !(Pred sym)               -- if true, global pair is defined
                !(GlobalPair sym v)       -- the value
                !(AbortedResult sym ext)  -- failure cases (when pred. is false)



-- | View the value stored in the partial result.
partialValue :: Lens (PartialResult sym ext u)
                     (PartialResult sym ext v)
                     (GlobalPair sym u)
                     (GlobalPair sym v)
partialValue f (TotalRes x) = TotalRes <$> f x
partialValue f (PartialRes p x r) = (\y -> PartialRes p y r) <$> f x
{-# INLINE partialValue #-}


------------------------------------------------------------------------
-- ExecResult

-- | Executions that have completed either due to (partial or total)
--   successful completion or by some abort condition.
data ExecResult p sym ext (r :: *)
   = -- | At least one exeuction path resulted in some return result.
     FinishedResult !(SimContext p sym ext) !(PartialResult sym ext r)
     -- | All execution paths resulted in an abort condition, and there is
     --   no result to return.
   | AbortedResult  !(SimContext p sym ext) !(AbortedResult sym ext)

-----------------------------------------------------------------------
-- ExecState

-- | An 'ExecState' represents an intermediate state of executing a
--   Crucible program.  The Crucible simulator executes by transistioning
--   between these different states until it results in a 'ResultState',
--   indicating the program has completed.
data ExecState p sym ext (rtp :: *)
   = -- | The 'ResultState' is used to indicate that the program has completed.
       ResultState
         !(ExecResult p sym ext rtp)

   | -- | An abort state indicates that the included 'SimState' encountered
     --   an abort event while executing its next step.  The state needs to
     --   be unwound to its nearest enclosing branch point and resumed.
     forall f a.
       AbortState
         !AbortExecReason
         !(SimState p sym ext rtp f a)

   | -- | A running state indicates the included 'SimState' is ready to enter
     --   and execute a Crucible basic block, or to resume a basic block
     --   from a call site.
     forall blocks r args.
       RunningState
         !(SimState p sym ext rtp (CrucibleLang blocks r) ('Just args))

   | -- | An override state indicates the included 'SimState' is prepared to
     --   execute a code override.
     forall args ret.
       OverrideState
         !(Override p sym ext args ret)
         !(SimState p sym ext rtp (OverrideLang ret) ('Just args))

   | -- | A control transfer state occurs when the included 'SimState' is
     --   in the process of transfering control to the included 'CrucibleBranchTarget'.
     --   During this process, paths may have to be merged.  If several branches
     --   must merge at the same control point, this state may be entered several
     --   times in succession before returning to a 'RunningState'.
     forall blocks r args.
       ControlTransferState
         !(CrucibleBranchTarget blocks args)
           {- Target of the control-flow transfer -}
         !(SimState p sym ext rtp (CrucibleLang blocks r) args)
           {- State of the simulator prior to the control-flow transfer -}

-- | An action which will construct an 'ExecState' given a current
--   'SimState'. Such continuations correspond to a single transition
--   of the simulator transition system.
type ExecCont p sym ext r f a =
  ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)

data ResolvedJump sym blocks
  = forall args.
      ResolvedJump
        !(Pred sym)
        !(BlockID blocks args)
        !(RegMap sym args)

data ControlResumption p sym ext rtp blocks r args where
  ContinueResumption ::
    ControlResumption p sym ext rtp blocks r args
  CheckMergeResumption ::
    BlockID blocks args ->
    ControlResumption p sym ext root blocks r args
  SwitchResumption ::
    CrucibleBranchTarget blocks args' {- postdominator target -}->
    [ResolvedJump sym blocks]         {- remaining branches -} ->
    ControlResumption p sym ext root blocks r args

------------------------------------------------------------------------
-- Paused Frame

data PausedFrame p sym ext root b r args
   = PausedFrame
     { _pausedFrame  :: !(PartialResult sym ext (SimFrame sym ext (CrucibleLang b r) ('Just args)))
     , _resume       :: !(ControlResumption p sym ext root b r args)
     }

pausedFrame ::
  Simple Lens
    (PausedFrame p sym ext root b r args)
    (PartialResult sym ext (SimFrame sym ext (CrucibleLang b r) ('Just args)))
pausedFrame = lens _pausedFrame (\ppf v -> ppf{ _pausedFrame = v })

resume ::
  Simple Lens
    (PausedFrame p sym ext root b r args)
    (ControlResumption p sym ext root b r args)
resume = lens _resume (\ppf r -> ppf{ _resume = r })


-- | This describes what to do in an inactive path.
data VFFOtherPath p sym ext ret blocks r args

   -- | This corresponds the a path that still needs to be analyzed.
   = forall o_args.
      VFFActivePath
        !(Maybe ProgramLoc)
          {- Location of branch target -}
        !(PausedFrame p sym ext ret blocks r o_args)
          {- Other branch we still need to run -}

     -- | This is a completed execution path.
   | VFFCompletePath
        !(Seq (Assumption sym))
          {- Assumptions that we collected while analyzing the branch -}
        !(PartialResult sym ext (SimFrame sym ext (CrucibleLang blocks r) args))
          {- Result of running the other branch -}


type family FrameRetType (f :: *) :: CrucibleType where
  FrameRetType (CrucibleLang b r) = r
  FrameRetType (OverrideLang r) = r


{- | This type contains information about the current state of the exploration
of the branching structure of a prgram.
The type parameters have the following meanings:

  * @p@ is the personality of the simulator (i.e., custom user state).

  * @sym@ is the simulator backend being used.

  * @ext@ specifies what extensions to the Crusible language are enabled

  * @ret@ is the global return type of the current function.

  * @f@ is the type of the top frame.
-}

data ValueFromFrame p sym ext (ret :: *) (f :: *)

  -- We are working on a branch;  this could be the first or the second
  -- of both branches (see the "VFFOtherPath" field).
  = forall blocks args r. (f ~ CrucibleLang blocks r) =>
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
      {- Assertion of current branch -}

      !(VFFOtherPath p sym ext ret blocks r args)
      {- Info about the state of the other branch.
         If the other branch is "VFFActivePath", then we still
         need to process it;  if it is "VFFCompletePath", then
         it is finsihed, and so once we are done then we go back to the
         outer context. -}

      !(CrucibleBranchTarget blocks args)
      {- Identifies the postdominator where the two branches merge back together -}



  {- We are on a branch where the other branch got aborted before getting
     to the merge point.  -}
  | forall blocks a.  (f ~ CrucibleLang blocks a) =>
    VFFPartial

      !(ValueFromFrame p sym ext ret f)
      {- The other context--what to do once we are done with this bracnh -}

      !(Pred sym)
      {- Assertion of current branch -}

      !(AbortedResult sym ext)
      {- What happened on the other branch -}

      !PendingPartialMerges
      {- should we abort the (outer) sibling branch when it merges with us? -}


  -- When we are finished with this branch we should return from the function
  | VFFEnd

      !(ValueFromValue p sym ext ret (RegEntry sym (FrameRetType f)))


data PendingPartialMerges =
    NoNeedToAbort
  | NeedsToBeAborted


data ValueFromValue p sym ext (ret :: *) (top_return :: *)

  -- VFVCall denotes a return to a given frame.
  = forall args caller new_args.
    VFVCall

    !(ValueFromFrame p sym ext ret caller)
    -- The context in which the call happened.

    !(SimFrame sym ext caller args)
    -- The frame of the caller.

    !(ReturnHandler top_return p sym ext ret caller args new_args)
    -- How to modify the current sim frame and resume execution
    -- when we obtain the return value

  {- | A partial value.
    The predicate indicates what needs to hold to avoid the partiality.
    The "AbortedResult" describes what could go wrong if the predicate
    does not hold. -}
  | VFVPartial
      !(ValueFromValue p sym ext ret top_return)
      !(Pred sym)
      !(AbortedResult sym ext)

  -- | The top return value.
  | (ret ~ top_return) => VFVEnd



instance PP.Pretty (ValueFromValue p ext sym root rp) where
  pretty = ppValueFromValue

instance PP.Pretty (ValueFromFrame p ext sym ret f) where
  pretty = ppValueFromFrame

instance PP.Pretty (VFFOtherPath ctx sym ext r blocks r' a) where
  pretty (VFFActivePath _ _)   = PP.text "active_path"
  pretty (VFFCompletePath _ _) = PP.text "complete_path"

ppValueFromFrame :: ValueFromFrame p sym ext ret f -> PP.Doc
ppValueFromFrame vff =
  case vff of
    VFFBranch ctx _ _ _ other mp ->
      PP.text "intra_branch" PP.<$$>
      PP.indent 2 (PP.pretty other) PP.<$$>
      PP.indent 2 (PP.text (ppBranchTarget mp)) PP.<$$>
      PP.pretty ctx
    VFFPartial ctx _ _ _ ->
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
    VFVPartial ctx _ _ ->
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
    VFFPartial c _ _ _ -> parentFrames c
    VFFEnd vfv -> vfvParents vfv

vfvParents :: ValueFromValue p sym ext r a -> [SomeFrame (SimFrame sym ext)]
vfvParents c0 =
  case c0 of
    VFVCall c f _ -> SomeFrame f : parentFrames c
    VFVPartial c _ _ -> vfvParents c
    VFVEnd -> []

------------------------------------------------------------------------
-- ReturnHandler

data ReturnHandler top_return p sym ext r f args new_args where
  ReturnToOverride ::
    (ret -> ExecCont p sym ext rtp (OverrideLang r) ('Just args))
      {- Remaining override code to run when the return value becomse available -} ->
    ReturnHandler ret p sym ext rtp (OverrideLang r) ('Just args) ('Just args)

  ReturnToCrucible ::
    TypeRepr ret                       {- Type of the return value -} ->
    StmtSeq ext blocks r (ctx ::> ret) {- Remaining statements to execute -} ->
    ReturnHandler (RegEntry sym ret)
      p sym ext root (CrucibleLang blocks r) ('Just ctx) ('Just (ctx ::> ret))

  TailReturnToCrucible ::
    ReturnHandler (RegEntry sym r)
      p sym ext root (CrucibleLang blocks r) ctx 'Nothing


returnToOverride ::
  (ret -> SimState p sym ext rtp (OverrideLang r) ('Just args) -> IO (ExecState p sym ext rtp))
    {- ^ Remaining override code to run when the return value becomse available -} ->
  ReturnHandler ret p sym ext rtp (OverrideLang r) ('Just args) ('Just args)
returnToOverride c = ReturnToOverride (ReaderT . c)

returnToCrucible :: forall p sym ext root ret blocks r ctx.
  TypeRepr ret {- ^ Type of the return value -} ->
  StmtSeq ext blocks r (ctx ::> ret) {- ^ Remaining statements to execute -} ->
  ReturnHandler (RegEntry sym ret)
    p sym ext root (CrucibleLang blocks r) ('Just ctx) ('Just (ctx ::> ret))
returnToCrucible = ReturnToCrucible

tailReturnToCrucible :: forall p sym ext root blocks ctx r.
  ReturnHandler (RegEntry sym r)
    p sym ext root (CrucibleLang blocks r) ctx 'Nothing
tailReturnToCrucible = TailReturnToCrucible

------------------------------------------------------------------------
-- ActiveTree

-- | An active execution tree contains at least one active execution.
-- The data structure is organized so that the current execution
-- can be accessed rapidly.
data ActiveTree p sym ext root (f :: *) args
   = ActiveTree
      { _actContext :: !(ValueFromFrame p sym ext root f)
      , _actResult  :: !(PartialResult sym ext (SimFrame sym ext f args))
      }

-- | Create a tree with a single top frame.
singletonTree :: TopFrame sym ext f args
              -> ActiveTree p
                            sym ext
                            (RegEntry sym (FrameRetType f))
                            f
                            args
singletonTree f = ActiveTree { _actContext = VFFEnd VFVEnd
                             , _actResult = TotalRes f
                             }

actContext :: Lens (ActiveTree p sym ext b a a_args)
                   (ActiveTree p sym ext b a a_args)
                   (ValueFromFrame p sym ext b a)
                   (ValueFromFrame p sym ext b a)
actContext = lens _actContext (\s v -> s { _actContext = v })

actResult :: Lens (ActiveTree p sym ext root b args0)
                  (ActiveTree p sym ext root b args1)
                  (PartialResult sym ext (SimFrame sym ext b args0))
                  (PartialResult sym ext (SimFrame sym ext b args1))
actResult = lens _actResult setter
  where setter s v = ActiveTree { _actContext = _actContext s
                                , _actResult = v
                                }
{-# INLINE actResult #-}

actFrame :: Lens (ActiveTree p sym ext root b args)
                 (ActiveTree p sym ext root b args')
                 (TopFrame sym ext b args)
                 (TopFrame sym ext b args')
actFrame = actResult . partialValue
{-# INLINE actFrame #-}

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

-- | State used to indicate what to do when function is called.
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
    { extensionEval :: IsSymInterface sym => sym -> IntrinsicTypes sym -> (Int -> String -> IO ()) -> EvalAppFunc sym (ExprExtension ext)
    , extensionExec :: EvalStmtFunc p sym ext
    }

type IsSymInterfaceProof sym a = (IsSymInterface sym => a) -> a

-- | Top-level state record for the simulator.  The state contained in this record
--   remains persistent across all symbolic simulator actions.  In particular, it
--   is not rolled back when the simulator returns previous program points to
--   explore additional paths, etc.
data SimContext (personality :: *) (sym :: *) (ext :: *)
   = SimContext { _ctxSymInterface       :: !sym
                  -- | Class dictionary for @'IsSymInterface' sym@
                , ctxSolverProof         :: !(forall a . IsSymInterfaceProof sym a)
                , ctxIntrinsicTypes      :: !(IntrinsicTypes sym)
                  -- | Allocator for function handles
                , simHandleAllocator     :: !(HandleAllocator RealWorld)
                  -- | Handle to write messages to.
                , printHandle            :: !Handle
                , extensionImpl          :: ExtensionImpl personality sym ext
                , _functionBindings      :: !(FunctionBindings personality sym ext)
                , _cruciblePersonality   :: !personality
                }

-- | Create a new 'SimContext' with the given bindings.
initSimContext ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  HandleAllocator RealWorld ->
  Handle {- ^ Handle to write output to -} ->
  FunctionBindings personality sym ext ->
  ExtensionImpl personality sym ext ->
  personality ->
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
             }

ctxSymInterface :: Simple Lens (SimContext p sym ext) sym
ctxSymInterface = lens _ctxSymInterface (\s v -> s { _ctxSymInterface = v })

-- | A map from function handles to their semantics.
functionBindings :: Simple Lens (SimContext p sym ext) (FunctionBindings p sym ext)
functionBindings = lens _functionBindings (\s v -> s { _functionBindings = v })

cruciblePersonality :: Simple Lens (SimContext p sym ext) p
cruciblePersonality = lens _cruciblePersonality (\s v -> s{ _cruciblePersonality = v })


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
      = AH { runAH :: forall (l :: *) args.
                 AbortExecReason ->
                 ExecCont p sym ext rtp l args
           }

-- | A SimState contains the execution context, an error handler, and
--   the current execution tree.
data SimState p sym ext rtp f (args :: Maybe (Ctx.Ctx CrucibleType))
   = SimState { _stateContext      :: !(SimContext p sym ext)
              , _abortHandler      :: !(AbortHandler p sym ext rtp)
              , _stateTree         :: !(ActiveTree p sym ext rtp f args)
              }

-- | A simulator state that is currently executing Crucible instructions.
type CrucibleState p sym ext rtp blocks ret args
   = SimState p sym ext rtp (CrucibleLang blocks ret) ('Just args)


-- | Create an initial 'SimState'.
initSimState :: SimContext p sym ext
             -> SymGlobalState sym
             -- ^ state of global variables
             -> AbortHandler p sym ext (RegEntry sym ret)
             -> SimState p sym ext (RegEntry sym ret) (OverrideLang ret) ('Just EmptyCtx)
initSimState ctx globals ah =
  let startFrame = OverrideFrame { override = startFunctionName
                                 , overrideRegMap = emptyRegMap
                                 }
      startGP = GlobalPair (OF startFrame) globals
   in SimState
      { _stateContext = ctx
      , _abortHandler = ah
      , _stateTree    = singletonTree startGP
      }

-- | View a sim context.
stateContext :: Simple Lens (SimState p sym ext r f a) (SimContext p sym ext)
stateContext = lens _stateContext (\s v -> s { _stateContext = v })
{-# INLINE stateContext #-}

-- | Access the current abort handler of a state.
abortHandler :: Simple Lens (SimState p sym ext r f a) (AbortHandler p sym ext r)
abortHandler = lens _abortHandler (\s v -> s { _abortHandler = v })

-- | Access the active tree associated with a state.
stateTree :: Lens (SimState p sym ext rtp f a)
                  (SimState p sym ext rtp g b)
                  (ActiveTree p sym ext rtp f a)
                  (ActiveTree p sym ext rtp g b)
stateTree = lens _stateTree (\s v -> s { _stateTree = v })
{-# INLINE stateTree #-}

-- | A lens to access the Crucible call frame inside a 'SimState'
stateCrucibleFrame ::
  Lens (SimState p sym ext rtp (CrucibleLang blocks r) ('Just a))
       (SimState p sym ext rtp (CrucibleLang blocks r) ('Just a'))
       (CallFrame sym ext blocks r a)
       (CallFrame sym ext blocks r a')
stateCrucibleFrame = stateTree . actFrame . crucibleTopFrame
{-# INLINE stateCrucibleFrame #-}

stateOverrideFrame :: Lens (SimState p sym ext q (OverrideLang r) ('Just a))
                           (SimState p sym ext q (OverrideLang r) ('Just a))
                           (OverrideFrame sym r a)
                           (OverrideFrame sym r a)
stateOverrideFrame = stateTree . actFrame . gpValue . overrideSimFrame

stateSymInterface :: SimState p sym ext r f a -> sym
stateSymInterface s = s ^. stateContext . ctxSymInterface

stateSolverProof :: SimState p sym ext r f args -> (forall a . IsSymInterfaceProof sym a)
stateSolverProof s = ctxSolverProof (s^.stateContext)

stateIntrinsicTypes :: SimState p sym ext r f args -> IntrinsicTypes sym
stateIntrinsicTypes s = ctxIntrinsicTypes (s^.stateContext)

stateGetConfiguration :: SimState p sym ext r f args -> Config
stateGetConfiguration s = stateSolverProof s (getConfiguration (stateSymInterface s))
