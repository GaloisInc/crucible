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
  , TopFrame
  , crucibleTopFrame
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
  , ExecState(..)
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
  , returnToOverride
  , returnToCrucible
  , tailReturnToCrucible
  , continue
  , continueWith
  , jumpToBlock
  , runOverride

  , isSingleCont
  , pathConditions
    -- * Branch information
  , PausedValue(..)
  , PausedFrame(..)

    -- ** Branch and merge at return
  , intra_branch
  , SomeLabel(..)
    -- * High level operations.
  , replaceTailFrame
  , getIntraFrameBranchTarget
  , performIntraFrameMerge
  , callFn
  , returnValue
  , returnAndMerge
  , abortExec
  , extractCurrentPath
  , branchConditions
    -- * SimState
  , SimState(..)
  , CrucibleState
  , stateTree
  , IsSymInterfaceProof
  , ErrorHandler(..)
  , CrucibleBranchTarget(..)
  , errorHandler
  , stateContext
  , stateCrucibleFrame
    -- * SimContext
  , Override(..)
  , SimContext(..)
  , initSimContext
  , ctxSymInterface
  , functionBindings
  , cruciblePersonality
  , FunctionBindings
  , FnState(..)
  , ExtensionImpl(..)
  , EvalStmtFunc
    -- * Utilities
  , stateSymInterface
  , stateSolverProof
  , stateIntrinsicTypes
  , stateOverrideFrame
  , stateGetConfiguration
  , runErrorHandler
  , runGenericErrorHandler
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.ST (RealWorld)
import           Data.Monoid ((<>))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Type.Equality hiding (sym)
import           System.Exit (ExitCode)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Config
import           What4.Interface
import           What4.FunctionName (FunctionName)
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle (FnHandleMap, HandleAllocator)
import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.Frame
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap




-- | @swap_unless b (x,y)@ returns @(x,y)@ when @b@ is @True@ and
-- @(y,x)@ when @b@ if @False@.
swap_unless :: Bool -> (a, a) -> (a,a)
swap_unless True p = p
swap_unless False (x,y) = (y,x)
{-# INLINE swap_unless #-}

-- | Return assertion where predicate equals a constant
predEqConst :: IsExprBuilder sym => sym -> Pred sym -> Bool -> IO (Pred sym)
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
type TopFrame sym ext f a = GlobalPair sym (SimFrame sym ext f a)

crucibleTopFrame ::
  Lens (TopFrame sym ext (CrucibleLang blocks r) ('Just args))
       (TopFrame sym ext (CrucibleLang blocks r) ('Just args'))
       (CallFrame sym ext blocks r args)
       (CallFrame sym ext blocks r args')
crucibleTopFrame = gpValue . crucibleSimFrame

stateCrucibleFrame ::
  Lens (SimState p sym ext rtp (CrucibleLang blocks r) ('Just a))
       (SimState p sym ext rtp (CrucibleLang blocks r) ('Just a'))
       (CallFrame sym ext blocks r a)
       (CallFrame sym ext blocks r a')
stateCrucibleFrame = stateTree . actFrame . crucibleTopFrame
{-# INLINE stateCrucibleFrame #-}



------------------------------------------------------------------------
-- SomeFrame

-- | This represents an execution frame.
data SomeFrame (f :: fk -> argk -> *) = forall l a . SomeFrame !(f l a)

filterCrucibleFrames :: SomeFrame (SimFrame sym ext)
                     -> Maybe ProgramLoc
filterCrucibleFrames (SomeFrame (MF f)) = Just (frameProgramLoc f)
filterCrucibleFrames _ = Nothing

------------------------------------------------------------------------
-- AbortedResult

-- | An execution that was prematurely aborted.
data AbortedResult sym ext where
  -- A single aborted execution with the execution state at time of error,
  -- and the reason for the error.
  AbortedExec :: !AbortExecReason
              -> !(GlobalPair sym (SimFrame sym ext l args))
              -> AbortedResult sym ext
  -- An aborted execution that was ended by a call to 'exit'
  AbortedExit :: !ExitCode
              -> AbortedResult sym ext

  -- An entire aborted branch.
  AbortedBranch :: !(Pred sym)
                -> !(AbortedResult sym ext)
                -> !(AbortedResult sym ext)
                -> AbortedResult sym ext

-- | Iterate over frames in the result.
arFrames :: Simple Traversal (AbortedResult sym ext) (SomeFrame (SimFrame sym ext))
arFrames h (AbortedExec e p) =
  (\(SomeFrame f') -> AbortedExec e (p & gpValue .~ f'))
     <$> h (SomeFrame (p^.gpValue))
arFrames _ (AbortedExit ec) = pure (AbortedExit ec)
arFrames h (AbortedBranch p r s) =
  AbortedBranch p <$> arFrames h r
                  <*> arFrames h s

-- | Print the exception
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

-- | Abort the current execution.
abortTree ::
  IsSymInterface sym =>
  AbortExecReason ->
  ExecCont p sym ext rtp f args
abortTree e = do
  t   <- view stateTree
  cfg <- asks stateGetConfiguration
  ctx <- view stateContext
  v <- liftIO (getOpt =<< getOptionSetting verbosity cfg)
  when (v > 0) $ do
    let frames = activeFrames t
    let msg = ppAbortExecReason e PP.<$$>
              PP.indent 2 (ppExceptionContext frames)
    -- Print error message.
    liftIO (hPrint (printHandle ctx) msg)
  -- Switch to new frame.
  abortExec e

defaultErrorHandler :: IsSymInterface sym => ErrorHandler p sym ext rtp
defaultErrorHandler = EH abortTree

------------------------------------------------------------------------
-- PartialResult

-- | 'PartialResult' contains a value and global variables along with an
-- optional aborted result.
data PartialResult sym ext (v :: *)

    -- | A 'TotalRes' indicates that the the global pair is always defined.
   = TotalRes !(GlobalPair sym v)

    {- | 'PartialRes' indicates that the global pair may be undefined
        under some circusmstances.  The predicate specifies when the
        'GlobalPair' is guaranteed to be defined.
        The 'AbortedResult' describes the circumstances under which
        the result would be partial. -}
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

mergeAbortedBranch :: Pred sym
                   -> AbortedResult sym ext
                   -> AbortedResult sym ext
                   -> AbortedResult sym ext
mergeAbortedBranch _ (AbortedExit ec) _ = AbortedExit ec
mergeAbortedBranch _ _ (AbortedExit ec) = AbortedExit ec
mergeAbortedBranch c q r = AbortedBranch c q r

mergePartialAndAbortedResult ::
  IsExprBuilder sym =>
  sym ->
  Pred sym {- ^ This needs to hold to avoid the aborted result -} ->
  PartialResult sym ext v ->
  AbortedResult sym ext ->
  IO (PartialResult sym ext v)
mergePartialAndAbortedResult sym c ar r =
  case ar of
    TotalRes gp -> return $! PartialRes c gp r
    PartialRes d gp q ->
      do e <- andPred sym c d
         return $! PartialRes e gp (mergeAbortedBranch c q r)

mergePartialResult ::
  IsSymInterface sym =>
  SimState p sym ext f root args ->
  CrucibleBranchTarget blocks args ->
  MuxFn (Pred sym)
     (PartialResult sym ext (SimFrame sym ext (CrucibleLang blocks ret) args))
mergePartialResult s tgt pp x y =
  let sym       = stateSymInterface s
      iteFns    = stateIntrinsicTypes s
      merge_val = mergeCrucibleFrame sym iteFns tgt
      merge_fn  = mergeGlobalPair merge_val (globalMuxFn sym iteFns)
  in
  case x of
    TotalRes cx ->
      case y of
        TotalRes cy ->
          TotalRes <$> merge_fn pp cx cy

        PartialRes py cy fy ->
          PartialRes <$> orPred sym pp py
                     <*> merge_fn pp cx cy
                     <*> pure fy

    PartialRes px cx fx ->
      case y of
        TotalRes cy ->
          do pc <- notPred sym pp
             PartialRes <$> orPred sym pc px
                        <*> merge_fn pp cx cy
                        <*> pure fx

        PartialRes py cy fy ->
          PartialRes <$> itePred sym pp px py
                     <*> merge_fn pp cx cy
                     <*> pure (AbortedBranch pp fx fy)

------------------------------------------------------------------------
-- ExecResult

-- | Executions that have completed either due to (partial or total) successful execution
--   completion or by an error.
--
--   The included predicate indicates the path condition that resulted in the
--   given result.
data ExecResult p sym ext (r :: *)
   = FinishedResult !(SimContext p sym ext) !(PartialResult sym ext r)
   | AbortedResult  !(SimContext p sym ext) !(AbortedResult sym ext)

data ExecState p sym ext (rtp :: *)
   =   ResultState
         !(ExecResult p sym ext rtp)

   | forall f a.
       AbortState
         !AbortExecReason
         !(SimState p sym ext rtp f a)

   | forall blocks r args.
       RunningState
         !(SimState p sym ext rtp (CrucibleLang blocks r) ('Just args))

   | forall args ret.
       OverrideState
         !(Override p sym ext args ret)
         !(SimState p sym ext rtp (OverrideLang args ret) 'Nothing)

   | forall blocks r args.
       ControlTransferState
         !(ExecCont p sym ext rtp (CrucibleLang blocks r) args)
         !(CrucibleBranchTarget blocks args)
         !(SimState p sym ext rtp (CrucibleLang blocks r) args)

------------------------------------------------------------------------
-- A Paused value and ExecCont

-- | An action which will construct an ExecState given a global state.
--   Such continuations correspond to a single step of execution.
type ExecCont p sym ext r f a =
  ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)

-- | This is essentially a closure denoting a type of continuation that needs a
-- global state to run, but currently has a value that it will use to generate
-- the state, along with a solver state used to configure the state of the
-- solver interface.
data PausedValue p sym ext root f args (v :: *)
   = PausedValue { _pausedValue :: !v
                 , resume :: !(ExecCont p sym ext root f args)
                   -- ^ Function to run.
                 }

pausedValue :: Lens (PausedValue p sym ext root f a u)
                    (PausedValue p sym ext root f a v)
                    u
                    v
pausedValue = lens _pausedValue (\s v -> s { _pausedValue = v })

resumed :: Simple Lens (PausedValue p sym ext root f a u)
                       (ExecCont    p sym ext root f a)
resumed = lens resume (\s v -> s { resume = v })

------------------------------------------------------------------------
-- ReurnHandler and CallerCont

-- | This type names a simulator frame, paired with a continuation
-- to be used when returning from the function.

data ReturnHandler top_return p sym ext r f args new_args where
  ReturnToOverride ::
    (ret -> ExecCont p sym ext rtp (OverrideLang args r) 'Nothing)
      {- ^ Remaining override code to run when the return value becomse available -} ->
    ReturnHandler ret p sym ext rtp (OverrideLang args r) 'Nothing 'Nothing
  
  ReturnToCrucible ::
    TypeRepr ret {- ^ Type of the return value -} ->
    StmtSeq ext blocks r (ctx ::> ret) {- ^ Remaining statements to execute -} ->
    ReturnHandler (RegEntry sym ret)
      p sym ext root (CrucibleLang blocks r) ('Just ctx) ('Just (ctx ::> ret))

  TailReturnToCrucible ::
    ReturnHandler (RegEntry sym r)
      p sym ext root (CrucibleLang blocks r) ctx 'Nothing


returnToOverride ::
  (ret -> ExecCont p sym ext rtp (OverrideLang args r) 'Nothing)
    {- ^ Remaining override code to run when the return value becomse available -} ->
  ReturnHandler ret p sym ext rtp (OverrideLang args r) 'Nothing 'Nothing
returnToOverride = ReturnToOverride

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

runOverride ::
  Override p sym ext args ret ->
  ExecCont p sym ext rtp (OverrideLang args ret) 'Nothing
runOverride o = ReaderT (return . OverrideState o)

continue :: ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just a)
continue = ReaderT (return . RunningState)

continueWith ::
  (SimState p sym ext rtp f a -> SimState p sym ext rtp (CrucibleLang blocks r) ('Just ctx)) ->
  ExecCont p sym ext rtp f a
continueWith f = withReaderT f continue

returnAndMerge :: forall p sym ext rtp blocks r args.
  IsSymInterface sym =>
  RegEntry sym r ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) args
returnAndMerge arg =
  let cont :: ExecCont p sym ext rtp (CrucibleLang b r) 'Nothing
      cont = do RF v <- view (stateTree.actFrame.gpValue)
                returnValue v
  in
  withReaderT
    (stateTree.actFrame.gpValue .~ RF arg)
    (checkForIntraFrameMerge cont ReturnTarget)

jumpToBlock :: (IsSymInterface sym, IsSyntaxExtension ext)
             => BlockID blocks args
             -> RegMap sym args
             -> ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just a)
jumpToBlock block_id args =
  withReaderT
    (stateCrucibleFrame %~ setFrameBlock block_id args)
    (checkForIntraFrameMerge continue (BlockTarget block_id))
{-# INLINE jumpToBlock #-}

------------------------------------------------------------------------
-- Recursive data types

type PausedPartialFrame p sym ext root f args
   = PausedValue p sym ext root f args (PartialResult sym ext (SimFrame sym ext f args))

-- | An active execution tree contains at least one active execution.
-- The data structure is organized so that the current execution
-- can be accessed rapidly.
data ActiveTree p sym ext root (f :: *) args
   = ActiveTree
      { _actContext :: !(ValueFromFrame p sym ext root f)
      , _actResult  :: !(PartialResult sym ext (SimFrame sym ext f args))
      }

-- | This describes what to do in an inactive path.
data VFFOtherPath p sym ext ret blocks r args

   -- | This corresponds the a path that still needs to be analyzed.
   = forall o_args.
      VFFActivePath
        !(Maybe ProgramLoc) {- Location of branch target -}
        !(PausedPartialFrame p sym ext ret (CrucibleLang blocks r) o_args)

     -- | This is a completed execution path.
   | VFFCompletePath
        !(Seq (Assumption sym))
        {- Assumptions that we collected while analyzing the branch -}

        !(PausedPartialFrame p sym ext ret (CrucibleLang blocks r) args)



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
         need to prcess it;  if it is "VFFCompletePath", then
         it is finsihed, and so once we are done then we go back to the
         outer context. -}

      !(CrucibleBranchTarget blocks args)
      {- Identifies where the two branches merge back together -}



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


-- | value from value denotes
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

------------------------------------------------------------------------
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
-- Utilities

pushCrucibleFrame :: forall sym ext b r a
                  .  IsSymInterface sym
                  => sym
                  -> IntrinsicTypes sym
                  -> SimFrame sym ext (CrucibleLang b r) a
                  -> IO (SimFrame sym ext (CrucibleLang b r) a)
pushCrucibleFrame sym muxFns (MF x) = do
  r' <- pushBranchRegs sym muxFns (x^.frameRegs)
  return $! MF (x & frameRegs .~ r')
pushCrucibleFrame sym muxFns (RF x) = do
  x' <- pushBranchRegEntry sym muxFns x
  return $! RF x'


popCrucibleFrame :: IsSymInterface sym
                 => sym
                 -> IntrinsicTypes sym
                 -> SimFrame sym ext (CrucibleLang b r') a'
                 -> IO (SimFrame sym ext (CrucibleLang b r') a')
popCrucibleFrame sym intrinsicFns (MF x') =
  do r' <- abortBranchRegs sym intrinsicFns (x'^.frameRegs)
     return $! MF (x' & frameRegs .~ r')

popCrucibleFrame sym intrinsicFns (RF x') =
  RF <$> abortBranchRegEntry sym intrinsicFns x'


fromJustCallFrame :: SimFrame sym ext (CrucibleLang b r) ('Just a)
                  -> CallFrame sym ext b r a
fromJustCallFrame (MF x) = x

fromNothingCallFrame :: SimFrame sym ext (CrucibleLang b r) 'Nothing
                     -> RegEntry sym r
fromNothingCallFrame (RF x) = x


mergeCrucibleFrame :: IsSymInterface sym
                   => sym
                   -> IntrinsicTypes sym
                   -> CrucibleBranchTarget blocks args -- ^ Target of branch
                   -> MuxFn (Pred sym) (SimFrame sym ext (CrucibleLang blocks ret) args)
mergeCrucibleFrame sym muxFns tgt p x0 y0 =
  case tgt of
    BlockTarget _b_id -> do
      let x = fromJustCallFrame x0
      let y = fromJustCallFrame y0
      z <- mergeRegs sym muxFns p (x^.frameRegs) (y^.frameRegs)
      pure $! MF (x & frameRegs .~ z)
    ReturnTarget -> do
      let x = fromNothingCallFrame x0
      let y = fromNothingCallFrame y0
      RF <$> muxRegEntry sym muxFns p x y

------------------------------------------------------------------------
-- pathConditions

-- | Return list of conditions along current execution path.
pathConditions :: ValueFromFrame p sym ext r a
               -> [Pred sym]
pathConditions c0 =
  case c0 of
    VFFBranch   c _ _ p _ _ -> p : pathConditions c
    VFFPartial  c p _ _   -> p : pathConditions c
    VFFEnd vfv            -> vfvConditions vfv

-- | Get the path conditions from the valueFromValue context
vfvConditions :: ValueFromValue p sym ext r a
              -> [Pred sym]
vfvConditions c0 =
  case c0 of
    VFVCall c _ _ -> pathConditions c
    VFVPartial c p _ -> p : vfvConditions c
    VFVEnd -> []

------------------------------------------------------------------------
-- Resuming frames

-- | Resume a paused frame.
resumeFrame :: PausedPartialFrame p sym ext r f a
            -> ValueFromFrame p sym ext r f
            -> ExecCont p sym ext r g b
resumeFrame pv ctx =
    withReaderT
       (stateTree .~ ActiveTree ctx (pv^.pausedValue))
       (resume pv)
{-# INLINABLE resumeFrame #-}

------------------------------------------------------------------------
-- | Checking for intra-frame merge.

-- | Return branch target if there is one.
getIntraFrameBranchTarget ::
  ValueFromFrame p sym ext root (CrucibleLang b a) ->
  Maybe (Some (CrucibleBranchTarget b))
getIntraFrameBranchTarget vff0 =
  case vff0 of
  VFFBranch _ _ _ _ _ tgt -> Just (Some tgt)
  VFFPartial ctx _ _ _ -> getIntraFrameBranchTarget ctx
  VFFEnd{} -> Nothing

abortPartialResult ::
  IsSymInterface sym =>
  SimState p sym ext r f args ->
  PartialResult sym ext (SimFrame sym ext (CrucibleLang b r') a') ->
  IO (PartialResult sym ext (SimFrame sym ext (CrucibleLang b r') a'))
abortPartialResult s pr =
  let sym                    = stateSymInterface s
      muxFns                 = stateIntrinsicTypes s
      abtGp (GlobalPair v g) = GlobalPair <$> popCrucibleFrame sym muxFns v
                                          <*> globalAbortBranch sym muxFns g
  in partialValue abtGp pr

-- | Branch with a merge point inside this frame.
--
-- If the argument of type @Maybe ('BlockID' b next_args)@ is @Just bid@, and
-- the target of @bid@ is the same as the post-dominator block, then we will
-- check for the opportunity to merge with any pending symbolic branch frames.
-- When all pending merges are complete, run the given computation. If we are
-- not currently about to execute the post-dominator block for a pending merge,
-- then simply run the given computation.
tryIntraFrameMerge
  :: forall p sym ext root b r next_args state_args pd_args
   . IsSymInterface sym
  => ExecCont p sym ext root (CrucibleLang b r) ('Just next_args)
     -- ^ What to run for next computation
  -> CrucibleBranchTarget b pd_args
     -- ^ The location of the post-dominator block.
  -> (SimState p sym ext root (CrucibleLang b r) state_args -> SimState p sym ext root (CrucibleLang b r) ('Just next_args))
    -- ^ Operation to perform on the current tree.
  -> Maybe (BlockID b next_args)
    -- ^ 'Just' the frame corresponds to a label, 'Nothing' otherwise
  -> ExecCont p sym ext root (CrucibleLang b r) state_args
tryIntraFrameMerge active_cont tgt setter m_bid
  | Just bid  <- m_bid
  , Just Refl <- testEquality tgt (BlockTarget bid)
  = withReaderT setter (checkForIntraFrameMerge active_cont tgt)
  | otherwise
  = withReaderT setter active_cont


-- | Checks for the opportunity to merge within a frame.
--
-- This should be called everytime the current control flow location changes.
checkForIntraFrameMerge ::
  ExecCont p sym ext root (CrucibleLang b r) args
  {- ^ What to run for next computation -} ->

  CrucibleBranchTarget b args
  {- ^ The location of the current block.-} ->

  ExecCont p sym ext root (CrucibleLang b r) args
checkForIntraFrameMerge cont tgt =
  ReaderT $ return . ControlTransferState cont tgt


-- | Perform a single instance of path merging at a join point.
--   This will resume an alternate branch, if it is pending,
--   or merge result values if a completed branch has alread reached
--   this point. If there are no pending merge points at this location,
--   continue executing by entering the given continuation.
performIntraFrameMerge ::
  IsSymInterface sym =>
  ExecCont p sym ext root (CrucibleLang b r) args
  {- ^ What to run for next computation -} ->

  CrucibleBranchTarget b args
  {- ^ The location of the current block.-} ->

  ExecCont p sym ext root (CrucibleLang b r) args

performIntraFrameMerge active_cont tgt = do
  s <- ask
  ActiveTree ctx0 er <- view stateTree
  sym <- asks stateSymInterface
  case ctx0 of
    VFFBranch ctx assume_frame loc p other_branch tgt'

      -- Did we get to our merge point (i.e., we are finished with this branch)
      | Just Refl <- testEquality tgt tgt' ->

        case other_branch of

          -- We still have some more work to do.
          VFFActivePath toTgt next ->
            do pathAssumes      <- liftIO $ popAssumptionFrame sym assume_frame
               new_assume_frame <- liftIO $ pushAssumptionFrame sym
               pnot             <- liftIO $ notPred sym p
               liftIO $ addAssumption sym (LabeledPred pnot (ExploringAPath loc toTgt))

               -- The current branch is done
               let other = VFFCompletePath
                              pathAssumes
                              PausedValue { _pausedValue = er
                                          , resume = active_cont
                                          }
               resumeFrame next (VFFBranch ctx new_assume_frame loc pnot other tgt)

          -- We are done with both branches, pop-off back to the outer context.
          VFFCompletePath otherAssumes other ->
            do ar <- liftIO $ mergePartialResult s tgt p er (other^.pausedValue)

               -- Merge the assumptions from each branch and add to the
               -- current assumption frame
               pathAssumes <- liftIO $ popAssumptionFrame sym assume_frame

               mergedAssumes <- liftIO $ mergeAssumptions sym p pathAssumes otherAssumes
               liftIO $ addAssumptions sym mergedAssumes

               -- Check for more potential merge targets.
               withReaderT
                 (stateTree .~ ActiveTree ctx ar)
                 (checkForIntraFrameMerge active_cont tgt)

    -- Since the other branch aborted before it got to the merge point,
    -- we merge-in the partiality on our current path and keep going.
    VFFPartial ctx p ar needsAborting ->
      do er'  <- case needsAborting of
                   NoNeedToAbort    -> return er
                   NeedsToBeAborted -> liftIO $ abortPartialResult s er
         er'' <- liftIO $ mergePartialAndAbortedResult sym p er' ar
         withReaderT
           (stateTree .~ ActiveTree ctx er'')
           (checkForIntraFrameMerge active_cont tgt)

    _ -> active_cont


--------------------------------------------------------------------------------
-- Branching

newtype PausedFrame p sym ext root f args
      = PausedFrame (PausedValue p sym ext root f args (TopFrame sym ext f args))

pushBranchVal :: (f ~ CrucibleLang b a, IsSymInterface sym)
              => SimState p sym ext root f ma
              -> PausedFrame p sym ext root f args
              -> IO (PausedFrame p sym ext root f args)
pushBranchVal s (PausedFrame pv) = do
  let sym = stateSymInterface s
  let iTypes = stateIntrinsicTypes s
  let GlobalPair v gs = pv^.pausedValue
  v' <- pushCrucibleFrame sym iTypes v
  gs' <- globalPushBranch sym iTypes gs
  return $! PausedFrame (pv & pausedValue .~ GlobalPair v' gs')


-- | 'Some' frame, together with its 'BlockID'.
data SomeLabel p sym ext r b a =
  forall args.
  SomeLabel !(PausedFrame p sym ext r (CrucibleLang b a) ('Just args))
            !(Maybe (BlockID b args))

getTgtLoc ::
  SimState p sym ext r (CrucibleLang b a) ('Just dc_args) ->
  BlockID b y ->
  ProgramLoc
getTgtLoc s (BlockID i) = blockLoc (blocks Ctx.! i)
  where
  blocks = frameBlockMap (s ^. stateCrucibleFrame)

-- | Branch with a merge point inside this frame.
intra_branch ::
  IsSymInterface sym =>
  Pred sym
  {- ^ Branch condition branch -} ->

  SomeLabel p sym ext r b a
  {- ^ true branch. -} ->

  SomeLabel p sym ext r b a
  {- ^ false branch. -} ->

  CrucibleBranchTarget b (args :: Maybe (Ctx CrucibleType))
  {- ^ Merge point, where both branches meet again. -} ->

  ExecCont p sym ext r (CrucibleLang b a) ('Just dc_args)

intra_branch p t_label f_label tgt = do
  s <- ask
  ctx <- asContFrame <$> view stateTree
  sym <- asks stateSymInterface
  r <- liftIO $ evalBranch sym p

  case r of
    SymbolicBranch chosen_branch -> do
      -- Get correct predicate
      p' <- liftIO $ predEqConst sym p chosen_branch

      (SomeLabel a_state a_id, SomeLabel o_state o_id) <-
                      return (swap_unless chosen_branch (t_label, f_label))

      loc <- liftIO $ getCurrentProgramLoc sym
      let a_loc  = getTgtLoc s <$> a_id
          o_loc  = getTgtLoc s <$> o_id


      a_frame <- liftIO $ pushBranchVal s a_state
      PausedFrame o_frame <- liftIO $ pushBranchVal s o_state

      assume_frame <- liftIO $ pushAssumptionFrame sym
      liftIO $ addAssumption sym (LabeledPred p' (ExploringAPath loc a_loc))

      -- Create context for paused frame.
      let o_tree = o_frame & pausedValue %~ TotalRes
                           & resumed     .~ (tryIntraFrameMerge
                                                        (resume o_frame)
                                                           tgt
                                                           id
                                                           o_id)

      let todo = VFFActivePath o_loc o_tree
          ctx' = VFFBranch ctx assume_frame loc p' todo tgt

      -- Start a_state (where branch pred is p')
      let PausedFrame pf = a_frame
          setter = stateTree .~ ActiveTree ctx' (TotalRes (pf^.pausedValue))
      tryIntraFrameMerge (resume pf) tgt setter a_id

    NoBranch chosen_branch ->
      do SomeLabel a_state a_id <-
                      return (if chosen_branch then t_label else f_label)
         let PausedFrame pf = a_state
             setter = stateTree .~ ActiveTree ctx (TotalRes (pf^.pausedValue))

         tryIntraFrameMerge (resume pf) tgt setter a_id


{-# INLINABLE intra_branch #-}



{- | Merge the assumptions collected from the branches of a conditional.
The result is a bunch of qualified assumptions: if the branch condition
is @p@, then the true assumptions become @p => a@, while the false ones
beome @not p => a@.
-}
mergeAssumptions ::
  IsExprBuilder sym =>
  sym ->
  Pred sym ->
  Seq (Assumption sym) ->
  Seq (Assumption sym) ->
  IO (Seq (Assumption sym))
mergeAssumptions sym p thens elses =
  do pnot <- notPred sym p
     th' <- (traverse.labeledPred) (impliesPred sym p) thens
     el' <- (traverse.labeledPred) (impliesPred sym pnot) elses
     let xs = th' <> el'
     -- Filter out all the trivally true assumptions
     return (Seq.filter ((/= Just True) . asConstantPred . view labeledPred) xs)

------------------------------------------------------------------------
-- ValueFromFrame

-- | Returns true if tree contains a single non-aborted execution.
isSingleCont :: ValueFromFrame p sym ext root a -> Bool
isSingleCont c0 =
  case c0 of
    VFFBranch{} -> False
    VFFPartial c _ _ _ -> isSingleCont c
    VFFEnd vfv -> isSingleVFV vfv

isSingleVFV :: ValueFromValue p sym ext r a -> Bool
isSingleVFV c0 = do
  case c0 of
    VFVCall c _ _ -> isSingleCont c
    VFVPartial c _ _ -> isSingleVFV c
    VFVEnd -> True

-- | Attempt to unwind a frame context into a value context.
--   This succeeds only if there are no pending symbolic
--   merges.
unwindContext :: ValueFromFrame p sym ext root f
              -> Maybe (ValueFromValue p sym ext root (RegEntry sym (FrameRetType f)))
unwindContext c0 =
    case c0 of
      VFFBranch{} -> Nothing
      VFFPartial _ _ _ NeedsToBeAborted -> Nothing
      VFFPartial d p ar NoNeedToAbort ->
        (\d' -> VFVPartial d' p ar) <$> unwindContext d
      VFFEnd vfv -> return vfv

-- | Get the context for when returning (assumes no
-- intra-procedural merges are possible).
returnContext :: ValueFromFrame ctx sym ext root f
              -> ValueFromValue ctx sym ext root (RegEntry sym (FrameRetType f))
returnContext c0 =
    case unwindContext c0 of
      Just vfv -> vfv
      Nothing ->
        panic "ExecutionTree.returnContext"
          [ "Unexpected attempt to exit function before all intra-procedural merges are complete."
          , "The call stack was:"
          , show (PP.pretty c0)
          ]

-- | Replace the given frame with a new frame.  Succeeds
--   only if there are no pending symbolic merge points.
replaceTailFrame :: forall p sym ext a b c args args'
                  . FrameRetType a ~ FrameRetType c
                 => ActiveTree p sym ext b a args
                 -> SimFrame sym ext c args'
                 -> Maybe (ActiveTree p sym ext b c args')
replaceTailFrame (ActiveTree c er) f = do
    vfv <- unwindContext c
    return $ ActiveTree (VFFEnd vfv) (er & partialValue . gpValue .~ f)

------------------------------------------------------------------------
-- ActiveTree

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

-- | Return the context of the current top frame.
asContFrame :: (f ~ CrucibleLang b a)
            => ActiveTree     p sym ext ret f args
            -> ValueFromFrame p sym ext ret f
asContFrame (ActiveTree ctx active_res) =
  case active_res of
    TotalRes{} -> ctx
    PartialRes p _ex ar -> VFFPartial ctx p ar NoNeedToAbort

activeFrames :: ActiveTree ctx sym ext root a args ->
                [SomeFrame (SimFrame sym ext)]
activeFrames (ActiveTree ctx ar) =
  SomeFrame (ar^.partialValue^.gpValue) : parentFrames ctx


callFn ::
  ReturnHandler (RegEntry sym (FrameRetType a)) p sym ext r f old_args new_args
    {- ^ What to do with the result of the function -} ->

  SimFrame sym ext a args
    {- ^ The code to run -} ->

  ActiveTree p sym ext r f old_args ->
  ActiveTree p sym ext r a args
callFn rh f' (ActiveTree ctx er) =
    ActiveTree (VFFEnd (VFVCall ctx old_frame rh)) er'
  where
  old_frame = er ^. partialValue ^. gpValue
  er'       = er &  partialValue  . gpValue .~ f'


------------------------------------------------------------------------
-- Return a value

-- | Return value from current execution.
--
-- NOTE: All symbolic branching must be resolved before calling `returnValue`.
returnValue :: IsSymInterface sym
            => RegEntry sym (FrameRetType f)
            -> ExecCont p sym ext r f a
returnValue v =
  do ActiveTree ctx er <- view stateTree
     let val = er & partialValue . gpValue .~ v
     handleSimReturn (returnContext ctx) val


handleSimReturn ::
  IsSymInterface sym =>
  ValueFromValue p sym ext r ret {- ^ Context to return to. -} ->
  PartialResult sym ext ret {- ^ Value that is being returned. -} ->
  ExecCont p sym ext r f a
handleSimReturn ctx0 return_value = do
  case ctx0 of
    VFVCall ctx (MF f) (ReturnToCrucible tpr rest) ->
      do let v  = return_value^.partialValue.gpValue
             f' = extendFrame tpr (regValue v) rest f
         continueWith
           (stateTree .~ ActiveTree ctx (return_value & partialValue . gpValue .~ MF f'))

    VFVCall ctx _ TailReturnToCrucible ->
      do let v  = return_value^.partialValue.gpValue
         withReaderT
           (stateTree .~ ActiveTree ctx (return_value & partialValue . gpValue .~ RF v))
           (returnAndMerge v)

    VFVCall ctx (OF f) (ReturnToOverride k) ->
      do let v = return_value^.partialValue.gpValue
         withReaderT
           (stateTree .~ ActiveTree ctx (return_value & partialValue . gpValue .~ OF f))
           (k v)

    VFVPartial ctx p r ->
      do sym <- asks stateSymInterface
         new_ret_val <- liftIO (mergePartialAndAbortedResult sym p return_value r)
         handleSimReturn ctx new_ret_val

    VFVEnd ->
      do res <- view stateContext
         return $! ResultState $ FinishedResult res return_value

------------------------------------------------------------------------
-- Aborting an execution.

-- | Abort the current execution, and either return or switch to next
-- execution path and run it.
abortExec :: IsSymInterface sym
          => AbortExecReason
          -> ExecCont p sym ext (r :: *) f args
abortExec rsn = do
  ActiveTree ctx ar0 <- view stateTree
  -- Get aborted result from active result.
  let ar = case ar0 of
             TotalRes e -> AbortedExec rsn e
             PartialRes c ex ar1 -> AbortedBranch c (AbortedExec rsn ex) ar1
  resumeValueFromFrameAbort ctx ar

-- | Resolve the fact that the current branch aborted.
resumeValueFromFrameAbort ::
  IsSymInterface sym =>
  ValueFromFrame p sym ext r f ->
  AbortedResult sym ext {- ^ The execution that is being aborted. -} ->
  ExecCont p sym ext r g args
resumeValueFromFrameAbort ctx0 ar0 = do
  sym <- asks stateSymInterface
  case ctx0 of

    -- This is the first abort.
    VFFBranch ctx assume_frame loc p other_branch tgt ->
      do pnot <- liftIO $ notPred sym p
         let nextCtx = VFFPartial ctx pnot ar0 NeedsToBeAborted

         -- Reset the backend path state
         _assumes <- liftIO $ popAssumptionFrame sym assume_frame

         case other_branch of

           -- We have some more work to do.
           VFFActivePath toLoc n ->
             do liftIO $ addAssumption sym (LabeledPred pnot (ExploringAPath loc toLoc))
                resumeFrame n nextCtx

           -- The other branch had finished successfully;
           -- Since this one aborted, then the other one is really the only
           -- viable option we have, and so we commit to it.
           VFFCompletePath otherAssumes pv ->
             do let er = pv^.pausedValue

                -- We are committed to the other path,
                -- assume all of its suspended assumptions
                liftIO $ addAssumptions sym otherAssumes

                -- check for further merges, then continue onward.
                withReaderT
                  (stateTree .~ ActiveTree nextCtx er)
                  (checkForIntraFrameMerge (resume pv) tgt)

    -- Both branches aborted
    VFFPartial ctx p ay _ ->
      resumeValueFromFrameAbort ctx (AbortedBranch p ar0 ay)

    VFFEnd ctx ->
      resumeValueFromValueAbort ctx ar0

-- | Run rest of execution given a value from value context and an aborted
-- result.
resumeValueFromValueAbort :: IsSymInterface sym
                          => ValueFromValue p sym ext r ret'
                          -> AbortedResult sym ext
                          -> ExecCont p sym ext r f a
resumeValueFromValueAbort ctx0 ar0 =
  case ctx0 of
    VFVCall ctx _ _ -> do
      -- Pop out of call context.
      resumeValueFromFrameAbort ctx ar0
    VFVPartial ctx p ay -> do
      resumeValueFromValueAbort ctx (AbortedBranch p ar0 ay)
    VFVEnd ->
      do res <- view stateContext
         return $! ResultState $ AbortedResult res ar0

------------------------------------------------------------------------
-- extractCurrentPath

-- | Create a tree that contains just a single path with no branches.
--
-- All branch conditions are converted to assertions.
extractCurrentPath :: ActiveTree p sym ext ret f args
                   -> ActiveTree p sym ext ret f args
extractCurrentPath t =
  ActiveTree (vffSingleContext (t^.actContext))
             (TotalRes (t^.actResult^.partialValue))

vffSingleContext :: ValueFromFrame p sym ext ret f
                 -> ValueFromFrame p sym ext ret f
vffSingleContext ctx0 =
  case ctx0 of
    VFFBranch ctx _ _ _ _ _ -> vffSingleContext ctx
    VFFPartial ctx _ _ _    -> vffSingleContext ctx
    VFFEnd ctx              -> VFFEnd (vfvSingleContext ctx)

vfvSingleContext :: ValueFromValue p sym ext root top_ret
                 -> ValueFromValue p sym ext root top_ret
vfvSingleContext ctx0 =
  case ctx0 of
    VFVCall ctx f h         -> VFVCall (vffSingleContext ctx) f h
    VFVPartial ctx _ _      -> vfvSingleContext ctx
    VFVEnd                  -> VFVEnd

------------------------------------------------------------------------
-- branchConditions

-- | Return all branch conditions along path to this node.
branchConditions :: ActiveTree ctx sym ext ret f args -> [Pred sym]
branchConditions t =
  case t^.actResult of
    TotalRes _ -> vffBranchConditions (t^.actContext)
    PartialRes p _ _ -> p : vffBranchConditions (t^.actContext)

vffBranchConditions :: ValueFromFrame p sym ext ret f
                    -> [Pred sym]
vffBranchConditions ctx0 =
  case ctx0 of
    VFFBranch   ctx _ _ p _ _  -> p : vffBranchConditions ctx
    VFFPartial  ctx p _ _      -> p : vffBranchConditions ctx
    VFFEnd  ctx -> vfvBranchConditions ctx

vfvBranchConditions :: ValueFromValue p sym ext root top_ret
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

type CrucibleState p sym ext rtp blocks ret args
   = SimState p sym ext rtp (CrucibleLang blocks ret) ('Just args)

-- | A map from function handles to their semantics.
type FunctionBindings p sym ext = FnHandleMap (FnState p sym ext)

type EvalStmtFunc p sym ext =
  forall rtp blocks r ctx tp'.
    StmtExtension ext (RegEntry sym) tp' ->
    CrucibleState p sym ext rtp blocks r ctx ->
    IO (RegValue sym tp', CrucibleState p sym ext rtp blocks r ctx)

data ExtensionImpl p sym ext
  = ExtensionImpl
    { extensionEval :: IsSymInterface sym => sym -> IntrinsicTypes sym -> (Int -> String -> IO ()) -> EvalAppFunc sym (ExprExtension ext)
    , extensionExec :: EvalStmtFunc p sym ext
    }

------------------------------------------------------------------------
-- SimContext

-- | Global context for state.
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

-- | A definition of function semantics.
data Override p sym ext (args :: Ctx CrucibleType) ret
   = Override { overrideName :: FunctionName
              , overrideHandler
                  :: forall r. ExecCont p sym ext r (OverrideLang args ret) 'Nothing
              }

-- | State used to indicate what to do when function is called.
data FnState p sym ext (args :: Ctx CrucibleType) (ret :: CrucibleType)
   = UseOverride !(Override p sym ext args ret)
   | forall blocks . UseCFG !(CFG ext blocks args ret) !(CFGPostdom blocks)

------------------------------------------------------------------------
-- SimContext utilities

-- | Create a new 'SimContext' with the given bindings.
initSimContext :: IsSymInterface sym
               => sym
               -> IntrinsicTypes sym
               -> HandleAllocator RealWorld
               -> Handle -- ^ Handle to write output to
               -> FunctionBindings personality sym ext
               -> ExtensionImpl personality sym ext
               -> personality
               -> SimContext personality sym ext
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

type IsSymInterfaceProof sym a = (IsSymInterface sym => a) -> a

-- | A SimState contains the execution context, an error handler, and
-- the current execution tree.
data SimState p sym ext rtp f (args :: Maybe (Ctx.Ctx CrucibleType))
   = SimState { _stateContext      :: !(SimContext p sym ext)
              , _errorHandler      :: !(ErrorHandler p sym ext rtp)
              , _stateTree         :: !(ActiveTree p sym ext rtp f args)
              }

newtype ErrorHandler p sym ext rtp
      = EH { runEH :: forall (l :: *) args
                    . AbortExecReason
                   -> ExecCont p sym ext rtp l args
           }

------------------------------------------------------------------------
-- SimState lens

-- | View a sim context.
stateContext :: Simple Lens (SimState p sym ext r f a) (SimContext p sym ext)
stateContext = lens _stateContext (\s v -> s { _stateContext = v })
{-# INLINE stateContext #-}

errorHandler :: Simple Lens (SimState p sym ext r f a) (ErrorHandler p sym ext r)
errorHandler = lens _errorHandler (\s v -> s { _errorHandler = v })

-- | Access the active tree associated with a state.
stateTree :: Lens (SimState p sym ext rtp f a)
                  (SimState p sym ext rtp g b)
                  (ActiveTree p sym ext rtp f a)
                  (ActiveTree p sym ext rtp g b)
stateTree = lens _stateTree (\s v -> s { _stateTree = v })
{-# INLINE stateTree #-}

stateSymInterface :: SimState p sym ext r f a -> sym
stateSymInterface s = s ^. stateContext . ctxSymInterface

stateSolverProof :: SimState p sym ext r f args -> (forall a . IsSymInterfaceProof sym a)
stateSolverProof s = ctxSolverProof (s^.stateContext)

stateIntrinsicTypes :: SimState p sym ext r f args -> IntrinsicTypes sym
stateIntrinsicTypes s = ctxIntrinsicTypes (s^.stateContext)

stateGetConfiguration :: SimState p sym ext r f args -> Config
stateGetConfiguration s = stateSolverProof s (getConfiguration (stateSymInterface s))

------------------------------------------------------------------------
-- HasSimState instance

-- | View a sim context.
stateOverrideFrame :: Lens (SimState p sym ext q (OverrideLang a r) 'Nothing)
                           (SimState p sym ext q (OverrideLang a r) 'Nothing)
                           (OverrideFrame sym r a)
                           (OverrideFrame sym r a)
stateOverrideFrame = stateTree . actFrame . gpValue . overrideSimFrame

------------------------------------------------------------------------
-- Running error handler

-- | Start running the error handler.
runErrorHandler ::
  AbortExecReason ->
  ExecCont p sym ext rtp f args
runErrorHandler err = ReaderT $ \s -> return (AbortState err s)

runGenericErrorHandler ::
  String ->
  ExecCont p sym ext rtp f args
runGenericErrorHandler msg =
  do ctx <- view stateContext
     let sym = ctx^.ctxSymInterface
     loc <- ctxSolverProof ctx (liftIO (getCurrentProgramLoc sym))
     runErrorHandler (ManualAbort loc msg)
