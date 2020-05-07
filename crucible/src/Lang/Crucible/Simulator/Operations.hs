-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Operations
-- Description      : Basic operations on execution trees
-- Copyright        : (c) Galois, Inc 2014-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Operations corresponding to basic control-flow events on
-- simulator execution trees.
------------------------------------------------------------------------

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fprint-explicit-kinds -Wall #-}
module Lang.Crucible.Simulator.Operations
  ( -- * Control-flow operations
    continue
  , jumpToBlock
  , conditionalBranch
  , variantCases
  , returnValue
  , callFunction
  , tailCallFunction
  , runOverride
  , runAbortHandler
  , runErrorHandler
  , runGenericErrorHandler
  , performIntraFrameMerge
  , performIntraFrameSplit
  , performFunctionCall
  , performTailCall
  , performReturn
  , performControlTransfer
  , resumeFrame
  , resumeValueFromValueAbort
  , overrideSymbolicBranch

    -- * Resolving calls
  , ResolvedCall(..)
  , UnresolvableFunction(..)
  , resolveCall
  , resolvedCallName

    -- * Abort handlers
  , abortExecAndLog
  , abortExec
  , defaultAbortHandler

    -- * Call tree manipulations
  , pushCallFrame
  , replaceTailFrame
  , isSingleCont
  , unwindContext
  , extractCurrentPath
  , asContFrame
  , forgetPostdomFrame
  ) where

import Prelude hiding (pred)

import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad.Reader
import           Data.Maybe (fromMaybe)
import           Data.List (isPrefixOf)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import           Data.Type.Equality hiding (sym)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Config
import           What4.Interface

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Intrinsics
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

---------------------------------------------------------------------
-- Intermediate state branching/merging

-- | Merge two globals together.
mergeGlobalPair ::
  MuxFn p v ->
  MuxFn p (SymGlobalState sym) ->
  MuxFn p (GlobalPair sym v)
mergeGlobalPair merge_fn global_fn c x y =
  GlobalPair <$> merge_fn  c (x^.gpValue) (y^.gpValue)
             <*> global_fn c (x^.gpGlobals) (y^.gpGlobals)

mergeAbortedResult ::
  ProgramLoc {- ^ Program location of control-flow branching -} ->
  Pred sym {- ^ Branch predicate -} ->
  AbortedResult sym ext ->
  AbortedResult sym ext ->
  AbortedResult sym ext
mergeAbortedResult _ _ (AbortedExit ec) _ = AbortedExit ec
mergeAbortedResult _ _ _ (AbortedExit ec) = AbortedExit ec
mergeAbortedResult loc pred q r = AbortedBranch loc pred q r

mergePartialAndAbortedResult ::
  IsExprBuilder sym =>
  sym ->
  ProgramLoc {- ^ Program location of control-flow branching -} ->
  Pred sym {- ^ This needs to hold to avoid the aborted result -} ->
  PartialResult sym ext v ->
  AbortedResult sym ext ->
  IO (PartialResult sym ext v)
mergePartialAndAbortedResult sym loc pred ar r = do
  case ar of
    TotalRes gp -> return $! PartialRes loc pred gp r
    PartialRes loc' d gp q ->
      do e <- andPred sym pred d
         return $! PartialRes loc' e gp (mergeAbortedResult loc pred q r)


mergeCrucibleFrame ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  CrucibleBranchTarget f args {- ^ Target of branch -} ->
  MuxFn (Pred sym) (SimFrame sym ext f args)
mergeCrucibleFrame sym muxFns tgt p x0 y0 =
  case tgt of
    BlockTarget _b_id -> do
      let x = fromCallFrame x0
      let y = fromCallFrame y0
      z <- mergeRegs sym muxFns p (x^.frameRegs) (y^.frameRegs)
      pure $! MF (x & frameRegs .~ z)
    ReturnTarget -> do
      let x = fromReturnFrame x0
      let y = fromReturnFrame y0
      RF (x0^.frameFunctionName) <$> muxRegEntry sym muxFns p x y


mergePartialResult ::
  IsSymInterface sym =>
  SimState p sym ext root f args ->
  CrucibleBranchTarget f args ->
  MuxFn (Pred sym)
     (PartialResult sym ext (SimFrame sym ext f args))
mergePartialResult s tgt pred x y =
  let sym       = s^.stateSymInterface
      iteFns    = s^.stateIntrinsicTypes
      merge_val = mergeCrucibleFrame sym iteFns tgt
      merge_fn  = mergeGlobalPair merge_val (globalMuxFn sym iteFns)
  in
  case x of
    TotalRes cx ->
      case y of
        TotalRes cy ->
          TotalRes <$> merge_fn pred cx cy

        PartialRes loc py cy fy ->
          PartialRes loc <$> orPred sym pred py
                         <*> merge_fn pred cx cy
                         <*> pure fy

    PartialRes loc px cx fx ->
      case y of
        TotalRes cy ->
          do pc <- notPred sym pred
             PartialRes loc <$> orPred sym pc px
                            <*> merge_fn pred cx cy
                            <*> pure fx

        PartialRes loc' py cy fy ->
          PartialRes loc' <$> itePred sym pred px py
                          <*> merge_fn pred cx cy
                          <*> pure (AbortedBranch loc' pred fx fy)

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

forgetPostdomFrame ::
  PausedFrame p sym ext rtp g ->
  PausedFrame p sym ext rtp g
forgetPostdomFrame (PausedFrame frm cont loc) = PausedFrame frm (f cont) loc
  where
  f (CheckMergeResumption jmp) = ContinueResumption jmp
  f x = x


pushPausedFrame ::
  IsSymInterface sym =>
  PausedFrame p sym ext rtp g ->
  ReaderT (SimState p sym ext rtp f ma) IO (PausedFrame p sym ext rtp g)
pushPausedFrame (PausedFrame frm res loc) =
  do sym <- view stateSymInterface
     iTypes <- view stateIntrinsicTypes
     frm' <- lift (frm & traverseOf (partialValue.gpGlobals) (globalPushBranch sym iTypes))
     res' <- lift (pushControlResumption sym iTypes res)
     return (PausedFrame frm' res' loc)

pushControlResumption ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  ControlResumption p sym ext rtp g ->
  IO (ControlResumption p sym ext rtp g)
pushControlResumption sym iTypes res =
  case res of
    ContinueResumption jmp ->
      ContinueResumption <$> pushResolvedJump sym iTypes jmp
    CheckMergeResumption jmp ->
      CheckMergeResumption <$> pushResolvedJump sym iTypes jmp
    SwitchResumption ps ->
      SwitchResumption <$> (traverse._2) (pushResolvedJump sym iTypes) ps
    OverrideResumption k args ->
      OverrideResumption k <$> pushBranchRegs sym iTypes args

pushResolvedJump ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  ResolvedJump sym branches ->
  IO (ResolvedJump sym branches)
pushResolvedJump sym iTypes (ResolvedJump block_id args) =
  ResolvedJump block_id <$> pushBranchRegs sym iTypes args


abortCrucibleFrame ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  CrucibleBranchTarget f a' ->
  SimFrame sym ext f a' ->
  IO (SimFrame sym ext f a')
abortCrucibleFrame sym intrinsicFns (BlockTarget _) (MF x') =
  do r' <- abortBranchRegs sym intrinsicFns (x'^.frameRegs)
     return $! MF (x' & frameRegs .~ r')

abortCrucibleFrame sym intrinsicFns ReturnTarget (RF nm x') =
  RF nm <$> abortBranchRegEntry sym intrinsicFns x'


abortPartialResult ::
  IsSymInterface sym =>
  SimState p sym ext r f args ->
  CrucibleBranchTarget f a' ->
  PartialResult sym ext (SimFrame sym ext f a') ->
  IO (PartialResult sym ext (SimFrame sym ext f a'))
abortPartialResult s tgt pr =
  let sym                    = s^.stateSymInterface
      muxFns                 = s^.stateIntrinsicTypes
      abtGp (GlobalPair v g) = GlobalPair <$> abortCrucibleFrame sym muxFns tgt v
                                          <*> globalAbortBranch sym muxFns g
  in partialValue abtGp pr


------------------------------------------------------------------------
-- resolveCall

-- | This exception is thrown if a 'FnHandle' cannot be resolved to
--   a callable function.  This usually indicates a programming error,
--   but might also be used to allow on-demand function loading.
--
--   The 'ProgramLoc' argument references the call site for the unresolved
--   function call.
--
--   The @['SomeFrame']@ argument is the active call stack at the time of
--   the exception.
data UnresolvableFunction where
  UnresolvableFunction ::
    !(ProgramLoc) ->
    [SomeFrame (SimFrame sym ext)] ->
    !(FnHandle args ret) ->
    UnresolvableFunction

instance Ex.Exception UnresolvableFunction
instance Show UnresolvableFunction where
  show (UnresolvableFunction loc callStack h) =
    let name = show $ handleName h
    in unlines $
         if "llvm" `isPrefixOf` name
         then [ "Encountered unresolved LLVM intrinsic '" ++ name ++ "'"
              , "Please report this on the following issue:"
              , "https://github.com/GaloisInc/crucible/issues/73"
              ] ++ [ show (ppExceptionContext callStack) ]
         else [ "Could not resolve function: " ++ name
              , "Called at: " ++ show (PP.pretty (plSourceLoc loc))
              ] ++ [ show (ppExceptionContext callStack) ]


-- | Utility function that packs the tail of a collection of arguments
--   into a vector of ANY type values for passing to varargs functions.
packVarargs ::
  CtxRepr addlArgs ->
  RegMap sym (args <+> addlArgs) ->
  RegMap sym (args ::> VectorType AnyType)

packVarargs = go mempty
 where
 go ::
  V.Vector (AnyValue sym) ->
  CtxRepr addlArgs ->
  RegMap sym (args <+> addlArgs) ->
  RegMap sym (args ::> VectorType AnyType)

 go v (addl Ctx.:> tp) (unconsReg -> (args, x)) =
   go (V.cons (AnyValue tp (regValue x)) v) addl args

 go v Ctx.Empty args =
   assignReg knownRepr v args

-- | Given a set of function bindings, a function-
--   value (which is possibly a closure) and a
--   collection of arguments, resolve the identity
--   of the function to call, and set it up to be called.
--
--   Will throw an 'UnresolvableFunction' exception if
--   the underlying function handle is not found in the
--   'FunctionBindings' map.
resolveCall ::
  FunctionBindings p sym ext {- ^ Map from function handles to semantics -} ->
  FnVal sym args ret {- ^ Function handle and any closure variables -} ->
  RegMap sym args {- ^ Arguments to the function -} ->
  ProgramLoc {- ^ Location of the call -} ->
  [SomeFrame (SimFrame sym ext)] {-^ current call stack (for exceptions) -} ->
  ResolvedCall p sym ext ret
resolveCall bindings c0 args loc callStack =
  case c0 of
    ClosureFnVal c tp v -> do
      resolveCall bindings c (assignReg tp v args) loc callStack

    VarargsFnVal h addlTypes ->
      resolveCall bindings (HandleFnVal h) (packVarargs addlTypes args) loc callStack

    HandleFnVal h -> do
      case lookupHandleMap h bindings of
        Nothing -> Ex.throw (UnresolvableFunction loc callStack h)
        Just (UseOverride o) -> do
          let f = OverrideFrame { _override = overrideName o
                                , _overrideHandle = SomeHandle h
                                , _overrideRegMap = args
                                }
           in OverrideCall o f
        Just (UseCFG g pdInfo) -> do
          CrucibleCall (cfgEntryBlockID g) (mkCallFrame g pdInfo args)


resolvedCallName :: ResolvedCall p sym ext ret -> FunctionName
resolvedCallName (OverrideCall _ f) = f^.override
resolvedCallName (CrucibleCall _ f) = case frameHandle f of SomeHandle h -> handleName h

---------------------------------------------------------------------
-- Control-flow operations

-- | Immediately transtition to an 'OverrideState'.  On the next
--   execution step, the simulator will execute the given override.
runOverride ::
  Override p sym ext args ret {- ^ Override to execute -} ->
  ExecCont p sym ext rtp (OverrideLang ret) ('Just args)
runOverride o = ReaderT (return . OverrideState o)

-- | Immediately transition to a 'RunningState'.  On the next
--   execution step, the simulator will interpret the next basic
--   block.
continue :: RunningStateInfo blocks a -> ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just a)
continue rtgt = ReaderT (return . RunningState rtgt)

-- | Immediately transition to an 'AbortState'.  On the next
--   execution step, the simulator will unwind the 'SimState'
--   and resolve the abort.
runAbortHandler ::
  AbortExecReason {- ^ Description of the abort condition -} ->
  SimState p sym ext rtp f args {- ^ Simulator state prior to the abort -} ->
  IO (ExecState p sym ext rtp)
runAbortHandler rsn s = return (AbortState rsn s)

-- | Abort the current thread of execution with an error.
--   This adds a proof obligation that requires the current
--   execution path to be infeasible, and unwids to the
--   nearest branch point to resume.
runErrorHandler ::
  SimErrorReason {- ^ Description of the error -} ->
  SimState p sym ext rtp f args {- ^ Simulator state prior to the abort -} ->
  IO (ExecState p sym ext rtp)
runErrorHandler msg st =
  let ctx = st^.stateContext
      sym = ctx^.ctxSymInterface
   in ctxSolverProof ctx $
      do loc <- getCurrentProgramLoc sym
         let err = SimError loc msg
         let obl = LabeledPred (falsePred sym) err
         let rsn = AssumedFalse (AssumingNoError err)
         addProofObligation sym obl
         return (AbortState rsn st)

-- | Abort the current thread of execution with an error.
--   This adds a proof obligation that requires the current
--   execution path to be infeasible, and unwids to the
--   nearest branch point to resume.
runGenericErrorHandler ::
  String {- ^ Generic description of the error condition -} ->
  SimState p sym ext rtp f args {- ^ Simulator state prior to the abort -} ->
  IO (ExecState p sym ext rtp)
runGenericErrorHandler msg st = runErrorHandler (GenericSimError msg) st

-- | Transfer control to the given resolved jump, after first
--   checking for any pending symbolic merges at the destination
--   of the jump.
jumpToBlock ::
  IsSymInterface sym =>
  ResolvedJump sym blocks {- ^ Jump target and arguments -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just a)
jumpToBlock jmp = ReaderT $ return . ControlTransferState (CheckMergeResumption jmp)
{-# INLINE jumpToBlock #-}

performControlTransfer ::
  IsSymInterface sym =>
  ControlResumption p sym ext rtp f ->
  ExecCont p sym ext rtp f ('Just a)
performControlTransfer res =
  case res of
    ContinueResumption (ResolvedJump block_id args) ->
      withReaderT
        (stateCrucibleFrame %~ setFrameBlock block_id args)
        (continue (RunBlockStart block_id))
    CheckMergeResumption (ResolvedJump block_id args) ->
      withReaderT
        (stateCrucibleFrame %~ setFrameBlock block_id args)
        (checkForIntraFrameMerge (BlockTarget block_id))
    SwitchResumption cs ->
      variantCases cs
    OverrideResumption k args ->
      withReaderT
        (stateOverrideFrame.overrideRegMap .~ args)
        k

-- | Perform a conditional branch on the given predicate.
--   If the predicate is symbolic, this will record a symbolic
--   branch state.
conditionalBranch ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Pred sym {- ^ Predicate to branch on -} ->
  ResolvedJump sym blocks {- ^ True branch -} ->
  ResolvedJump sym blocks {- ^ False branch -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks ret) ('Just ctx)
conditionalBranch p xjmp yjmp = do
  top_frame <- view (stateTree.actFrame)
  Some pd <- return (top_frame^.crucibleTopFrame.framePostdom)

  x_frame <- cruciblePausedFrame xjmp top_frame pd
  y_frame <- cruciblePausedFrame yjmp top_frame pd

  intra_branch p x_frame y_frame pd

-- | Execute the next branch of a sequence of branch cases.
--   These arise from the implementation of the 'VariantElim'
--   construct.  The predicates are expected to be mutually
--   disjoint.  However, the construct still has well defined
--   semantics even in the case where they overlap; in this case,
--   the first branch with a true 'Pred' is taken.  In other words,
--   each branch assumes the negation of all the predicates of branches
--   appearing before it.
--
--   In the final default case (corresponding to an empty list of branches),
--   a 'VariantOptionsExhausted' abort will be executed.
variantCases ::
  IsSymInterface sym =>
  [(Pred sym, ResolvedJump sym blocks)] {- ^ Variant branches to execute -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)

variantCases [] =
  do fm <- view stateCrucibleFrame
     let loc = frameProgramLoc fm
     let rsn = VariantOptionsExhausted loc
     abortExec rsn

variantCases ((p,jmp) : cs) =
  do top_frame <- view (stateTree.actFrame)
     Some pd <- return (top_frame^.crucibleTopFrame.framePostdom)

     x_frame <- cruciblePausedFrame jmp top_frame pd
     let y_frame = PausedFrame (TotalRes top_frame) (SwitchResumption cs) Nothing

     intra_branch p x_frame y_frame pd

-- | Return a value from current Crucible execution.
returnValue :: forall p sym ext rtp f args.
  RegEntry sym (FrameRetType f) {- ^ return value -} ->
  ExecCont p sym ext rtp f args
returnValue arg =
  do nm <- view (stateTree.actFrame.gpValue.frameFunctionName)
     withReaderT
       (stateTree.actFrame.gpValue .~ RF nm arg)
       (checkForIntraFrameMerge ReturnTarget)


callFunction ::
  IsExprBuilder sym =>
  FnVal sym args ret {- ^ Function handle and any closure variables -} ->
  RegMap sym args {- ^ Arguments to the function -} ->
  ReturnHandler ret p sym ext rtp f a {- ^ How to modify the caller's scope with the return value -} ->
  ProgramLoc {-^ location of call -} ->
  ExecCont p sym ext rtp f a
callFunction fn args retHandler loc =
  do bindings <- view (stateContext.functionBindings)
     callStack <- view (stateTree . to activeFrames)
     let rcall = resolveCall bindings fn args loc callStack
     ReaderT $ return . CallState retHandler rcall

tailCallFunction ::
  FrameRetType f ~ ret =>
  FnVal sym args ret {- ^ Function handle and any closure variables -} ->
  RegMap sym args {- ^ Arguments to the function -} ->
  ValueFromValue p sym ext rtp ret ->
  ProgramLoc {-^ location of call -} ->
  ExecCont p sym ext rtp f a
tailCallFunction fn args vfv loc =
  do bindings <- view (stateContext.functionBindings)
     callStack <- view (stateTree . to activeFrames)
     let rcall = resolveCall bindings fn args loc callStack
     ReaderT $ return . TailCallState vfv rcall


-- | Immediately transition to the 'BranchMergeState'.
--   On the next simulator step, this will checks for the
--   opportunity to merge within a frame.
--
--   This should be called everytime the current control flow location
--   changes to a potential merge point.
checkForIntraFrameMerge ::
  CrucibleBranchTarget f args
    {- ^ The location of the block we are transferring to -} ->
  ExecCont p sym ext root f args

checkForIntraFrameMerge tgt =
  ReaderT $ return . BranchMergeState tgt


assumeInNewFrame ::
  IsSymInterface sym =>
  sym ->
  Assumption sym ->
  IO FrameIdentifier
assumeInNewFrame sym asm =
  do frm <- pushAssumptionFrame sym
     Ex.try @Ex.SomeException (addAssumption sym asm) >>= \case
       Left ex ->
         do void $ popAssumptionFrame sym frm
            Ex.throw ex
       Right () -> return frm

-- | Perform a single instance of path merging at a join point.
--   This will resume an alternate branch, if it is pending,
--   or merge result values if a completed branch has alread reached
--   this point. If there are no pending merge points at this location,
--   continue executing by transfering control to the given target.
performIntraFrameMerge ::
  IsSymInterface sym =>
  CrucibleBranchTarget f args
    {- ^ The location of the block we are transferring to -} ->
  ExecCont p sym ext root f args

performIntraFrameMerge tgt = do
  ActiveTree ctx0 er <- view stateTree
  sym <- view stateSymInterface
  case ctx0 of
    VFFBranch ctx assume_frame loc pred other_branch tgt'

      -- Did we get to our merge point (i.e., we are finished with this branch)
      | Just Refl <- testEquality tgt tgt' ->
        case other_branch of

          -- We still have some more work to do, reactivate the other, postponed branch
          VFFActivePath next ->
            do pathAssumes      <- liftIO $ popAssumptionFrame sym assume_frame
               pnot             <- liftIO $ notPred sym pred
               new_assume_frame <-
                  liftIO $ assumeInNewFrame sym (LabeledPred pnot (ExploringAPath loc (pausedLoc next)))

               -- The current branch is done
               let new_other = VFFCompletePath pathAssumes er
               resumeFrame next (VFFBranch ctx new_assume_frame loc pnot new_other tgt)

          -- We are done with both branches, pop-off back to the outer context.
          VFFCompletePath otherAssumes other ->
            do ar <- ReaderT $ \s ->
                 mergePartialResult s tgt pred er other

               -- Merge the assumptions from each branch and add to the
               -- current assumption frame
               pathAssumes <- liftIO $ popAssumptionFrame sym assume_frame

               liftIO $ addAssumptions sym
                 =<< mergeAssumptions sym pred pathAssumes otherAssumes

               -- Check for more potential merge targets.
               withReaderT
                 (stateTree .~ ActiveTree ctx ar)
                 (checkForIntraFrameMerge tgt)

    -- Since the other branch aborted before it got to the merge point,
    -- we merge-in the partiality on our current path and keep going.
    VFFPartial ctx loc pred ar needsAborting ->
      do er'  <- case needsAborting of
                   NoNeedToAbort    -> return er
                   NeedsToBeAborted -> ReaderT $ \s -> abortPartialResult s tgt er
         er'' <- liftIO $
           mergePartialAndAbortedResult sym loc pred er' ar
         withReaderT
           (stateTree .~ ActiveTree ctx er'')
           (checkForIntraFrameMerge tgt)

    -- There are no pending merges to deal with.  Instead, complete
    -- the transfer of control by either transitioning into an ordinary
    -- running state, or by returning a value to the calling context.
    _ -> case tgt of
           BlockTarget bid ->
             continue (RunPostBranchMerge bid)
           ReturnTarget ->
             handleSimReturn
               (er^.partialValue.gpValue.frameFunctionName)
               (returnContext ctx0)
               (er^.partialValue.gpValue.to fromReturnFrame)

---------------------------------------------------------------------
-- Abort handling

-- | The default abort handler calls `abortExecAndLog`.
defaultAbortHandler :: IsSymInterface sym => AbortHandler p sym ext rtp
defaultAbortHandler = AH abortExecAndLog

-- | Abort the current execution and roll back to the nearest
--   symbolic branch point.  When verbosity is 3 or more, a message
--   will be logged indicating the reason for the abort.
--
--   The default abort handler calls this function.
abortExecAndLog ::
  IsSymInterface sym =>
  AbortExecReason ->
  ExecCont p sym ext rtp f args
abortExecAndLog rsn = do
  t   <- view stateTree
  cfg <- view stateConfiguration
  ctx <- view stateContext
  v <- liftIO (getOpt =<< getOptionSetting verbosity cfg)
  when (v >= 3) $ do
    let frames = activeFrames t
    let msg = ppAbortExecReason rsn PP.<$$>
              PP.indent 2 (ppExceptionContext frames)
    -- Print error message.
    liftIO (hPrint (printHandle ctx) msg)

  -- Switch to new frame.
  abortExec rsn


-- | Abort the current execution and roll back to the nearest
--   symbolic branch point.
abortExec ::
  IsSymInterface sym =>
  AbortExecReason ->
  ExecCont p sym ext rtp f args
abortExec rsn = do
  ActiveTree ctx ar0 <- view stateTree
  resumeValueFromFrameAbort ctx $
    -- Get aborted result from active result.
    case ar0 of
      TotalRes e -> AbortedExec rsn e
      PartialRes loc pred ex ar1 ->
        AbortedBranch loc pred (AbortedExec rsn ex) ar1


------------------------------------------------------------------------
-- Internal operations

-- | Resolve the fact that the current branch aborted.
resumeValueFromFrameAbort ::
  IsSymInterface sym =>
  ValueFromFrame p sym ext r f ->
  AbortedResult sym ext {- ^ The execution that is being aborted. -} ->
  ExecCont p sym ext r g args
resumeValueFromFrameAbort ctx0 ar0 = do
  sym <- view stateSymInterface
  case ctx0 of

    -- This is the first abort.
    VFFBranch ctx assume_frame loc pred other_branch tgt ->
      do pnot <- liftIO $ notPred sym pred
         let nextCtx = VFFPartial ctx loc pnot ar0 NeedsToBeAborted

         -- Reset the backend path state
         _assumes <- liftIO $ popAssumptionFrame sym assume_frame

         case other_branch of

           -- We have some more work to do.
           VFFActivePath n ->
             do liftIO $ addAssumption sym (LabeledPred pnot (ExploringAPath loc (pausedLoc n)))
                resumeFrame n nextCtx

           -- The other branch had finished successfully;
           -- Since this one aborted, then the other one is really the only
           -- viable option we have, and so we commit to it.
           VFFCompletePath otherAssumes er ->
             do -- We are committed to the other path,
                -- assume all of its suspended assumptions
                liftIO $ addAssumptions sym otherAssumes

                -- check for further merges, then continue onward.
                withReaderT
                  (stateTree .~ ActiveTree nextCtx er)
                  (checkForIntraFrameMerge tgt)

    -- Both branches aborted
    VFFPartial ctx loc pred ay _ ->
      resumeValueFromFrameAbort ctx $ AbortedBranch loc pred ar0 ay

    VFFEnd ctx ->
      ReaderT $ return . UnwindCallState ctx ar0

-- | Run rest of execution given a value from value context and an aborted
-- result.
resumeValueFromValueAbort ::
  IsSymInterface sym =>
  ValueFromValue p sym ext r ret' ->
  AbortedResult sym ext ->
  ExecCont p sym ext r f a
resumeValueFromValueAbort ctx0 ar0 =
  case ctx0 of
    VFVCall ctx frm _rh ->
      do ActiveTree _oldFrm er <- view stateTree
         withReaderT
           (stateTree .~ ActiveTree ctx (er & partialValue.gpValue .~ frm))
           (resumeValueFromFrameAbort ctx ar0)
    VFVPartial ctx loc pred ay -> do
      resumeValueFromValueAbort ctx (AbortedBranch loc pred ar0 ay)
    VFVEnd ->
      do res <- view stateContext
         return $! ResultState $ AbortedResult res ar0

-- | Resume a paused frame.
resumeFrame ::
  IsSymInterface sym =>
  PausedFrame p sym ext rtp f ->
  ValueFromFrame p sym ext rtp f ->
  ExecCont p sym ext rtp g ba
resumeFrame (PausedFrame frm cont toLoc) ctx =
 do case toLoc of
      Nothing -> return ()
      Just l  ->
        do sym <- view stateSymInterface
           liftIO $ setCurrentProgramLoc sym l
    withReaderT
      (stateTree .~ ActiveTree ctx frm)
      (ReaderT $ return . ControlTransferState cont)
{-# INLINABLE resumeFrame #-}


-- | Transition immediately to a @ReturnState@.  We are done with all
--   intercall merges, and are ready to resmue execution in the caller's
--   context.
handleSimReturn ::
  IsSymInterface sym =>
  FunctionName {- ^ Name of the function we are returning from -} ->
  ValueFromValue p sym ext r ret {- ^ Context to return to. -} ->
  RegEntry sym ret {- ^ Value that is being returned. -} ->
  ExecCont p sym ext r f a
handleSimReturn fnName vfv return_value =
  ReaderT $ return . ReturnState fnName vfv return_value


-- | Resolve the return value, and begin executing in the caller's context again.
performReturn ::
  IsSymInterface sym =>
  FunctionName {- ^ Name of the function we are returning from -} ->
  ValueFromValue p sym ext r ret {- ^ Context to return to. -} ->
  RegEntry sym ret {- ^ Value that is being returned. -} ->
  ExecCont p sym ext r f a
performReturn fnName ctx0 v = do
  case ctx0 of
    VFVCall ctx (MF f) (ReturnToCrucible tpr rest) ->
      do ActiveTree _oldctx pres <- view stateTree
         let f' = extendFrame tpr (regValue v) rest f
         withReaderT
           (stateTree .~ ActiveTree ctx (pres & partialValue . gpValue .~ MF f'))
           (continue (RunReturnFrom fnName))

    VFVCall ctx _ TailReturnToCrucible ->
      do ActiveTree _oldctx pres <- view stateTree
         withReaderT
           (stateTree .~ ActiveTree ctx (pres & partialValue . gpValue .~ RF fnName v))
           (returnValue v)

    VFVCall ctx (OF f) (ReturnToOverride k) ->
      do ActiveTree _oldctx pres <- view stateTree
         withReaderT
           (stateTree .~ ActiveTree ctx (pres & partialValue . gpValue .~ OF f))
           (ReaderT (k v))

    VFVPartial ctx loc pred r ->
      do sym <- view stateSymInterface
         ActiveTree oldctx pres <- view stateTree
         newPres <- liftIO $
           mergePartialAndAbortedResult sym loc pred pres r
         withReaderT
            (stateTree .~ ActiveTree oldctx newPres)
            (performReturn fnName ctx v)

    VFVEnd ->
      do simctx <- view stateContext
         ActiveTree _oldctx pres <- view stateTree
         return $! ResultState $ FinishedResult simctx (pres & partialValue . gpValue .~ v)

cruciblePausedFrame ::
  ResolvedJump sym b ->
  GlobalPair sym (SimFrame sym ext (CrucibleLang b r) ('Just a)) ->
  CrucibleBranchTarget (CrucibleLang b r) pd_args {- ^ postdominator target -} ->
  ReaderT (SimState p sym ext rtp (CrucibleLang b z) ('Just dc_args)) IO
          (PausedFrame p sym ext rtp' (CrucibleLang b r))
cruciblePausedFrame jmp@(ResolvedJump x_id _) top_frame pd =
  do let res = case testEquality pd (BlockTarget x_id) of
                 Just Refl -> CheckMergeResumption jmp
                 Nothing   -> ContinueResumption jmp
     loc <- getTgtLoc x_id
     return $ PausedFrame (TotalRes top_frame) res (Just loc)

overrideSymbolicBranch ::
  IsSymInterface sym =>
  Pred sym ->

  RegMap sym then_args ->
  ExecCont p sym ext rtp (OverrideLang r) ('Just then_args) {- ^ if branch -} ->
  Maybe Position {- ^ optional if branch location -} ->

  RegMap sym else_args ->
  ExecCont p sym ext rtp (OverrideLang r) ('Just else_args) {- ^ else branch -} ->
  Maybe Position {- ^ optional else branch location -} ->

  ExecCont p sym ext rtp (OverrideLang r) ('Just args)
overrideSymbolicBranch p thn_args thn thn_pos els_args els els_pos =
  do top_frm <- view (stateTree.actFrame)
     let fnm     = top_frm^.gpValue.overrideSimFrame.override
     let thn_loc = mkProgramLoc fnm <$> thn_pos
     let els_loc = mkProgramLoc fnm <$> els_pos
     let thn_frm = PausedFrame (TotalRes top_frm) (OverrideResumption thn thn_args) thn_loc
     let els_frm = PausedFrame (TotalRes top_frm) (OverrideResumption els els_args) els_loc
     intra_branch p thn_frm els_frm ReturnTarget

getTgtLoc ::
  BlockID b y ->
  ReaderT (SimState p sym ext r (CrucibleLang b a) ('Just dc_args)) IO ProgramLoc
getTgtLoc (BlockID i) =
   do blocks <- view (stateCrucibleFrame . to frameBlockMap)
      return $ blockLoc (blocks Ctx.! i)

-- | Return the context of the current top frame.
asContFrame ::
  ActiveTree     p sym ext ret f args ->
  ValueFromFrame p sym ext ret f
asContFrame (ActiveTree ctx active_res) =
  case active_res of
    TotalRes{} -> ctx
    PartialRes loc pred _ex ar -> VFFPartial ctx loc pred ar NoNeedToAbort


-- | Return assertion where predicate equals a constant
predEqConst :: IsExprBuilder sym => sym -> Pred sym -> Bool -> IO (Pred sym)
predEqConst _   p True  = return p
predEqConst sym p False = notPred sym p

-- | Branch with a merge point inside this frame.
intra_branch ::
  IsSymInterface sym =>
  Pred sym
  {- ^ Branch condition branch -} ->

  PausedFrame p sym ext rtp f
  {- ^ true branch. -} ->

  PausedFrame p sym ext rtp f
  {- ^ false branch. -} ->

  CrucibleBranchTarget f (args :: Maybe (Ctx CrucibleType))
  {- ^ Postdominator merge point, where both branches meet again. -} ->

  ExecCont p sym ext rtp f ('Just dc_args)

intra_branch p t_label f_label tgt = do
  ctx <- asContFrame <$> view stateTree
  sym <- view stateSymInterface

  case asConstantPred p of
    Nothing ->
      ReaderT $ return . SymbolicBranchState p t_label f_label tgt

    Just chosen_branch ->
      do p' <- liftIO $ predEqConst sym p chosen_branch
         let a_frame = if chosen_branch then t_label else f_label
         loc <- liftIO $ getCurrentProgramLoc sym
         liftIO $ addAssumption sym (LabeledPred p' (ExploringAPath loc (pausedLoc a_frame)))
         resumeFrame a_frame ctx
{-# INLINABLE intra_branch #-}

-- | Branch with a merge point inside this frame.
performIntraFrameSplit ::
  IsSymInterface sym =>
  Pred sym
  {- ^ Branch condition -} ->

  PausedFrame p sym ext rtp f
  {- ^ active branch. -} ->

  PausedFrame p sym ext rtp f
  {- ^ other branch. -} ->

  CrucibleBranchTarget f (args :: Maybe (Ctx CrucibleType))
  {- ^ Postdominator merge point, where both branches meet again. -} ->

  ExecCont p sym ext rtp f ('Just dc_args)
performIntraFrameSplit p a_frame o_frame tgt =
  do ctx <- asContFrame <$> view stateTree
     sym <- view stateSymInterface
     loc <- liftIO $ getCurrentProgramLoc sym

     a_frame' <- pushPausedFrame a_frame
     o_frame' <- pushPausedFrame o_frame

     assume_frame <-
       liftIO $ assumeInNewFrame sym (LabeledPred p (ExploringAPath loc (pausedLoc a_frame')))

     -- Create context for paused frame.
     let todo = VFFActivePath o_frame'
         ctx' = VFFBranch ctx assume_frame loc p todo tgt

     -- Start a_state (where branch pred is p)
     resumeFrame a_frame' ctx'


performFunctionCall ::
  IsSymInterface sym =>
  ReturnHandler ret p sym ext rtp outer_frame outer_args ->
  ResolvedCall p sym ext ret ->
  ExecCont p sym ext rtp outer_frame outer_args
performFunctionCall retHandler frm =
  do sym <- view stateSymInterface
     case frm of
       OverrideCall o f ->
         -- Eventually, locations should be nested. However, for now,
         -- while they're not, it's useful for the location of an
         -- override to be the location of its call site, so we don't
         -- change it here.
         withReaderT
           (stateTree %~ pushCallFrame retHandler (OF f))
           (runOverride o)
       CrucibleCall entryID f -> do
         let loc = mkProgramLoc (resolvedCallName frm) (OtherPos "<function entry>")
         liftIO $ setCurrentProgramLoc sym loc
         withReaderT
           (stateTree %~ pushCallFrame retHandler (MF f))
           (continue (RunBlockStart entryID))

performTailCall ::
  IsSymInterface sym =>
  ValueFromValue p sym ext rtp ret ->
  ResolvedCall p sym ext ret ->
  ExecCont p sym ext rtp f a
performTailCall vfv frm =
  do sym <- view stateSymInterface
     let loc = mkProgramLoc (resolvedCallName frm) (OtherPos "<function entry>")
     liftIO $ setCurrentProgramLoc sym loc
     case frm of
       OverrideCall o f ->
         withReaderT
           (stateTree %~ swapCallFrame vfv (OF f))
           (runOverride o)
       CrucibleCall entryID f ->
         withReaderT
           (stateTree %~ swapCallFrame vfv (MF f))
           (continue (RunBlockStart entryID))

------------------------------------------------------------------------
-- Context tree manipulations

-- | Returns true if tree contains a single non-aborted execution.
isSingleCont :: ValueFromFrame p sym ext root a -> Bool
isSingleCont c0 =
  case c0 of
    VFFBranch{} -> False
    VFFPartial c _ _ _ _ -> isSingleCont c
    VFFEnd vfv -> isSingleVFV vfv

isSingleVFV :: ValueFromValue p sym ext r a -> Bool
isSingleVFV c0 = do
  case c0 of
    VFVCall c _ _ -> isSingleCont c
    VFVPartial c _ _ _ -> isSingleVFV c
    VFVEnd -> True

-- | Attempt to unwind a frame context into a value context.
--   This succeeds only if there are no pending symbolic
--   merges.
unwindContext ::
  ValueFromFrame p sym ext root f ->
  Maybe (ValueFromValue p sym ext root (FrameRetType f))
unwindContext c0 =
    case c0 of
      VFFBranch{} -> Nothing
      VFFPartial _ _ _ _ NeedsToBeAborted -> Nothing
      VFFPartial d loc pred ar NoNeedToAbort ->
        (\d' -> VFVPartial d' loc pred ar) <$> unwindContext d
      VFFEnd vfv -> return vfv

-- | Get the context for when returning (assumes no
-- intra-procedural merges are possible).
returnContext ::
  ValueFromFrame ctx sym ext root f ->
  ValueFromValue ctx sym ext root (FrameRetType f)
returnContext c0 =
  fromMaybe
    (panic "ExecutionTree.returnContext"
      [ "Unexpected attempt to exit function before all intra-procedural merges are complete."
      , "The call stack was:"
      , show (PP.pretty c0)
      ])
    (unwindContext c0)

-- | Replace the given frame with a new frame.  Succeeds
--   only if there are no pending symbolic merge points.
replaceTailFrame :: forall p sym ext a b c args args'.
  FrameRetType a ~ FrameRetType c =>
  ActiveTree p sym ext b a args ->
  SimFrame sym ext c args' ->
  Maybe (ActiveTree p sym ext b c args')
replaceTailFrame t@(ActiveTree c _) f = do
    vfv <- unwindContext c
    return $ swapCallFrame vfv f t

swapCallFrame ::
  ValueFromValue p sym ext rtp (FrameRetType f') ->
  SimFrame sym ext f' args' ->
  ActiveTree p sym ext rtp f args ->
  ActiveTree p sym ext rtp f' args'
swapCallFrame vfv frm (ActiveTree _ er) =
  ActiveTree (VFFEnd vfv) (er & partialValue . gpValue .~ frm)


pushCallFrame ::
  ReturnHandler (FrameRetType a) p sym ext r f old_args
    {- ^ What to do with the result of the function -} ->

  SimFrame sym ext a args
    {- ^ The code to run -} ->

  ActiveTree p sym ext r f old_args ->
  ActiveTree p sym ext r a args
pushCallFrame rh f' (ActiveTree ctx er) =
    ActiveTree (VFFEnd (VFVCall ctx old_frame rh)) er'
  where
  old_frame = er ^. partialValue ^. gpValue
  er'       = er &  partialValue  . gpValue .~ f'


-- | Create a tree that contains just a single path with no branches.
--
-- All branch conditions are converted to assertions.
extractCurrentPath ::
  ActiveTree p sym ext ret f args ->
  ActiveTree p sym ext ret f args
extractCurrentPath t =
  ActiveTree (vffSingleContext (t^.actContext))
             (TotalRes (t^.actFrame))

vffSingleContext ::
  ValueFromFrame p sym ext ret f ->
  ValueFromFrame p sym ext ret f
vffSingleContext ctx0 =
  case ctx0 of
    VFFBranch ctx _ _ _ _ _ -> vffSingleContext ctx
    VFFPartial ctx _ _ _ _  -> vffSingleContext ctx
    VFFEnd ctx              -> VFFEnd (vfvSingleContext ctx)

vfvSingleContext ::
  ValueFromValue p sym ext root top_ret ->
  ValueFromValue p sym ext root top_ret
vfvSingleContext ctx0 =
  case ctx0 of
    VFVCall ctx f h         -> VFVCall (vffSingleContext ctx) f h
    VFVPartial ctx _ _ _    -> vfvSingleContext ctx
    VFVEnd                  -> VFVEnd


------------------------------------------------------------------------
-- branchConditions

-- -- | Return all branch conditions along path to this node.
-- branchConditions :: ActiveTree ctx sym ext ret f args -> [Pred sym]
-- branchConditions t =
--   case t^.actResult of
--     TotalRes _ -> vffBranchConditions (t^.actContext)
--     PartialRes p _ _ -> p : vffBranchConditions (t^.actContext)

-- vffBranchConditions :: ValueFromFrame p sym ext ret f
--                     -> [Pred sym]
-- vffBranchConditions ctx0 =
--   case ctx0 of
--     VFFBranch   ctx _ _ p _ _  -> p : vffBranchConditions ctx
--     VFFPartial  ctx p _ _      -> p : vffBranchConditions ctx
--     VFFEnd  ctx -> vfvBranchConditions ctx

-- vfvBranchConditions :: ValueFromValue p sym ext root top_ret
--                     -> [Pred sym]
-- vfvBranchConditions ctx0 =
--   case ctx0 of
--     VFVCall     ctx _ _      -> vffBranchConditions ctx
--     VFVPartial  ctx p _      -> p : vfvBranchConditions ctx
--     VFVEnd                   -> []
