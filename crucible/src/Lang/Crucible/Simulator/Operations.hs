-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.Operations
-- Description      : Basic operations on execution trees
-- Copyright        : (c) Galois, Inc 2014
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- Operations corresponding to basic control-flow events and evaluation
-- expression evaluation on execution trees.
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
module Lang.Crucible.Simulator.Operations
  ( 
    -- * Execption handling
    abortTree
  , defaultAbortHandler

    -- * Primitive state transitions
  , continue
  , runOverride
  , runErrorHandler
  , runGenericErrorHandler
  , jumpToBlock

    -- * ReturnHandler
  , ReturnHandler
  , returnToOverride
  , returnToCrucible
  , tailReturnToCrucible

  , returnAndMerge
  , returnValue
  , FrameRetType

  , isSingleCont

    -- * Branch information
  , cruciblePausedFrame
  , symbolicBranch

    -- ** Branch and merge at return
  , stepVariantCases
    -- * High level operations.
  , replaceTailFrame
  , getIntraFrameBranchTarget
  , performIntraFrameMerge
  , callFn
  , abortExec
  , extractCurrentPath
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Data.Monoid ((<>))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Type.Equality hiding (sym)
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Config
import           What4.Interface
import           What4.ProgramLoc

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.Panic(panic)
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.ExecutionTree
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


-- | Merge two globals together.
mergeGlobalPair :: MuxFn p v
                -> MuxFn p (SymGlobalState sym)
                -> MuxFn p (GlobalPair sym v)
mergeGlobalPair merge_fn global_fn c x y =
  GlobalPair <$> merge_fn  c (x^.gpValue) (y^.gpValue)
             <*> global_fn c (x^.gpGlobals) (y^.gpGlobals)


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

defaultAbortHandler :: IsSymInterface sym => AbortHandler p sym ext rtp
defaultAbortHandler = AH abortTree

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



-- | Immediately transtition to an 'OverrideState'.  On the next
--   execution step, the simulator will execute the given override.
runOverride ::
  Override p sym ext args ret ->
  ExecCont p sym ext rtp (OverrideLang args ret) 'Nothing
runOverride o = ReaderT (return . OverrideState o)

-- | Immediately transition to a 'RunningState'.  On the next
--   execution step, the simulator will interpret the next basic
--   block.
continue :: ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just a)
continue = ReaderT (return . RunningState)

-- | Immediately transition to an 'AbortState'.  On the next
--   execution step, the simulator will unwind the 'SimState'
--   and resolve the abort.
runErrorHandler ::
  AbortExecReason ->
  SimState p sym ext rtp f args ->
  IO (ExecState p sym ext rtp)
runErrorHandler err s = return (AbortState err s)

-- | Capture the current location and emit a `ManualAbort`
--   reason into the 'AbortState. On the next
--   execution step, the simulator will unwind the 'SimState'
--   and resolve the abort.
runGenericErrorHandler ::
  String ->
  SimState p sym ext rtp f args ->
  IO (ExecState p sym ext rtp)
runGenericErrorHandler msg st =
  do let ctx = st^.stateContext
     let sym = ctx^.ctxSymInterface
     loc <- ctxSolverProof ctx (liftIO (getCurrentProgramLoc sym))
     runErrorHandler (ManualAbort loc msg) st



jumpToBlock :: IsSymInterface sym
             => BlockID blocks args
             -> RegMap sym args
             -> ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just a)
jumpToBlock block_id args =
  withReaderT
    (stateCrucibleFrame %~ setFrameBlock block_id args)
    (checkForIntraFrameMerge ContinueResumption (BlockTarget block_id))
{-# INLINE jumpToBlock #-}


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


runControlResumption ::
  IsSymInterface sym =>
  ControlResumption p sym ext rtp blocks r args ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) args
runControlResumption ContinueResumption = continue
runControlResumption (CheckMergeResumption k tgt) = checkForIntraFrameMerge k tgt
runControlResumption (SwitchResumption tgt cs) =
  stepVariantCases tgt cs
runControlResumption ReturnResumption =
  do RF v <- view (stateTree.actFrame.gpValue)
     returnValue v

-- | Resume a paused frame.
resumeFrame ::
  IsSymInterface sym =>
  PausedFrame p sym ext rtp blocks r a ->
  ValueFromFrame p sym ext rtp (CrucibleLang blocks r) ->
  ExecCont p sym ext rtp g ba
resumeFrame (PausedFrame frm cont) ctx =
    withReaderT
       (stateTree .~ ActiveTree ctx frm)
       (runControlResumption cont)
{-# INLINABLE resumeFrame #-}

------------------------------------------------------------------------
-- Return a value

returnAndMerge :: forall p sym ext rtp blocks r args.
  IsSymInterface sym =>
  RegEntry sym r ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) args
returnAndMerge arg =
  withReaderT
    (stateTree.actFrame.gpValue .~ RF arg)
    (checkForIntraFrameMerge ReturnResumption ReturnTarget)

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
         withReaderT
           (stateTree .~ ActiveTree ctx (return_value & partialValue . gpValue .~ MF f'))
           continue

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
  :: forall p sym ext root b r next_args pd_args
   . IsSymInterface sym
  => CrucibleBranchTarget b pd_args
     -- ^ The location of the post-dominator block.
  -> Maybe (BlockID b next_args)
     -- ^ 'Just' the frame corresponds to a label, 'Nothing' otherwise
  -> ControlResumption p sym ext root b r ('Just next_args)
     -- ^ What to run for next computation
  -> ControlResumption p sym ext root b r ('Just next_args)

--  -> ExecCont p sym ext root (CrucibleLang b r) ('Just next_args) -- state_args
tryIntraFrameMerge tgt m_bid active_cont
  | Just bid  <- m_bid
  , Just Refl <- testEquality tgt (BlockTarget bid)
  = CheckMergeResumption active_cont tgt

  | otherwise
  = active_cont


-- | Immediately transition to the 'ControlTransferState'.
--   On the next simulator step, this will checks for the
--   opportunity to merge within a frame.
--
--   This should be called everytime the current control flow location
--   will change.
checkForIntraFrameMerge ::
  ControlResumption p sym ext root b r args
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
  (IsSyntaxExtension ext, IsSymInterface sym) =>
  ControlResumption p sym ext root b r args
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
               let other = VFFCompletePath pathAssumes (PausedFrame er active_cont)
               resumeFrame next (VFFBranch ctx new_assume_frame loc pnot other tgt)

          -- We are done with both branches, pop-off back to the outer context.
          VFFCompletePath otherAssumes other ->
            do ar <- liftIO $ mergePartialResult s tgt p er (other^.pausedFrame)

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

    _ -> runControlResumption active_cont


--------------------------------------------------------------------------------
-- Branching


pushBranchVal :: (IsSymInterface sym)
              => SimState p sym ext root (CrucibleLang b a) ma
              -> PausedFrame p sym ext root b a args
              -> IO (PausedFrame p sym ext root b a args)
pushBranchVal s =
  let sym = stateSymInterface s
      iTypes = stateIntrinsicTypes s
   in traverseOf (pausedFrame.partialValue)
        (\(GlobalPair v gs) ->
           GlobalPair <$> pushCrucibleFrame sym iTypes v <*>
                          globalPushBranch sym iTypes gs)

cruciblePausedFrame ::
  BlockID b new_args ->
  RegMap sym new_args ->
  GlobalPair sym (SimFrame sym ext (CrucibleLang b r) ('Just a)) ->
  PausedFrame p sym ext rtp b r ('Just new_args)
cruciblePausedFrame x_id x_args top_frame =
  let cf = top_frame & crucibleTopFrame %~ setFrameBlock x_id x_args
   in PausedFrame (TotalRes cf) ContinueResumption

symbolicBranch
    :: (IsSymInterface sym, IsSyntaxExtension ext)
    => Int
    -> Pred sym
    -> BlockID blocks args
    -> RegMap sym args
    -> BlockID blocks args'
    -> RegMap sym args'
       -- ^ Registers for false state.
    -> ExecCont p sym ext rtp (CrucibleLang blocks ret) ('Just ctx)
symbolicBranch verb p x_id x_args y_id y_args = do
  ctx <- view stateContext
  top_frame <- view (stateTree.actFrame)

  let x_frame = cruciblePausedFrame x_id x_args top_frame
  let y_frame = cruciblePausedFrame y_id y_args top_frame

  let cur_frame = top_frame^.crucibleTopFrame
  case cur_frame^.framePostdom of
    Nothing -> do
      when (verb >= 5) $ do
        liftIO (hPutStrLn (printHandle ctx) $ "Return-dominated symbolic branch")
      intra_branch p (SomeLabel x_frame (Just x_id))
                     (SomeLabel y_frame (Just y_id))
                     ReturnTarget
    Just (Some pd_id) ->
      let tgt = BlockTarget pd_id
      in intra_branch p (SomeLabel x_frame (Just x_id))
                        (SomeLabel y_frame (Just y_id))
                        tgt


-- | 'Some' frame, together with its 'BlockID'.
data SomeLabel p sym ext r b a =
  forall args.
  SomeLabel !(PausedFrame p sym ext r b a ('Just args))
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
      o_frame <- liftIO $ pushBranchVal s o_state

      assume_frame <- liftIO $ pushAssumptionFrame sym
      liftIO $ addAssumption sym (LabeledPred p' (ExploringAPath loc a_loc))

      -- Create context for paused frame.
      let o_tree = o_frame & resume %~ tryIntraFrameMerge tgt o_id
      let todo = VFFActivePath o_loc o_tree
          ctx' = VFFBranch ctx assume_frame loc p' todo tgt

      -- Start a_state (where branch pred is p')
      resumeFrame (a_frame & resume %~ tryIntraFrameMerge tgt a_id) ctx'

    NoBranch chosen_branch ->
      do SomeLabel a_frame a_id <-
                      return (if chosen_branch then t_label else f_label)
         resumeFrame (a_frame & resume %~ tryIntraFrameMerge tgt a_id) ctx

{-# INLINABLE intra_branch #-}

stepVariantCases ::
  IsSymInterface sym =>
  CrucibleBranchTarget blocks args ->
  [ResolvedJump sym blocks] ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
stepVariantCases _tgt [] =
  do fm <- view stateCrucibleFrame
     let loc = frameProgramLoc fm
     let rsn = VariantOptionsExhaused loc
     abortExec rsn
stepVariantCases tgt (ResolvedJump p x_id x_args : cs) =
  do top_frame <- view (stateTree.actFrame)
     let x_frame = cruciblePausedFrame x_id x_args top_frame
         x_label = SomeLabel x_frame (Just x_id)

         y_frame = PausedFrame (TotalRes top_frame) (SwitchResumption tgt cs)
         y_label = SomeLabel y_frame Nothing

     intra_branch p x_label y_label tgt


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
             do let er = pv^.pausedFrame -- pv^.pausedValue

                -- We are committed to the other path,
                -- assume all of its suspended assumptions
                liftIO $ addAssumptions sym otherAssumes

                -- check for further merges, then continue onward.
                withReaderT
                  (stateTree .~ ActiveTree nextCtx er)
                  (checkForIntraFrameMerge (pv^.resume) tgt)

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
-- Running error handler


{-
????

checkStateConsistency :: CrucibleState p sym rtp blocks r a
                      -> BlockID blocks args
                         -- ^ Current block of top of stack frame.
                      -> IO ()
checkStateConsistency s (BlockID block_id) = do
  let f = s^.stateCrucibleFrame
  case getIntraFrameBranchTarget (s^.stateTree^.actContext) of
    Nothing -> return ()
    Just (Some tgt) -> do
      let Const _pd = framePostdomMap f Ctx.! block_id
      case branchTarget tgt of
        ReturnTarget -> return ()
          -- FIXME? I'm not sure ignoring this situation is correct...
          -- unless (null pd) $ do
          --   fail $ "The crucible tree reached an illegal state.\n"
          --       ++ "Branch target: Function return\n"
          --       ++ "Postdoms:      " ++ show pd
        BlockTarget _tgt' -> return ()
          -- when (Some tgt' `notElem` pd) $ do
          --   fail $ "The crucible tree reached an illegal state.\n"
          --       ++ "Branch target: " ++ show tgt' ++ "\n"
          --       ++ "Postdoms:      " ++ show pd
-}
