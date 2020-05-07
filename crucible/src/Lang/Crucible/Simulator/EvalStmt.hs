-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.EvalStmt
-- Description      : Provides functions for evaluating statements.
-- Copyright        : (c) Galois, Inc 2013-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides functions for evaluating Crucible statements.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.EvalStmt
  ( -- * High-level evaluation
    singleStepCrucible
  , executeCrucible
  , ExecutionFeature(..)
  , GenericExecutionFeature(..)
  , ExecutionFeatureResult(..)
  , genericToExecutionFeature
  , timeoutFeature

    -- * Lower-level evaluation operations
  , dispatchExecState
  , advanceCrucibleState
  , evalReg
  , evalReg'
  , evalExpr
  , evalArgs
  , evalJumpTarget
  , evalSwitchTarget
  , stepStmt
  , stepTerm
  , stepBasicBlock
  , readRef
  , alterRef
  ) where

import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad.Reader
import           Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import qualified Data.Text as Text
import           Data.Time.Clock
import           System.IO
import           System.IO.Error as Ex
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.Config
import           What4.Interface
import           What4.InterpretedFloatingPoint (freshFloatConstant)
import           What4.Partial

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics (IntrinsicTypes)
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Operations
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Utils.MuxTree


-- | Retrieve the value of a register.
evalReg ::
  Monad m =>
  Reg ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (RegValue sym tp)
evalReg r = (`regVal` r) <$> view (stateCrucibleFrame.frameRegs)

-- | Retrieve the value of a register, returning a 'RegEntry'.
evalReg' ::
  Monad m =>
  Reg ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (RegEntry sym tp)
evalReg' r = (`regVal'` r) <$> view (stateCrucibleFrame.frameRegs)


evalLogFn ::
  Int {- current verbosity -} ->
  CrucibleState p sym ext rtp blocks r ctx ->
  Int {- verbosity level of the message -} ->
  String ->
  IO ()
evalLogFn verb s n msg = do
  let h = s^.stateContext.to printHandle
  if verb >= n then
      do hPutStr h msg
         hFlush h
  else
      return ()

-- | Evaluate an expression.
evalExpr :: forall p sym ext ctx tp rtp blocks r.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  Expr ext ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) IO (RegValue sym tp)
evalExpr verb fm (App a) = ReaderT $ \s ->
  do let iteFns = s^.stateIntrinsicTypes
     let sym = s^.stateSymInterface
     let logFn = evalLogFn verb s
     r <- evalApp sym fm iteFns logFn
            (extensionEval (extensionImpl (s^.stateContext)) sym iteFns logFn)
            (\r -> runReaderT (evalReg r) s)
            a
     return $! r

evalArgs' :: forall sym ctx args.
  RegMap sym ctx ->
  Ctx.Assignment (Reg ctx) args ->
  RegMap sym args
evalArgs' m0 args = RegMap (fmapFC (getEntry m0) args)
  where getEntry :: RegMap sym ctx -> Reg ctx tp -> RegEntry sym tp
        getEntry (RegMap m) r = m Ctx.! regIndex r
{-# NOINLINE evalArgs' #-}

-- | Evaluate the actual arguments for a function call or block transfer.
evalArgs ::
  Monad m =>
  Ctx.Assignment (Reg ctx) args ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (RegMap sym args)
evalArgs args = ReaderT $ \s -> return $! evalArgs' (s^.stateCrucibleFrame.frameRegs) args
{-# INLINE evalArgs #-}

-- | Resolve the arguments for a jump.
evalJumpTarget ::
  (IsSymInterface sym, Monad m) =>
  JumpTarget blocks ctx {- ^  Jump target to evaluate -} ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (ResolvedJump sym blocks)
evalJumpTarget (JumpTarget tgt _ a) = ResolvedJump tgt <$> evalArgs a

-- | Resolve the arguments for a switch target.
evalSwitchTarget ::
  (IsSymInterface sym, Monad m) =>
  SwitchTarget blocks ctx tp {- ^ Switch target to evaluate -} ->
  RegEntry sym tp {- ^ Value inside the variant -}  ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (ResolvedJump sym blocks)
evalSwitchTarget (SwitchTarget tgt _tp a) x =
  do xs <- evalArgs a
     return (ResolvedJump tgt (assignReg' x xs))

-- | Update a reference cell with a new value. Writing an unassigned
-- value resets the reference cell to an uninitialized state.
alterRef ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  TypeRepr tp ->
  MuxTree sym (RefCell tp) ->
  PartExpr (Pred sym) (RegValue sym tp) ->
  SymGlobalState sym ->
  IO (SymGlobalState sym)
alterRef sym iTypes tpr rs newv globs = foldM upd globs (viewMuxTree rs)
  where
  f p a b = liftIO $ muxRegForType sym iTypes tpr p a b

  upd gs (r,p) =
    do let oldv = lookupRef r globs
       z <- mergePartial sym f p newv oldv
       return (gs & updateRef r z)

-- | Read from a reference cell.
readRef ::
  IsSymInterface sym =>
  sym ->
  IntrinsicTypes sym ->
  TypeRepr tp ->
  MuxTree sym (RefCell tp) ->
  SymGlobalState sym ->
  IO (RegValue sym tp)
readRef sym iTypes tpr rs globs =
  do let vs = map (\(r,p) -> (p,lookupRef r globs)) (viewMuxTree rs)
     let f p a b = liftIO $ muxRegForType sym iTypes tpr p a b
     pv <- mergePartials sym f vs
     let msg = ReadBeforeWriteSimError "Attempted to read uninitialized reference cell"
     readPartExpr sym pv msg


-- | Evaluation operation for evaluating a single straight-line
--   statement of the Crucible evaluator.
--
--   This is allowed to throw user exceptions or 'SimError'.
stepStmt :: forall p sym ext rtp blocks r ctx ctx'.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  Stmt ext ctx ctx' {- ^ Statement to evaluate -} ->
  StmtSeq ext blocks r ctx' {- ^ Remaning statements in the block -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
stepStmt verb fm stmt rest =
  do ctx <- view stateContext
     let sym = ctx^.ctxSymInterface
     let iTypes = ctxIntrinsicTypes ctx
     globals <- view (stateTree.actFrame.gpGlobals)

     let continueWith :: forall rtp' blocks' r' c f a.
           (SimState p sym ext rtp' f a -> SimState p sym ext rtp' (CrucibleLang blocks' r') ('Just c)) ->
           ExecCont p sym ext rtp' f a
         continueWith f = withReaderT f (checkConsTerm verb fm)

     case stmt of
       NewRefCell tpr x ->
         do let halloc = simHandleAllocator ctx
            v <- evalReg x
            r <- liftIO $ freshRefCell halloc tpr
            continueWith $
               (stateTree . actFrame . gpGlobals %~ insertRef sym r v) .
               (stateCrucibleFrame %~ extendFrame (ReferenceRepr tpr) (toMuxTree sym r) rest)

       NewEmptyRefCell tpr ->
         do let halloc = simHandleAllocator ctx
            r <- liftIO $ freshRefCell halloc tpr
            continueWith $
              stateCrucibleFrame %~ extendFrame (ReferenceRepr tpr) (toMuxTree sym r) rest

       ReadRefCell x ->
         do RegEntry (ReferenceRepr tpr) rs <- evalReg' x
            v <- liftIO $ readRef sym iTypes tpr rs globals
            continueWith $
              stateCrucibleFrame %~ extendFrame tpr v rest

       WriteRefCell x y ->
         do RegEntry (ReferenceRepr tpr) rs <- evalReg' x
            newv <- justPartExpr sym <$> evalReg y
            globals' <- liftIO $ alterRef sym iTypes tpr rs newv globals
            continueWith $
              (stateTree . actFrame . gpGlobals .~ globals') .
              (stateCrucibleFrame  . frameStmts .~ rest)

       DropRefCell x ->
         do RegEntry (ReferenceRepr tpr) rs <- evalReg' x
            globals' <- liftIO $ alterRef sym iTypes tpr rs Unassigned globals
            continueWith $
              (stateTree . actFrame . gpGlobals .~ globals') .
              (stateCrucibleFrame  . frameStmts .~ rest)

       ReadGlobal global_var -> do
         case lookupGlobal global_var globals of
           Nothing ->
             do let msg = ReadBeforeWriteSimError $ "Attempt to read undefined global " ++ show global_var
                liftIO $ addFailedAssertion sym msg
           Just v ->
             continueWith $
               (stateCrucibleFrame %~ extendFrame (globalType global_var) v rest)

       WriteGlobal global_var local_reg ->
         do v <- evalReg local_reg
            continueWith $
              (stateTree . actFrame . gpGlobals %~ insertGlobal global_var v) .
              (stateCrucibleFrame . frameStmts .~ rest)

       FreshConstant bt mnm ->
         do let nm = fromMaybe emptySymbol mnm
            v <- liftIO $ freshConstant sym nm bt
            continueWith $ stateCrucibleFrame %~ extendFrame (baseToType bt) v rest

       FreshFloat fi mnm ->
         do let nm = fromMaybe emptySymbol mnm
            v <- liftIO $ freshFloatConstant sym fm nm fi
            continueWith $ stateCrucibleFrame %~ extendFrame (FloatRepr fi) v rest

       SetReg tp e ->
         do v <- evalExpr verb fm e
            continueWith $ stateCrucibleFrame %~ extendFrame tp v rest

       ExtendAssign estmt -> do
         do let tp = appType estmt
            estmt' <- traverseFC evalReg' estmt
            ReaderT $ \s ->
              do (v,s') <- liftIO $ extensionExec (extensionImpl ctx) estmt' s
                 runReaderT
                   (continueWith $ stateCrucibleFrame %~ extendFrame tp v rest)
                   s'

       CallHandle ret_type fnExpr _types arg_exprs ->
         do hndl <- evalReg fnExpr
            args <- evalArgs arg_exprs
            loc <- liftIO $ getCurrentProgramLoc sym
            callFunction hndl args (ReturnToCrucible ret_type rest) loc

       Print e ->
         do msg <- evalReg e
            let msg' = case asString msg of
                         Just (UnicodeLiteral txt) -> Text.unpack txt
                         _ -> show (printSymExpr msg)
            liftIO $ do
              let h = printHandle ctx
              hPutStr h msg'
              hFlush h
            continueWith (stateCrucibleFrame  . frameStmts .~ rest)

       Assert c_expr msg_expr ->
         do c <- evalReg c_expr
            msg <- evalReg msg_expr
            let err = case asString msg of
                         Just (UnicodeLiteral txt) -> AssertFailureSimError (Text.unpack txt) ""
                         _ -> AssertFailureSimError "Symbolic message" (show (printSymExpr msg))
            liftIO $ assert sym c err
            continueWith (stateCrucibleFrame  . frameStmts .~ rest)

       Assume c_expr msg_expr ->
         do c <- evalReg c_expr
            msg <- evalReg msg_expr
            let msg' = case asString msg of
                         Just (UnicodeLiteral txt) -> Text.unpack txt
                         _ -> show (printSymExpr msg)
            liftIO $
              do loc <- getCurrentProgramLoc sym
                 addAssumption sym (LabeledPred c (AssumptionReason loc msg'))
            continueWith (stateCrucibleFrame  . frameStmts .~ rest)


{-# INLINABLE stepTerm #-}

-- | Evaluation operation for evaluating a single block-terminator
--   statement of the Crucible evaluator.
--
--   This is allowed to throw user exceptions or 'SimError'.
stepTerm :: forall p sym ext rtp blocks r ctx.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Verbosity -} ->
  TermStmt blocks r ctx {- ^ Terminating statement to evaluate -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)

stepTerm _ (Jump tgt) =
  jumpToBlock =<< evalJumpTarget tgt

stepTerm _ (Return arg) =
  returnValue =<< evalReg' arg

stepTerm _ (Br c x y) =
  do x_jump <- evalJumpTarget x
     y_jump <- evalJumpTarget y
     p <- evalReg c
     conditionalBranch p x_jump y_jump

stepTerm _ (MaybeBranch tp e j n) =
  do evalReg e >>= \case
       Unassigned -> jumpToBlock =<< evalJumpTarget n
       PE p v ->
         do j_jump <- evalSwitchTarget j (RegEntry tp v)
            n_jump <- evalJumpTarget n
            conditionalBranch p j_jump n_jump

stepTerm _ (VariantElim ctx e cases) =
  do vs <- evalReg e
     jmps <- ctx & Ctx.traverseAndCollect (\i tp ->
                case vs Ctx.! i of
                  VB Unassigned ->
                    return []
                  VB (PE p v) ->
                    do jmp <- evalSwitchTarget (cases Ctx.! i) (RegEntry tp v)
                       return [(p,jmp)])

     variantCases jmps

-- When we make a tail call, we first try to unwind our calling context
-- and replace the currently-active frame with the frame of the new called
-- function.  However, this is only successful if there are no pending
-- symbolic merges.
--
-- If there _are_ pending merges we instead treat the tail call as normal
-- call-then-return sequence, pushing a new call frame on the top of our
-- current context (rather than replacing it).  The TailReturnToCrucible
-- return handler tells the simulator to immediately invoke another return
-- in the caller, which is still present on the stack in this scenario.
stepTerm _ (TailCall fnExpr _types arg_exprs) =
  do cl   <- evalReg fnExpr
     args <- evalArgs arg_exprs
     ctx <- view (stateTree.actContext)
     sym <- view stateSymInterface
     loc <- liftIO $ getCurrentProgramLoc sym
     case unwindContext ctx of
       Just vfv -> tailCallFunction cl args vfv loc
       Nothing  -> callFunction cl args TailReturnToCrucible loc

stepTerm _ (ErrorStmt msg) =
  do msg' <- evalReg msg
     sym <- view stateSymInterface
     liftIO $ case asString msg' of
       Just (UnicodeLiteral txt) ->
                   addFailedAssertion sym
                      $ GenericSimError $ Text.unpack txt
       Nothing  -> addFailedAssertion sym
                      $ GenericSimError $ show (printSymExpr msg')


-- | Checks whether the StmtSeq is a Cons or a Term,
--   to give callers another chance to jump into Crucible's control flow
checkConsTerm ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
checkConsTerm verb fm =
     do cf <- view stateCrucibleFrame

        case cf^.frameStmts of
          ConsStmt _ _ _ -> stepBasicBlock verb fm
          TermStmt _ _ -> continue (RunBlockEnd (cf^.frameBlockID))

-- | Main evaluation operation for running a single step of
--   basic block evaluation.
--
--   This is allowed to throw user exceptions or 'SimError'.
stepBasicBlock ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
stepBasicBlock verb fm =
  do ctx <- view stateContext
     let sym = ctx^.ctxSymInterface
     let h = printHandle ctx
     cf <- view stateCrucibleFrame

     case cf^.frameStmts of
       ConsStmt pl stmt rest ->
         do liftIO $
              do setCurrentProgramLoc sym pl
                 let sz = regMapSize (cf^.frameRegs)
                 when (verb >= 4) $ ppStmtAndLoc h (frameHandle cf) pl (ppStmt sz stmt)
            stepStmt verb fm stmt rest

       TermStmt pl termStmt -> do
         do liftIO $
              do setCurrentProgramLoc sym pl
                 when (verb >= 4) $ ppStmtAndLoc h (frameHandle cf) pl (pretty termStmt)
            stepTerm verb termStmt

ppStmtAndLoc :: Handle -> SomeHandle -> ProgramLoc -> Doc -> IO ()
ppStmtAndLoc h sh pl stmt = do
  hPrint h $
    text (show sh) <> char ':' <$$>
    indent 2 (stmt <+> text "%" <+> ppNoFileName (plSourceLoc pl))
  hFlush h

performStateRun ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  RunningStateInfo blocks ctx ->
  Int {- ^ Current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
performStateRun info verb fm = case info of
  RunPostBranchMerge bid -> continue (RunBlockStart bid)
  _ -> stepBasicBlock verb fm


----------------------------------------------------------------------
-- ExecState manipulations


-- | Given an 'ExecState', examine it and either enter the continuation
--   for final results, or construct the appropriate 'ExecCont' for
--   continuing the computation and enter the provided intermediate continuation.
dispatchExecState ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  IO Int {- ^ Action to query the current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  ExecState p sym ext rtp {- ^ Current execution state of the simulator -} ->
  (ExecResult p sym ext rtp -> IO z) {- ^ Final continuation for results -} ->
  (forall f a. ExecCont p sym ext rtp f a -> SimState p sym ext rtp f a -> IO z)
    {- ^ Intermediate continuation for running states -} ->
  IO z
dispatchExecState getVerb fm exst kresult k =
  case exst of
    ResultState res ->
      kresult res

    InitialState simctx globals ah ret cont ->
      do st <- initSimState simctx globals ah ret
         k cont st

    AbortState rsn st ->
      let (AH handler) = st^.abortHandler in
      k (handler rsn) st

    OverrideState ovr st ->
      k (overrideHandler ovr) st

    SymbolicBranchState p a_frame o_frame tgt st ->
      k (performIntraFrameSplit p a_frame o_frame tgt) st

    ControlTransferState resumption st ->
      k (performControlTransfer resumption) st

    BranchMergeState tgt st ->
      k (performIntraFrameMerge tgt) st

    UnwindCallState vfv ar st ->
      k (resumeValueFromValueAbort vfv ar) st

    CallState retHandler frm st ->
      k (performFunctionCall retHandler frm) st

    TailCallState vfv frm st ->
      k (performTailCall vfv frm) st

    ReturnState fnm vfv ret st ->
      k (performReturn fnm vfv ret) st

    RunningState info st ->
      do v <- getVerb
         k (performStateRun info v fm) st
{-# INLINE dispatchExecState #-}


-- | Run the given @ExecCont@ on the given @SimState@,
--   being careful to catch any simulator abort exceptions
--   that are thrown and dispatch them to the abort handler.
advanceCrucibleState ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  ExecCont p sym ext rtp f a ->
  SimState p sym ext rtp f a ->
  IO (ExecState p sym ext rtp)
advanceCrucibleState m st =
     Ex.catches (runReaderT m st)
                [ Ex.Handler $ \(e::AbortExecReason) ->
                    runAbortHandler e st
                , Ex.Handler $ \(e::Ex.IOException) ->
                    if Ex.isUserError e then
                      runGenericErrorHandler (Ex.ioeGetErrorString e) st
                    else
                      Ex.throwIO e
                ]


-- | Run a single step of the Crucible symbolic simulator.
singleStepCrucible ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  FloatModeRepr (CrucibleFloatMode sym) ->
  ExecState p sym ext rtp ->
  IO (ExecState p sym ext rtp)
singleStepCrucible verb fm exst =
  dispatchExecState
    (return verb)
    fm
    exst
    (return . ResultState)
    advanceCrucibleState


-- | This datatype indicates the possible results that an execution feature
--   can have.
data ExecutionFeatureResult p sym ext rtp where
  -- | This execution feature result indicates that no state changes were
  --   made.
  ExecutionFeatureNoChange       :: ExecutionFeatureResult p sym ext rtp

  -- | This execution feature indicates that the state was modified but
  --   not changed in an "essential" way.  For example, internal bookkeeping
  --   datastructures for the execution feature might be modified, but the
  --   state is not transitioned to a fundamentally different state.
  --
  --   When this result is returned, later execution features in the
  --   installed stack will be executed, until the main simulator loop
  --   is encountered.  Contrast with the \"new state\" result.
  ExecutionFeatureModifiedState ::
     ExecState p sym ext rtp -> ExecutionFeatureResult p sym ext rtp

  -- | This execution feature result indicates that the state was modified
  --   in an essential way that transforms it into new state altogether.
  --   When this result is returned, it preempts any later execution
  --   features and the main simulator loop and instead returns to the head
  --   of the execution feature stack.
  --
  --   NOTE: In particular, the execution feature will encounter the
  --   state again before the simulator loop.  It is therefore very
  --   important that the execution feature be prepared to immediately
  --   encounter the same state again and make significant execution
  --   progress on it, or ignore it so it makes it to the main simulator
  --   loop.  Otherwise, the execution feature will loop back to itself
  --   infinitely, starving out useful work.
  ExecutionFeatureNewState ::
     ExecState p sym ext rtp -> ExecutionFeatureResult p sym ext rtp


-- | An execution feature represents a computation that is allowed to intercept
--   the processing of execution states to perform additional processing at
--   each intermediate state.  A list of execution features is accepted by
--   `executeCrucible`.  After each step of the simulator, the execution features
--   are consulted, each in turn.  After all the execution features have run,
--   the main simulator code is executed to advance the simulator one step.
--
--   If an execution feature wishes to make changes to the execution
--   state before further execution happens, the return value can be
--   used to return a modified state.  If this happens, the current
--   stack of execution features is abandoned and a fresh step starts
--   over immediately from the top of the execution features.  In
--   essence, each execution feature can preempt all following
--   execution features and the main simulator loop. In other words,
--   the main simulator only gets reached if every execution feature
--   returns @Nothing@.  It is important, therefore, that execution
--   features make only a bounded number of modification in a row, or
--   the main simulator loop will be starved out.
newtype ExecutionFeature p sym ext rtp =
  ExecutionFeature
  { runExecutionFeature :: ExecState p sym ext rtp -> IO (ExecutionFeatureResult p sym ext rtp)
  }

-- | A generic execution feature is an execution feature that is
--   agnostic to the execution environment, and is therefore
--   polymorphic over the @p@, @ext@ and @rtp@ variables.
newtype GenericExecutionFeature sym =
  GenericExecutionFeature
  { runGenericExecutionFeature :: forall p ext rtp.
      (IsSymInterface sym, IsSyntaxExtension ext) =>
        ExecState p sym ext rtp -> IO (ExecutionFeatureResult p sym ext rtp)
  }

genericToExecutionFeature ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  GenericExecutionFeature sym -> ExecutionFeature p sym ext rtp
genericToExecutionFeature (GenericExecutionFeature f) = ExecutionFeature f


-- | Given a 'SimState' and an execution continuation,
--   apply the continuation and execute the resulting
--   computation until completion.
--
--   This function is responsible for catching
--   'AbortExecReason' exceptions and 'UserError'
--   exceptions and invoking the 'errorHandler'
--   contained in the state.
executeCrucible :: forall p sym ext rtp.
  ( IsSymInterface sym
  , IsSyntaxExtension ext
  ) =>
  FloatModeRepr (CrucibleFloatMode sym) ->
  [ ExecutionFeature p sym ext rtp ] {- ^ Execution features to install -} ->
  ExecState p sym ext rtp   {- ^ Execution state to begin executing -} ->
  IO (ExecResult p sym ext rtp)
executeCrucible fm execFeatures exst0 =
  do let cfg = getConfiguration . view ctxSymInterface . execStateContext $ exst0
     verbOpt <- getOptionSetting verbosity cfg

     let loop exst =
           dispatchExecState
             (fromInteger <$> getOpt verbOpt)
             fm
             exst
             return
             (\m st -> knext =<< advanceCrucibleState m st)

         applyExecutionFeature feat m = \exst ->
             runExecutionFeature feat exst >>= \case
                  ExecutionFeatureNoChange            -> m exst
                  ExecutionFeatureModifiedState exst' -> m exst'
                  ExecutionFeatureNewState exst'      -> knext exst'

         knext = foldr applyExecutionFeature loop execFeatures

     knext exst0


-- | This feature will terminate the execution of a crucible simulator
--   with a @TimeoutResult@ after a given interval of wall-clock time
--   has elapsed.
timeoutFeature ::
  NominalDiffTime ->
  IO (GenericExecutionFeature sym)
timeoutFeature timeout =
  do startTime <- getCurrentTime
     let deadline = addUTCTime timeout startTime
     return $ GenericExecutionFeature $ \exst ->
       case exst of
         ResultState _ -> return ExecutionFeatureNoChange
         _ ->
            do now <- getCurrentTime
               if deadline >= now then
                 return ExecutionFeatureNoChange
               else
                 return (ExecutionFeatureNewState (ResultState (TimeoutResult exst)))
