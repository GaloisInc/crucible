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
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.EvalStmt
  ( SomeSimFrame(..)
  , resolveCallFrame

  , singleStepCrucible
  , executeCrucible

  , evalReg
  , evalExpr
  , stepTerm
  , stepStmt
  , stepBasicBlock
  ) where

import qualified Control.Exception as Ex
import           Control.Lens
import           Control.Monad.Reader
import           Data.Maybe (fromMaybe)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import qualified Data.Text as Text
import           System.IO
import           System.IO.Error as Ex
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           What4.Config
import           What4.Interface
import           What4.Partial
import           What4.ProgramLoc
import           What4.Symbol (emptySymbol)
import           What4.Utils.MonadST

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.CFG.Extension
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Frame
import           Lang.Crucible.Simulator.Intrinsics (IntrinsicTypes)
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.Operations
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Utils.MuxTree


------------------------------------------------------------------------
-- resolveCallFrame

data SomeSimFrame p sym ext ret where
  SomeOF :: Override p sym ext args ret
         -> OverrideFrame sym ret args
         -> SomeSimFrame p sym ext ret
  SomeCF :: CallFrame sym ext blocks ret args
         -> SomeSimFrame p sym ext ret

resolveCallFrame :: FunctionBindings p sym ext
                 -> FnVal sym args ret
                 -> RegMap sym args
                 -> SomeSimFrame p sym ext ret
resolveCallFrame bindings c0 args =
  case c0 of
    ClosureFnVal c tp v -> do
      resolveCallFrame bindings c (assignReg tp v args)
    HandleFnVal h -> do
      case lookupHandleMap h bindings of
        Nothing -> Ex.throw . userError $
          "Could not resolve function: " ++ show (handleName h)
        Just (UseOverride o) -> do
          let f = OverrideFrame { override = overrideName o
                                , overrideRegMap = args
                                }
           in SomeOF o f
        Just (UseCFG g pdInfo) -> do
          SomeCF (mkCallFrame g pdInfo args)



------------------------------------------------------------------------
-- CrucibleState

evalLogFn :: CrucibleState p sym ext rtp blocks r ctx
          -> Int
          -> String
          -> IO ()
evalLogFn s n msg = do
  let h = printHandle (s^.stateContext)
  let cfg = stateGetConfiguration s
  verb <- getMaybeOpt =<< getOptionSetting verbosity cfg
  case verb of
    Just v | v >= toInteger n ->
      do hPutStr h msg
         hFlush h
    _ -> return ()

-- | Evaluate an expression.
evalReg ::
  Monad m =>
  Reg ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (RegValue sym tp)
evalReg r = (`regVal` r) <$> view (stateCrucibleFrame.frameRegs)

-- | Evaluate an expression, returning a 'RegEntry'
evalReg' ::
  Monad m =>
  Reg ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (RegEntry sym tp)
evalReg' r = (`regVal'` r) <$> view (stateCrucibleFrame.frameRegs)

-- | Evaluate an expression.
evalExpr :: forall p sym ext ctx tp rtp blocks r.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Expr ext ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) IO (RegValue sym tp)
evalExpr (App a) = do
  s <- ask
  let iteFns = stateIntrinsicTypes s
  let sym = stateSymInterface s
  let logFn = evalLogFn s
  r <- liftIO $ evalApp sym iteFns logFn
                  (extensionEval (extensionImpl (s^.stateContext)) sym iteFns logFn)
                  (\r -> runReaderT (evalReg r) s)
                  a
  return $! r

------------------------------------------------------------------------
-- Pretty printing

ppStmtAndLoc :: Handle -> SomeHandle -> ProgramLoc -> Doc -> IO ()
ppStmtAndLoc h sh pl stmt = do
  hPrint h $
    text (show sh) <> char ':' <$$>
    indent 2 (stmt <+> text "%" <+> ppNoFileName (plSourceLoc pl))
  hFlush h

------------------------------------------------------------------------
-- JumpCall


data JumpCall sym blocks where
  JumpCall :: !(BlockID blocks args)
           -> !(RegMap sym args)
           -> JumpCall sym blocks

evalJumpTarget ::
  (IsSymInterface sym, Monad m) =>
  JumpTarget blocks ctx ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (JumpCall sym blocks)
evalJumpTarget (JumpTarget tgt _ a) = JumpCall tgt <$> evalArgs a

------------------------------------------------------------------------
-- SwitchCall

data SwitchCall sym blocks tp where
  SwitchCall :: !(BlockID blocks (args ::> tp))
             -> !(RegMap sym args)
             -> SwitchCall sym blocks tp

evalSwitchTarget ::
  (IsSymInterface sym, Monad m) =>
  SwitchTarget blocks ctx tp ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (SwitchCall sym blocks tp)
evalSwitchTarget (SwitchTarget tgt _tp a) = SwitchCall tgt <$> evalArgs a


-- | Jump to given block.
--
-- May throw a user error if merging fails.
jump :: (IsSymInterface sym, IsSyntaxExtension ext)
      => JumpTarget blocks args
      -> ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just args)
jump (JumpTarget block_id _tp a) =
  jumpToBlock block_id =<< evalArgs a


data VariantCall sym blocks tp where
  VariantCall :: TypeRepr tp
              -> VariantBranch sym tp
              -> SwitchCall sym blocks tp
              -> VariantCall sym blocks tp

evalArgs' :: forall sym ctx args.
  RegMap sym ctx ->
  Ctx.Assignment (Reg ctx) args ->
  RegMap sym args
evalArgs' m0 args = RegMap (fmapFC (getEntry m0) args)
  where getEntry :: RegMap sym ctx -> Reg ctx tp -> RegEntry sym tp
        getEntry (RegMap m) r = m Ctx.! regIndex r
{-# NOINLINE evalArgs' #-}

evalArgs ::
  Monad m =>
  Ctx.Assignment (Reg ctx) args ->
  ReaderT (CrucibleState p sym ext rtp blocks r ctx) m (RegMap sym args)
evalArgs args = ReaderT $ \s -> return $! evalArgs' (s^.stateCrucibleFrame.frameRegs) args
{-# INLINE evalArgs #-}


{-# INLINABLE stepTerm #-}

-- | Evaluation operation for evaluating a single block-terminator
--   statement of the Crucible evaluator.
--
--   This is allowed to throw user execeptions or SimError.
stepTerm :: forall p sym ext rtp blocks r ctx.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Verbosity -} ->
  TermStmt blocks r ctx ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
stepTerm _ (Jump tgt) = jump tgt

stepTerm verb (Br c x y) =
  do JumpCall x_id x_args <- evalJumpTarget x
     JumpCall y_id y_args <- evalJumpTarget y
     p <- evalReg c
     symbolicBranch verb p x_id x_args y_id y_args

stepTerm verb (MaybeBranch tp e j n) =
  do evalReg e >>= \case
       Unassigned -> jump n
       PE p v ->
         do SwitchCall j_tgt j_args0 <- evalSwitchTarget j
            JumpCall   n_tgt n_args  <- evalJumpTarget n
            let j_args = assignReg tp v j_args0
            symbolicBranch verb p j_tgt j_args n_tgt n_args

stepTerm _ (VariantElim ctx e cases) =
  do vs <- evalReg e
     cases' <- Ctx.generateM (Ctx.size ctx) (\i ->
                     VariantCall (ctx Ctx.! i) (vs Ctx.! i) <$> evalSwitchTarget (cases Ctx.! i))
     let ls = foldMapFC (\(VariantCall tp (VB v) (SwitchCall tgt regs)) ->
                case v of
                  Unassigned -> []
                  PE p v' -> [ResolvedJump p tgt (assignReg tp v' regs)])
              cases'
     pd <- view (stateCrucibleFrame.framePostdom)
     Some tgt <- case pd of
                   Nothing -> return (Some ReturnTarget)
                   Just (Some pd_id) -> return (Some (BlockTarget pd_id))
     stepVariantCases tgt ls

stepTerm _ (Return arg) =
  returnAndMerge =<< evalReg' arg

-- When we make a tail call, we first try to unwind our calling context
-- and replace the currently-active frame with the frame of the new called
-- function.  However, this is only successful if there are no pending
-- symbolic merges.
--
-- If there _are_ pending merges we instead treat the tail call as normal
-- call-then-return sequence, pushing a new call frame on the top of our
-- current context (rather than replacing it).  The tailReturnToCrucible
-- function is invoked when the tail-called function returns; it immediately
-- invokes another return in the other caller, which is still present on the
-- stack in this scenerio.

stepTerm _ (TailCall fnExpr _types arg_exprs) =
  do cl   <- evalReg fnExpr
     args <- evalArgs arg_exprs
     bindings <- view (stateContext.functionBindings)
     t <- view stateTree
     case resolveCallFrame bindings cl args of
       SomeOF o f ->
         case replaceTailFrame t (OF f) of
           Just t' -> withReaderT
                        (stateTree .~ t')
                        (runOverride o)
           Nothing -> withReaderT
                        (stateTree %~ callFn tailReturnToCrucible (OF f))
                        (runOverride o)
       SomeCF f ->
         case replaceTailFrame t (MF f) of
           Just t' -> withReaderT (stateTree .~ t') continue
           Nothing -> withReaderT (stateTree %~ callFn tailReturnToCrucible (MF f)) continue

stepTerm _ (ErrorStmt msg) =
  do msg' <- evalReg msg
     sym <- asks stateSymInterface
     liftIO $ case asString msg' of
       Just txt -> addFailedAssertion sym
                      $ GenericSimError $ Text.unpack txt
       Nothing  -> addFailedAssertion sym
                      $ GenericSimError $ show (printSymExpr msg')


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
--   This is allowed to throw user execeptions or SimError.
stepStmt :: forall p sym ext rtp blocks r ctx ctx'.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  Stmt ext ctx ctx' {- ^ Statement to evaluate -} ->
  StmtSeq ext blocks r ctx' {- ^ Remaning statements in the block -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
stepStmt verb stmt rest =
  do ctx <- view stateContext
     let sym = ctx^.ctxSymInterface
     let iTypes = ctxIntrinsicTypes ctx
     globals <- view (stateTree.actFrame.gpGlobals)

     let continueWith :: forall rtp' blocks' r' c f a.
           (SimState p sym ext rtp' f a -> SimState p sym ext rtp' (CrucibleLang blocks' r') ('Just c)) ->
           ExecCont p sym ext rtp' f a
         continueWith f = withReaderT f (stepBasicBlock verb)

     case stmt of
       NewRefCell tpr x ->
         do let halloc = simHandleAllocator ctx
            v <- evalReg x
            r <- liftST (freshRefCell halloc tpr)
            continueWith $
               (stateTree . actFrame . gpGlobals %~ insertRef sym r v) .
               (stateCrucibleFrame %~ extendFrame (ReferenceRepr tpr) (toMuxTree sym r) rest)

       NewEmptyRefCell tpr ->
         do let halloc = simHandleAllocator ctx
            r <- liftST (freshRefCell halloc tpr)
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

       SetReg tp e ->
         do v <- evalExpr e
            continueWith $ stateCrucibleFrame %~ extendFrame tp v rest

       ExtendAssign estmt -> do
         do estmt' <- traverseFC evalReg' estmt
            ReaderT $ \s ->
              do (v,s') <- liftIO $ extensionExec (extensionImpl ctx) estmt' s
                 let tp = appType estmt
                 runReaderT
                   (continueWith $ stateCrucibleFrame %~ extendFrame tp v rest)
                   s'

       CallHandle ret_type fnExpr _types arg_exprs ->
         do hndl <- evalReg fnExpr
            args <- evalArgs arg_exprs
            bindings <- view (stateContext.functionBindings)
            case resolveCallFrame bindings hndl args of
              SomeOF o f ->
                withReaderT
                  (stateTree %~ callFn (returnToCrucible ret_type rest) (OF f))
                  (runOverride o)
              SomeCF f ->
                withReaderT
                  (stateTree %~ callFn (returnToCrucible ret_type rest) (MF f))
                  continue

       Print e ->
         do msg <- evalReg e
            let msg' = case asString msg of
                         Just txt -> Text.unpack txt
                         _ -> show (printSymExpr msg)
            liftIO $ do
              let h = printHandle ctx
              hPutStr h msg'
              hFlush h
            continueWith (stateCrucibleFrame  . frameStmts .~ rest)

       Assert c_expr msg_expr ->
         do c <- evalReg c_expr
            msg <- evalReg msg_expr
            let msg' = case asString msg of
                         Just txt -> Text.unpack txt
                         _ -> show (printSymExpr msg)
            liftIO $ assert sym c (AssertFailureSimError msg')
            continueWith (stateCrucibleFrame  . frameStmts .~ rest)

-- | Main evaluation operation for running a single step of
--   basic block evalaution.
--
--   This is allowed to throw user execeptions or SimError.
stepBasicBlock ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  ExecCont p sym ext rtp (CrucibleLang blocks r) ('Just ctx)
stepBasicBlock verb =
  do ctx <- view stateContext
     let sym = ctx^.ctxSymInterface
     let h = printHandle ctx
     cf <- view stateCrucibleFrame

     case cf^.frameStmts of
       TermStmt pl stmt -> do
         do liftIO $
              do setCurrentProgramLoc sym pl
                 when (verb >= 4) $ ppStmtAndLoc h (frameHandle cf) pl (pretty stmt)
            stepTerm verb stmt

       ConsStmt pl stmt rest ->
         do liftIO $
              do setCurrentProgramLoc sym pl
                 let sz = regMapSize (cf^.frameRegs)
                 when (verb >= 4) $ ppStmtAndLoc h (frameHandle cf) pl (ppStmt sz stmt)
            stepStmt verb stmt rest


-- | Run a single step of the Crucible symbolic simulator.
--
--   'AbortExecReason' exceptions and 'UserError'
--   exceptions are NOT caught, and must be handled
--   by the calling context of 'singleStepCrucible'.
singleStepCrucible ::
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  Int {- ^ Current verbosity -} ->
  ExecState p sym ext rtp ->
  IO (ExecState p sym ext rtp)
singleStepCrucible verb exst =
  case exst of
    ResultState res ->
      return (ResultState res)

    AbortState rsn st ->
      let (AH handler) = st^.abortHandler in
      runReaderT (handler rsn) st

    OverrideState ovr st ->
      runReaderT (overrideHandler ovr) st

    ControlTransferState k tgt st ->
      runReaderT (performIntraFrameMerge k tgt) st

    RunningState st ->
      runReaderT (stepBasicBlock verb) st


-- | Given a 'SimState' and an execution continuation,
--   apply the continuation and execute the resulting
--   computation until completion.
--
--   This function is responsible for catching
--   'AbortExecReason' exceptions and 'UserError'
--   exceptions and invoking the 'errorHandler'
--   contained in the state.
executeCrucible :: forall p sym ext rtp f a.
  (IsSymInterface sym, IsSyntaxExtension ext) =>
  SimState p sym ext rtp f a {- ^ Initial simulator state -} ->
  ExecCont p sym ext rtp f a {- ^ Execution continuation to run -} ->
  IO (ExecResult p sym ext rtp)
executeCrucible st0 cont =
  do let cfg = stateGetConfiguration st0
     verbOpt <- getOptionSetting verbosity cfg
     loop verbOpt st0 cont

 where
 loop :: forall f' a'.
   OptionSetting BaseIntegerType ->
   SimState p sym ext rtp f' a' ->
   ExecCont p sym ext rtp f' a' ->
   IO (ExecResult p sym ext rtp)
 loop verbOpt st m =
   do exst <- Ex.catches (runReaderT m st)
                [ Ex.Handler $ \(e::AbortExecReason) ->
                    runErrorHandler e st
                , Ex.Handler $ \(e::Ex.IOException) ->
                    if Ex.isUserError e then
                      runGenericErrorHandler (Ex.ioeGetErrorString e) st
                    else
                      Ex.throwIO e
                ]
      case exst of
        ResultState res ->
          return res

        AbortState rsn st' ->
          let (AH handler) = st'^.abortHandler in
          loop verbOpt st' (handler rsn)

        OverrideState ovr st' ->
          loop verbOpt st' (overrideHandler ovr)

        ControlTransferState k tgt st' ->
          loop verbOpt st' (performIntraFrameMerge k tgt)

        RunningState st' ->
          do verb <- fromInteger <$> getOpt verbOpt
             loop verbOpt st' (stepBasicBlock verb)
