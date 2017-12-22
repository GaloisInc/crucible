-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.Simulator.CallFns
-- Description      : Provides functions for calling functions and Crucible CFGs.
-- Copyright        : (c) Galois, Inc 2013-2015
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides functions for calling overrides and Crucible CFGS.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Lang.Crucible.Simulator.CallFns
  ( CrucibleState
  , loopCrucible
  , returnToOverride
  , SomeSimFrame(..)
  , resolveCallFrame
  ) where

import           Control.Exception
import           Control.Lens
import           Control.Monad.State
import           Data.IORef
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import qualified Data.Text as Text
import           System.IO
import           System.IO.Error
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Lang.Crucible.Config
import           Lang.Crucible.CFG.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.ExecutionTree
  hiding ( ReturnHandler
         )
import qualified Lang.Crucible.Simulator.ExecutionTree as Exec
import           Lang.Crucible.Simulator.Frame
import           Lang.Crucible.Simulator.GlobalState
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Utils.MonadST

crucibleSimFrame :: Lens (SimFrame sym (CrucibleLang blocks r) ('Just args))
                         (SimFrame sym (CrucibleLang blocks r) ('Just args'))
                         (CallFrame sym blocks r args)
                         (CallFrame sym blocks r args')
crucibleSimFrame f (MF c) = MF <$> f c

crucibleTopFrame ::  Lens (TopFrame sym (CrucibleLang blocks r) ('Just args))
                          (TopFrame sym (CrucibleLang blocks r) ('Just args'))
                          (CallFrame sym blocks r args)
                          (CallFrame sym blocks r args')
crucibleTopFrame = gpValue . crucibleSimFrame

stateCrucibleFrame :: Lens (SimState p sym rtp (CrucibleLang blocks r) ('Just a))
                           (SimState p sym rtp (CrucibleLang blocks r) ('Just a'))
                           (CallFrame sym blocks r a)
                           (CallFrame sym blocks r a')
stateCrucibleFrame = stateTree . actFrame . crucibleTopFrame
{-# INLINE stateCrucibleFrame #-}

------------------------------------------------------------------------
-- resolveCallFrame

data SomeSimFrame p sym ret where
  SomeOF :: Override p sym args ret
         -> OverrideFrame sym ret args
         -> SomeSimFrame p sym ret
  SomeCF :: CallFrame sym blocks ret args
         -> SomeSimFrame p sym ret

resolveCallFrame :: FunctionBindings p sym
                 -> FnVal sym args ret
                 -> RegMap sym args
                 -> SomeSimFrame p sym ret
resolveCallFrame bindings c0 args =
  case c0 of
    ClosureFnVal c tp v -> do
      resolveCallFrame bindings c (assignReg tp v args)
    HandleFnVal h -> do
      case lookupHandleMap h bindings of
        Nothing -> throw . userError $
          "Could not resolve function: " ++ show (handleName h)
        Just (UseOverride o) -> do
          let f = OverrideFrame { override = overrideName o
                                , overrideRegMap = args
                                }
           in SomeOF o f
        Just (UseCFG g pdInfo) -> do
          SomeCF (mkCallFrame g pdInfo args)

------------------------------------------------------------------------
-- callFromAny

-- | Call back function returning from a call.
type ExecReturn p sym root l caller_args ret new_args
  =  ret
     -- ^ Value returned by solver.
  -> SimFrame sym l caller_args
     -- ^ Frame
  -> Exec.ReturnHandler p sym root l new_args

returnToCrucible :: TypeRepr ret
                 -> StmtSeq blocks r (ctx ::> ret)
                 -> ExecReturn p sym
                               root
                               (CrucibleLang blocks r)
                               ('Just ctx)
                               (RegEntry sym ret)
                               ('Just (ctx ::> ret))
returnToCrucible ret stmts = \v (MF f) ->
  let f' = extendFrame ret (regValue v) stmts f
      c s = loopCrucible (s & stateTree . actFrame . gpValue .~ MF f')
   in (MF f', c)

tailReturnToCrucible :: forall p sym root blocks ctx r
                      . IsSymInterface sym
                     => ExecReturn p sym
                               root
                               (CrucibleLang blocks r)
                               ctx
                               (RegEntry sym r)
                               'Nothing
tailReturnToCrucible = \v _ ->
  let c :: ExecCont p sym root (CrucibleLang blocks r) 'Nothing
      c s = case s^.stateTree^.actFrame^.gpValue of
              RF v' -> returnAndMerge s v'
   in (RF v, c)

returnToOverride :: (ret -> ExecCont p sym rtp (OverrideLang args r) 'Nothing)
                    -- ^ Continuation to run next.
                 -> ExecReturn p sym rtp (OverrideLang args r) 'Nothing ret 'Nothing
returnToOverride c = \v (OF o) -> (OF o, c v)


------------------------------------------------------------------------
-- CrucibleState

type CrucibleState p sym rtp blocks ret args
   = SimState p sym rtp (CrucibleLang blocks ret) ('Just args)

evalLogFn :: CrucibleState p sym rtp blocks r ctx
          -> Int
          -> String
          -> IO ()
evalLogFn s n msg = do
  let h = printHandle (s^.stateContext)
  let cfg = simConfig (s^.stateContext)
  verb <- getConfigValue verbosity cfg
  when (verb >= n) $ do
    hPutStr h msg
    hFlush h

-- | Evaluate an expression.
evalReg :: CrucibleState p sym rtp blocks r ctx
        -> Reg ctx tp
        -> RegValue sym tp
evalReg s r = frameRegs (s^.stateCrucibleFrame) `regVal` r

-- | Evaluate an expression.
evalReg' :: CrucibleState p sym rtp blocks r ctx
        -> Reg ctx tp
        -> RegEntry sym tp
evalReg' s r = frameRegs (s^.stateCrucibleFrame) `regVal'` r

-- | Evaluate an expression.
evalExpr :: forall p sym ctx tp rtp blocks r
          . IsSymInterface sym
         => CrucibleState p sym rtp blocks r ctx
         -> Expr ctx tp
         -> IO (RegValue sym tp)
evalExpr s (App a) = do
  let iteFns = stateIntrinsicTypes s
  r <- evalApp (stateSymInterface s) iteFns (evalLogFn s) (\r -> return $ evalReg s r) a
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

evalJumpTarget :: IsSymInterface sym
               => CrucibleState p sym rtp blocks r ctx
               -> JumpTarget blocks ctx
               -> JumpCall sym blocks
evalJumpTarget s (JumpTarget tgt _ a) = JumpCall tgt (evalArgs s a)

------------------------------------------------------------------------
-- SwitchCall

data SwitchCall sym blocks tp where
  SwitchCall :: !(BlockID blocks (args ::> tp))
             -> !(RegMap sym args)
             -> SwitchCall sym blocks tp

evalSwitchTarget :: IsSymInterface sym
                  => CrucibleState p sym rtp blocks r ctx
                  -> SwitchTarget blocks ctx tp
                  -> SwitchCall sym blocks tp
evalSwitchTarget s (SwitchTarget tgt _tp a) = do
  SwitchCall tgt (evalArgs s a)

{-
checkStateConsistency :: CrucibleState p sym rtp blocks r a
                      -> BlockID blocks args
                         -- ^ Current block of top of stack frame.
                      -> IO ()
checkStateConsistency s (BlockID block_id) = do
  let f = s^.stateCrucibleFrame
  case getIntraFrameBranchTarget (s^.stateTree^.actContext) of
    Nothing -> return ()
    Just (Some tgt) -> do
      let ConstK _pd = framePostdomMap f Ctx.! block_id
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

-- | Jump to given block.
--
-- May throw a user error if merging fails.
jump :: IsSymInterface sym
      => CrucibleState p sym rtp blocks r args
      -> JumpTarget blocks args
      -> IO (ExecResult p sym rtp)
jump s (JumpTarget block_id _tp a) =
  jumpToBlock s block_id (evalArgs s a)


symbolicBranch
    :: IsSymInterface sym
    => CrucibleState p sym rtp blocks ret ctx
    -> Int
    -> Pred sym
    -> BlockID blocks args
    -> RegMap sym args
    -> BlockID blocks args'
    -> RegMap sym args'
       -- ^ Registers for false state.
    -> IO (IO (ExecResult p sym rtp))
symbolicBranch s verb p x_id x_args y_id y_args = do
  let top_frame = s^.stateTree^.actFrame

  let x_frame = cruciblePausedFrame x_id x_args top_frame
  let y_frame = cruciblePausedFrame y_id y_args top_frame

  let cur_frame = top_frame^.crucibleTopFrame
  case cur_frame^.framePostdom of
    Nothing -> do
      when (verb >= 5) $ do
        hPutStrLn (printHandle (s^.stateContext)) $ "Return-dominated symbolic branch"
      return $ intra_branch s p (\sps -> SomeLabel (x_frame sps) (Just x_id))
                                (\sps -> SomeLabel (y_frame sps) (Just y_id))
                                ReturnTarget
    Just (Some pd_id) ->
      let tgt = BlockTarget pd_id
      in return $ intra_branch s p (\sps -> SomeLabel (x_frame sps) (Just x_id))
                                   (\sps -> SomeLabel (y_frame sps) (Just y_id))
                                   tgt

data VariantCall sym blocks tp where
  VariantCall :: TypeRepr tp
              -> VariantBranch sym tp
              -> SwitchCall sym blocks tp
              -> VariantCall sym blocks tp

cruciblePausedFrame :: HasProgramLoc (SymPathState sym)
                    => BlockID b new_args
                    -> RegMap sym new_args
                    -> GlobalPair sym (SimFrame sym (CrucibleLang b r) ('Just a))
                    -> SymPathState sym
                    -> Exec.PausedFrame p sym
                       rtp
                       (CrucibleLang b r)
                       ('Just new_args)
cruciblePausedFrame x_id x_args top_frame s =
  let cf = top_frame & crucibleTopFrame %~ setFrameBlock x_id x_args
   in PausedFrame $
      PausedValue { _pausedValue = cf
                  , savedStateInfo  = s & programLoc .~ frameProgramLoc (cf^.crucibleTopFrame)
                  , resume = loopCrucible
                  }

stepReturnVariantCases
         :: forall p sym rtp blocks r ctx
          . IsSymInterface sym
         => CrucibleState p sym rtp blocks r ctx
         -> [(Pred sym, JumpCall sym blocks)]
         -> IO (IO (ExecResult p sym rtp))
stepReturnVariantCases s [] = do
  let top_frame = s^.stateTree^.actFrame
  let loc = frameProgramLoc (top_frame^.crucibleTopFrame)
  let rsn = PatternMatchFailureSimError
  let err = SimError loc rsn
  return (abortExec err s)
stepReturnVariantCases s ((p,JumpCall x_id x_args):cs) = do
  let top_frame = s^.stateTree^.actFrame
  let x_frame = cruciblePausedFrame x_id x_args top_frame
  let y_frame sym_state =
        SomeLabel (PausedFrame $ PausedValue
                     { _pausedValue = top_frame
                     , savedStateInfo
                       = sym_state
                       & programLoc .~ frameProgramLoc (top_frame^.crucibleTopFrame)
                     , resume = \s'' -> join $ stepReturnVariantCases s'' cs
                     })
                  Nothing
  return $ intra_branch s p (\sps -> SomeLabel (x_frame sps) (Just x_id)) y_frame ReturnTarget

stepVariantCases
         :: forall p sym rtp blocks r ctx x
          . IsSymInterface sym
         => CrucibleState p sym rtp blocks r ctx
         -> BlockID blocks x
         -> [(Pred sym, JumpCall sym blocks)]
         -> IO (IO (ExecResult p sym rtp))
stepVariantCases s _pd_id [] = do
  let top_frame = s^.stateTree^.actFrame
  let loc = frameProgramLoc (top_frame^.crucibleTopFrame)
  let rsn = PatternMatchFailureSimError
  let err = SimError loc rsn
  return (abortExec err s)
stepVariantCases s pd_id ((p,JumpCall x_id x_args):cs) = do
  let top_frame = s^.stateTree^.actFrame
  let x_frame = cruciblePausedFrame x_id x_args top_frame
  let y_frame s' = PausedValue
                   { _pausedValue = top_frame
                   , savedStateInfo =
                       s' & programLoc .~ frameProgramLoc (top_frame^.crucibleTopFrame)
                   , resume = \s'' -> join (stepVariantCases s'' pd_id cs)
                   }
  let y_frame' sym_state = SomeLabel (PausedFrame (y_frame sym_state)) Nothing
  let tgt = BlockTarget pd_id
  return $ intra_branch s p (\sps -> SomeLabel (x_frame sps) (Just x_id)) y_frame' tgt

returnAndMerge :: forall p sym rtp blocks r args
               .  IsSymInterface sym
               => SimState p sym rtp (CrucibleLang blocks r) args
               -> RegEntry sym r
               -> IO (ExecResult p sym rtp)
returnAndMerge s arg = do
  let s' = s & stateTree . actFrame . gpValue .~ RF arg
  let cont :: ExecCont p sym rtp (CrucibleLang b r) 'Nothing
      cont st = do
        case st^.stateTree^.actFrame^.gpValue of
           RF v -> returnValue st v
  checkForIntraFrameMerge cont ReturnTarget s'

{-# INLINABLE stepTerm #-}
stepTerm :: forall p sym rtp blocks r ctx
          . IsSymInterface sym
         => CrucibleState p sym rtp blocks r ctx
         -> Int  -- ^ Verbosity
         -> TermStmt blocks r ctx
         -> IO (IO (ExecResult p sym rtp))
stepTerm s _ (Jump tgt) = do
  return $! jump s tgt
stepTerm s verb (Br c x y)
  | JumpCall x_id x_args <- evalJumpTarget s x
  , JumpCall y_id y_args <- evalJumpTarget s y = do

  let p = evalReg s c
  symbolicBranch s verb p x_id x_args y_id y_args

stepTerm s verb (MaybeBranch tp e j n) = do
  case evalReg s e of
    Unassigned -> do
      return $! jump s n
    PE p v | SwitchCall j_tgt j_args0 <- evalSwitchTarget s j
           , JumpCall   n_tgt n_args  <- evalJumpTarget   s n -> do

      let j_args = assignReg tp v j_args0
      symbolicBranch s verb p j_tgt j_args n_tgt n_args

stepTerm s _ (VariantElim ctx e cases) = do
  let vs = evalReg s e
  let cases' = Ctx.generate (Ctx.size ctx) (\i ->
                   VariantCall (ctx Ctx.! i)
                               (vs Ctx.! i)
                               (evalSwitchTarget s (cases Ctx.! i)))
  let ls = foldMapFC (\(VariantCall tp (VB v) (SwitchCall tgt regs)) ->
              case v of
                Unassigned -> []
                PE p v' -> [(p, JumpCall tgt (assignReg tp v' regs))])
            cases'
  let cur_frame = s^.stateTree^.actFrame^.crucibleTopFrame
  case cur_frame^.framePostdom of
    Nothing -> do
      stepReturnVariantCases s ls
    Just (Some pd_id) -> do
      stepVariantCases s pd_id ls

stepTerm s _ (Return arg) = do
  return $! returnAndMerge s (evalReg' s arg)

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

stepTerm s _ (TailCall fnExpr _types arg_exprs) = do
  let cl   = evalReg s fnExpr
  let args = evalArgs s arg_exprs
  let bindings = s^.stateContext^.functionBindings
  case resolveCallFrame bindings cl args of
    SomeOF o f ->
      case replaceTailFrame (s^.stateTree) (OF f) of
        Just t' -> do
          let s' = s & stateTree .~ t'
          return $! overrideHandler o s'
        Nothing -> do
          let s' = s & stateTree %~ callFn tailReturnToCrucible (OF f)
          return $! overrideHandler o s'
    SomeCF f ->
      case replaceTailFrame (s^.stateTree) (MF f) of
        Just t' -> do
          let s' = s & stateTree .~ t'
          return $! loopCrucible s'
        Nothing -> do
          let s' = s & stateTree %~ callFn tailReturnToCrucible (MF f)
          return $! loopCrucible s'

stepTerm s _ (ErrorStmt msg) = do
  fail (Text.unpack (evalReg s msg))

evalArgs' :: forall sym ctx args
           . RegMap sym ctx
          -> Ctx.Assignment (Reg ctx) args
          -> RegMap sym args
evalArgs' m0 args = RegMap (fmapFC (getEntry m0) args)
  where getEntry :: RegMap sym ctx -> Reg ctx tp -> RegEntry sym tp
        getEntry (RegMap m) r = m Ctx.! regIndex r
{-# NOINLINE evalArgs' #-}

evalArgs :: forall p sym rtp blocks r ctx args
           . CrucibleState p sym rtp blocks r ctx
          -> Ctx.Assignment (Reg ctx) args
          -> RegMap sym args
evalArgs s args = evalArgs' (frameRegs (s^.stateCrucibleFrame)) args
{-# INLINE evalArgs #-}

-- | This continuation starts with a state with an active crucible frame
-- and runs it to completion.
--
-- It catches exceptions if a step throws an exception.
loopCrucible :: CrucibleState p sym rtp blocks r ctx
             -> IO (ExecResult p sym rtp)
loopCrucible s = stateSolverProof s $ do
  s_ref <- newIORef (SomeState s)
  let cfg = simConfig (s^.stateContext)
  verb <- getConfigValue verbosity cfg
  next <- catches (loopCrucible' s_ref verb)
     [ Handler $ \(e::IOException) -> do
          SomeState s' <- readIORef s_ref
          if isUserError e then
            return $ mssRunGenericErrorHandler s' (ioeGetErrorString e)
           else
            throwIO e
     , Handler $ \(e::SimError) -> do
          SomeState s' <- readIORef s_ref
          return $  mssRunErrorHandler s' e
     ]
  next

data SomeState p sym rtp where
  SomeState :: !(CrucibleState p sym rtp blocks r ctx) -> SomeState p sym rtp


continueCrucible :: IsSymInterface sym
                 => IORef (SomeState p sym rtp)
                 -> Int
                 -> CrucibleState p sym rtp blocks r ctx
                 -> IO (IO (ExecResult p sym rtp))
continueCrucible s_ref verb s = do
  writeIORef s_ref $! SomeState s
  loopCrucible' s_ref verb

-- | Internal loop for running the simulator.
--
-- This is allowed to throw user execeptions or SimError.
loopCrucible' :: IsSymInterface sym
              => IORef (SomeState p sym rtp) -- ^ A reference to the current state value.
              -> Int -- ^ Current verbosity
              -> IO (IO (ExecResult p sym rtp))
loopCrucible' s_ref verb = do
  SomeState s <- readIORef s_ref
  let ctx = s^.stateContext
  let sym = ctx^.ctxSymInterface
  let top_frame = s^.stateTree^.actFrame
  let cf = top_frame^.crucibleTopFrame
  let h = printHandle ctx
  case cf^.frameStmts of
    TermStmt pl stmt -> do
      setCurrentProgramLoc sym pl
      when (verb >= 4) $ do
        ppStmtAndLoc h (frameHandle cf) pl (pretty stmt)
      stepTerm s verb stmt

    ConsStmt pl stmt rest -> do
      setCurrentProgramLoc sym pl
      when (verb >= 4) $ do
        let sz = regMapSize (frameRegs cf)
        ppStmtAndLoc h (frameHandle cf) pl (ppStmt sz stmt)
      case stmt of
        NewRefCell tpr x -> do
          let halloc = simHandleAllocator ctx
          let v = evalReg s x
          r <- liftST (freshRefCell halloc tpr)
          continueCrucible s_ref verb $
            s & stateTree . actFrame . gpGlobals %~ insertRef sym r v
              & stateCrucibleFrame %~ extendFrame (ReferenceRepr tpr) r rest
        NewEmptyRefCell tpr -> do
          let halloc = simHandleAllocator ctx
          r <- liftST (freshRefCell halloc tpr)
          continueCrucible s_ref verb $
            s & stateCrucibleFrame %~ extendFrame (ReferenceRepr tpr) r rest
        ReadRefCell x -> do
          let ref = evalReg s x
          let msg = ReadBeforeWriteSimError "Attempted to read uninitialized reference cell"
          v <- readPartExpr sym (lookupRef ref (s^.stateTree^.actFrame^.gpGlobals)) msg
          continueCrucible s_ref verb $
             s & stateCrucibleFrame %~ extendFrame (refType ref) v rest
        WriteRefCell x y -> do
          let ref = evalReg s x
          let v   = evalReg s y
          continueCrucible s_ref verb $
            s & stateTree . actFrame . gpGlobals %~ insertRef sym ref v
              & stateCrucibleFrame  . frameStmts .~ rest
        DropRefCell x -> do
          let ref = evalReg s x
          continueCrucible s_ref verb $
            s & stateTree . actFrame . gpGlobals %~ dropRef ref
              & stateCrucibleFrame  . frameStmts .~ rest
        ReadGlobal global_var -> do
          case lookupGlobal global_var (top_frame^.gpGlobals) of
            Nothing ->
              do let msg = ReadBeforeWriteSimError $ "Attempt to read undefined global " ++ show global_var
                 addFailedAssertion sym msg
            Just v ->
              continueCrucible s_ref verb $
                s & stateCrucibleFrame %~ extendFrame (globalType global_var) v rest
        WriteGlobal global_var local_reg -> do
          let updateFrame f = f & crucibleTopFrame . frameStmts .~ rest
                                & gpGlobals %~ insertGlobal global_var (evalReg s local_reg)
          continueCrucible s_ref verb $
            s & stateTree . actFrame %~ updateFrame
        SetReg tp e -> do
          v <- evalExpr s e
          continueCrucible s_ref verb $ s & stateCrucibleFrame %~ extendFrame tp v rest
        CallHandle ret_type fnExpr _types arg_exprs -> do
          let hndl = evalReg s fnExpr
          let args = evalArgs s arg_exprs
          let bindings = s^.stateContext^.functionBindings
          case resolveCallFrame bindings hndl args of
            SomeOF o f -> do
              let s' = s & stateTree %~ callFn (returnToCrucible ret_type rest) (OF f)
              return $ overrideHandler o $ s'
            SomeCF f -> do
              let s' = s & stateTree %~ callFn (returnToCrucible ret_type rest) (MF f)
              continueCrucible s_ref verb $ s'
        Print e -> do
          let msg = evalReg s e
          hPutStr h (Text.unpack msg)
          hFlush h
          continueCrucible s_ref verb $ s & stateCrucibleFrame  . frameStmts .~ rest
        Assert c_expr msg_expr -> do
          let c = evalReg s c_expr
          let m = evalReg s msg_expr
          addAssertion sym c (AssertFailureSimError (Text.unpack m))
          continueCrucible s_ref verb $ s & stateCrucibleFrame  . frameStmts .~ rest

jumpToBlock :: IsSymInterface sym
             => SimState p sym rtp (CrucibleLang blocks r) ('Just a)
             -> BlockID blocks args
             -> RegMap sym args
             -> IO (ExecResult p sym rtp)
jumpToBlock s block_id args = do
  let s' = s & stateCrucibleFrame %~ setFrameBlock block_id args
  let cont s2 = loopCrucible s2
  checkForIntraFrameMerge cont (BlockTarget block_id) s'
{-# INLINE jumpToBlock #-}
