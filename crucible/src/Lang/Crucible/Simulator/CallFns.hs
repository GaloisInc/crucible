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
  ( callCFG
  , callFnVal
  , CrucibleState
  , loopCrucible
  , returnToOverride
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

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.Config
import           Lang.Crucible.Core
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.ProgramLoc
import           Lang.Crucible.Simulator.CallFrame
import           Lang.Crucible.Simulator.Evaluation
import           Lang.Crucible.Simulator.ExecutionTree
  hiding ( Frame
         , ReturnHandler
         , ReturnType
         )
import qualified Lang.Crucible.Simulator.ExecutionTree as Exec
import           Lang.Crucible.Simulator.MSSim
import           Lang.Crucible.Simulator.MatlabValue
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError
import           Lang.Crucible.Solver.Interface
import           Lang.Crucible.Solver.Partial
import           Lang.Crucible.Utils.MonadST
import           Lang.Crucible.Utils.StateContT

crucibleSimFrame :: Lens (SimFrame sym (CrucibleLang blocks r) ('Just args))
                         (SimFrame sym (CrucibleLang blocks r) ('Just args'))
                         (CallFrame sym blocks r args)
                         (CallFrame sym blocks r args')
crucibleSimFrame f (MF c) = MF <$> f c

crucibleTopFrame ::  Lens (TopFrame (SimState ctx sym) (CrucibleLang blocks r) ('Just args))
                          (TopFrame (SimState ctx sym) (CrucibleLang blocks r) ('Just args'))
                          (CallFrame sym blocks r args)
                          (CallFrame sym blocks r args')
crucibleTopFrame = gpValue . crucibleSimFrame

stateCrucibleFrame :: Lens (MSS_State sym rtp (CrucibleLang blocks r) ('Just a))
                           (MSS_State sym rtp (CrucibleLang blocks r) ('Just a'))
                           (CallFrame sym blocks r a)
                           (CallFrame sym blocks r a')
stateCrucibleFrame = simTree . actFrame . crucibleTopFrame
{-# INLINE stateCrucibleFrame #-}

------------------------------------------------------------------------
-- resolveCallFrame

data SomeSimFrame sym ret where
  SomeOF :: Override sym args ret
         -> OverrideFrame sym ret args
         -> SomeSimFrame sym ret
  SomeCF :: CallFrame sym blocks ret args
         -> SomeSimFrame sym ret

resolveCallFrame :: FunctionBindings sym
                 -> FnVal sym args ret
                 -> RegMap sym args
                 -> SomeSimFrame sym ret
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
type ExecReturn sym root l caller_args ret new_args
  =  ret
     -- ^ Value returned by solver.
  -> SimFrame sym l caller_args
     -- ^ Frame
  -> Exec.ReturnHandler (MSS_State sym) root l new_args

returnToCrucible :: TypeRepr ret
                 -> StmtSeq blocks r (ctx ::> ret)
                 -> ExecReturn sym
                               root
                               (CrucibleLang blocks r)
                               ('Just ctx)
                               (RegEntry sym ret)
                               ('Just (ctx ::> ret))
returnToCrucible ret stmts = \v (MF f) ->
  let f' = extendFrame ret (regValue v) stmts f
      c s = loopCrucible (s & simTree . actFrame . gpValue .~ MF f')
   in (MF f', c)

tailReturnToCrucible :: forall sym root blocks ctx r
                      . IsSymInterface sym
                     => ExecReturn sym
                               root
                               (CrucibleLang blocks r)
                               ctx
                               (RegEntry sym r)
                               'Nothing
tailReturnToCrucible = \v _ ->
  let c :: ExecCont (MSS_State sym) root (CrucibleLang blocks r) 'Nothing
      c s = case s^.simTree^.actFrame^.gpValue of
              RF v' -> returnAndMerge s v'
   in (RF v, c)

returnToOverride :: (ret -> ExecCont (MSS_State sym) rtp (OverrideLang args r) 'Nothing)
                    -- ^ Continuation to run next.
                 -> ExecReturn sym rtp (OverrideLang args r) 'Nothing ret 'Nothing
returnToOverride c = \v (OF o) -> (OF o, c v)

-- | Call a function with the given arguments.
callFnVal :: FnVal sym args ret
          -> RegMap sym args
          -> OverrideSim sym rtp a r (RegEntry sym ret)
callFnVal cl args = do
  Sim $ StateContT $ \c s -> do
    let bindings = s^.stateContext^.functionBindings
    case resolveCallFrame bindings cl args of
      SomeOF o f -> do
        overrideHandler o $ s & simTree %~ callFn (returnToOverride c) (OF f)
      SomeCF f -> do
        loopCrucible $ s & simTree %~ callFn (returnToOverride c) (MF f)

-- | Call a control flow graph from OverrideSim.
--
-- Note that this computes the postdominator information, so there is some
-- performance overhead in the call.
callCFG  :: CFG blocks init ret
         -> RegMap sym init
         -> OverrideSim sym rtp a r (RegEntry sym ret)
callCFG cfg args = do
  Sim $ StateContT $ \c s -> do
    let f = mkCallFrame cfg (postdomInfo cfg) args
    loopCrucible $ s & simTree %~ callFn (returnToOverride c) (MF f)

------------------------------------------------------------------------
-- CrucibleState

type CrucibleState sym rtp blocks ret args
   = CrucibleState' sym rtp blocks ret ('Just args)

type CrucibleState' sym rtp blocks ret args
   = MSS_State sym rtp (CrucibleLang blocks ret) args

evalLogFn :: CrucibleState sym rtp blocks r ctx
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
evalReg :: CrucibleState sym rtp blocks r ctx
        -> Reg ctx tp
        -> RegValue sym tp
evalReg s r = frameRegs (s^.stateCrucibleFrame) `regVal` r

-- | Evaluate an expression.
evalReg' :: CrucibleState sym rtp blocks r ctx
        -> Reg ctx tp
        -> RegEntry sym tp
evalReg' s r = frameRegs (s^.stateCrucibleFrame) `regVal'` r

-- | Evaluate an expression.
evalExpr :: forall sym ctx tp rtp blocks r
          . IsSymInterface sym
         => CrucibleState sym rtp blocks r ctx
         -> Expr ctx tp
         -> IO (RegValue sym tp)
evalExpr s (App a) = do
  let iteFns = ctxIntrinsicMuxFns (s^.stateContext)
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
               => CrucibleState sym rtp blocks r ctx
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
                  => CrucibleState sym rtp blocks r ctx
                  -> SwitchTarget blocks ctx tp
                  -> SwitchCall sym blocks tp
evalSwitchTarget s (SwitchTarget tgt _tp a) = do
  SwitchCall tgt (evalArgs s a)

checkStateConsistency :: CrucibleState sym rtp blocks r a
                      -> BlockID blocks args
                         -- ^ Current block of top of stack frame.
                      -> IO ()
checkStateConsistency s (BlockID block_id) = do
  let f = s^.stateCrucibleFrame
  case getIntraFrameBranchTarget (s^.simTree^.actContext) of
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

jumpToBlock :: IsSymInterface sym
             => CrucibleState sym rtp blocks r a
             -> BlockID blocks args
             -> RegMap sym args
             -> IO (SimResult sym rtp)
jumpToBlock s block_id args = do
  let s' = s & stateCrucibleFrame %~ setFrameBlock block_id args
  let cont s2 = checkStateConsistency s2 block_id >> loopCrucible s2
  let tgt = mkIntraProcedureMergePoint s' (text "jump") block_id
  checkForIntraFrameMerge cont tgt s'
{-# INLINE jumpToBlock #-}

-- | Jump to given block.
jump :: IsSymInterface sym
      => CrucibleState sym rtp blocks r args
      -> JumpTarget blocks args
      -> IO (SimResult sym rtp)
jump s (JumpTarget block_id _tp a) =
  jumpToBlock s block_id (evalArgs s a)

jumpToSwitchTarget :: (KnownRepr TypeRepr tp, IsSymInterface sym)
                   => CrucibleState sym rtp blocks r args
                   -> SwitchTarget blocks args tp
                   -> RegValue sym tp
                   -> IO (SimResult sym rtp)
jumpToSwitchTarget s (SwitchTarget tgt _tps a) v =
  jumpToBlock s tgt (assignReg knownRepr v (evalArgs s a))
{-# NOINLINE jumpToSwitchTarget #-}

-- | This is used to merge two call frames together at an post-dominator
callFrameIntraProcedureMergePoint
  :: IsSymInterface sym
     => MSS_State sym r l a
     -> CallFrame sym blocks ret args0
        -- ^ Current frame
     -> BlockID blocks args
        -- ^ Postdominator for block.
     -> IntraProcedureMergePoint (MSS_State sym)
                                 (CrucibleLang blocks ret)
                                 ('Just args)
callFrameIntraProcedureMergePoint s frame pd_id =
  let branch_loc = plSourceLoc (frameProgramLoc frame)
      merge_loc = plSourceLoc (blockLoc (frameBlockMap frame Ctx.! blockIDIndex pd_id))
      p  = text "branch:" <+> pretty branch_loc <$$>
           text "merge:"  <+> pretty merge_loc
   in mkIntraProcedureMergePoint s p pd_id

mkIntraProcedureMergePoint
  :: IsSymInterface sym
     => MSS_State sym r l a
     -> Doc
        -- ^ Name of frame.
     -> BlockID blocks args
        -- ^ Postdominator for block.
     -> IntraProcedureMergePoint (MSS_State sym)
                                 (CrucibleLang blocks ret)
                                 ('Just args)
mkIntraProcedureMergePoint s p pd_id =
  IntraProcedureMergePoint { mergePointName = p
                           , branchTarget = BlockTarget pd_id
                           , mergeFunctions = crucibleFrameFns s
                           , withFrameEquality = \x -> x
                           }

-- | This is used to merge two call frames together at function return
callFrameReturnMergePoint
  :: IsSymInterface sym
     => MSS_State sym r l a
     -> CallFrame sym blocks ret args0
        -- ^ Current frame
     -> IntraProcedureMergePoint (MSS_State sym)
                                 (CrucibleLang blocks ret)
                                 'Nothing
callFrameReturnMergePoint s frame =
  let branch_loc = plSourceLoc (frameProgramLoc frame)
      p  = text "branch:" <+> pretty branch_loc <$$>
           text "merge: Function return"
   in mkReturnMergePoint s p

-- | This is used to merge two call frames together
--   at the functionr return
mkReturnMergePoint
  :: IsSymInterface sym
     => MSS_State sym r l a
     -> Doc
        -- ^ Name of frame.
     -> IntraProcedureMergePoint (MSS_State sym)
                                 (CrucibleLang blocks ret)
                                 'Nothing

mkReturnMergePoint s p =
  IntraProcedureMergePoint { mergePointName = p
                           , branchTarget = ReturnTarget
                           , mergeFunctions = crucibleFrameFns s
                           , withFrameEquality = \x -> x
                           }

symbolicBranch
    :: IsSymInterface sym
    => CrucibleState sym rtp blocks ret ctx
    -> Int
    -> Pred sym
    -> BlockID blocks args
    -> RegMap sym args
    -> BlockID blocks args'
    -> RegMap sym args'
       -- ^ Registers for false state.
    -> IO (IO (SimResult sym rtp))
symbolicBranch s verb p x_id x_args y_id y_args = do
  let top_frame = s^.simTree^.actFrame

  let x_frame = top_frame & cruciblePausedFrame x_id x_args
  let y_frame = top_frame & cruciblePausedFrame y_id y_args

  let cur_frame = top_frame^.crucibleTopFrame
  let sym    = s^.stateContext^.ctxSymInterface
  let push_fn = cruciblePushFrame s
  case cur_frame^.framePostdom of
    Nothing -> do
      when (verb >= 5) $ do
        hPutStrLn (printHandle (s^.stateContext)) $ "Return-dominated symbolic branch"
      let mh = callFrameReturnMergePoint s cur_frame
      return $ intra_branch s push_fn p (Some . x_frame) (Some . y_frame) mh
    Just (Some pd_id)
      | Just Refl <- x_id `testEquality` pd_id -> do
        when (verb >= 5) $ do
          hPutStrLn (printHandle (s^.stateContext)) $ "First branch at postdom"
        let mh = callFrameIntraProcedureMergePoint s cur_frame pd_id
        pnot <- notPred sym p
        return $ completed_branch s push_fn pnot (Some . y_frame) x_frame mh
      | Just Refl <- y_id `testEquality` pd_id -> do
        when (verb >= 5) $ do
          hPutStrLn (printHandle (s^.stateContext)) $ "Second branch at postdom"
        let mh = callFrameIntraProcedureMergePoint s cur_frame pd_id
        return $ completed_branch s push_fn p    (Some . x_frame) y_frame mh
      | otherwise -> do
        when (verb >= 5) $ do
          hPutStrLn (printHandle (s^.stateContext)) $ "Neither branch at postdom"
        let mh = callFrameIntraProcedureMergePoint s cur_frame pd_id
        return $ intra_branch s push_fn p (Some . x_frame) (Some . y_frame) mh

data VariantCall sym blocks tp where
  VariantCall :: TypeRepr tp
              -> VariantBranch sym tp
              -> SwitchCall sym blocks tp
              -> VariantCall sym blocks tp

cruciblePausedFrame :: HasProgramLoc (SymPathState sym)
                    => BlockID b new_args
                    -> RegMap sym new_args
                    -> GlobalPair (MSS_State sym) (SimFrame sym (CrucibleLang b r) ('Just a))
                    -> SymPathState sym
                    -> Exec.PausedFrame (MSS_State sym)
                       rtp
                       (CrucibleLang b r)
                       ('Just new_args)
cruciblePausedFrame x_id x_args top_frame = \s ->
  let cf = top_frame & crucibleTopFrame %~ setFrameBlock x_id x_args
   in PausedFrame $
      PausedValue { _pausedValue = cf
                  , savedStateInfo  = s & setProgramLoc (frameProgramLoc (cf^.crucibleTopFrame))
                  , resume = \s2 -> checkStateConsistency s2 x_id >> loopCrucible s2
                  }

cruciblePushFrame :: MSS_State sym ret l a0
                  -> PushFrameFn (SimFrame sym (CrucibleLang b r))
cruciblePushFrame s =
  isSolverProof ctx $
    Exec.PushFrameFn $ \(MF x) -> do
      r' <- pushBranchRegs sym intrinsicFns (frameRegs x)
      return $! MF x{ frameRegs = r' }
  where ctx = s^.stateContext
        sym = ctx^.ctxSymInterface
        intrinsicFns = ctxIntrinsicMuxFns ctx


-- | Creates the frame functions for a frame.
crucibleFrameFns :: MSS_State sym r l a
                 -> Exec.PathValueFns (Pred sym) (SimFrame sym (CrucibleLang b r') a')
crucibleFrameFns s =
    isSolverProof ctx $
      Exec.PathValueFns
      { Exec.muxPathValue = \p x y ->
         case (x, y) of
          (MF x', MF y') -> MF <$> mergeCallFrame sym intrinsicFns p x' y'
          (RF x', RF y') -> RF <$> muxRegEntry sym intrinsicFns p x' y'
          _ -> error "internal error: Attempting to merge active frame with return frame"
      , Exec.popPathValue = \x ->
          case x of
            (MF x') -> do
               r' <- abortBranchRegs sym intrinsicFns (frameRegs x')
               return $! MF x'{ frameRegs = r' }
            (RF x') -> RF <$> abortBranchRegEntry sym intrinsicFns x'
      }
  where ctx = s^.stateContext
        sym = ctx^.ctxSymInterface
        intrinsicFns = ctxIntrinsicMuxFns ctx

stepReturnVariantCases
         :: forall sym rtp blocks r ctx
          . IsSymInterface sym
         => CrucibleState sym rtp blocks r ctx
         -> [(Pred sym, JumpCall sym blocks)]
         -> IO (IO (SimResult sym rtp))
stepReturnVariantCases s [] = do
  let top_frame = s^.simTree^.actFrame
  let loc = frameProgramLoc (top_frame^.crucibleTopFrame)
  let rsn = PatternMatchFailureSimError
  let err = SimError loc rsn
  return (abortExec err s)
stepReturnVariantCases s ((p,JumpCall x_id x_args):cs) = do
  let push_fn = cruciblePushFrame s
  let top_frame = s^.simTree^.actFrame
  let cur_frame = top_frame^.crucibleTopFrame

  let x_frame sym_state = Some $ cruciblePausedFrame x_id x_args top_frame sym_state
  let y_frame sym_state = Some $ PausedFrame $ PausedValue
                   { _pausedValue = top_frame
                   , savedStateInfo
                     = sym_state
                     & setProgramLoc (frameProgramLoc (top_frame^.crucibleTopFrame))
                   , resume = \s'' -> join $ stepReturnVariantCases s'' cs
                   }
  let mh = callFrameReturnMergePoint s cur_frame
  return $ intra_branch s push_fn p x_frame y_frame mh

stepVariantCases
         :: forall sym rtp blocks r ctx x
          . IsSymInterface sym
         => CrucibleState sym rtp blocks r ctx
         -> BlockID blocks x
         -> [(Pred sym, JumpCall sym blocks)]
         -> IO (IO (SimResult sym rtp))
stepVariantCases s _pd_id [] = do
  let top_frame = s^.simTree^.actFrame
  let loc = frameProgramLoc (top_frame^.crucibleTopFrame)
  let rsn = PatternMatchFailureSimError
  let err = SimError loc rsn
  return (abortExec err s)
stepVariantCases s pd_id ((p,JumpCall x_id x_args):cs) = do
  let top_frame = s^.simTree^.actFrame
  let cur_frame = top_frame^.crucibleTopFrame
  let sym = s^.stateContext^.ctxSymInterface

  let x_frame = top_frame & cruciblePausedFrame x_id x_args
  let y_frame s' = PausedValue
                   { _pausedValue = top_frame
                   , savedStateInfo = s' & setProgramLoc (frameProgramLoc (top_frame^.crucibleTopFrame))
                   , resume = \s'' -> join (stepVariantCases s'' pd_id cs)
                   }
  let y_frame' = Some . PausedFrame . y_frame
  let push_fn = cruciblePushFrame s
  case x_id `testEquality` pd_id of
    Just Refl -> do
      let mh = callFrameIntraProcedureMergePoint s cur_frame pd_id
      pnot <- notPred sym p
      return $ completed_branch s push_fn pnot y_frame' x_frame mh
    Nothing -> do
      let mh = callFrameIntraProcedureMergePoint s cur_frame pd_id
      return $ intra_branch s push_fn p (Some . x_frame) y_frame' mh

returnAndMerge :: forall sym rtp blocks r args
               . IsSymInterface sym
               => CrucibleState' sym rtp blocks r args
               -> RegEntry sym r
               -> IO (SimResult sym rtp)
returnAndMerge s arg = do
  let f' = RF arg
  let s' = s & simTree . actFrame . gpValue .~ f'
  let mp = mkReturnMergePoint s (text "return")
  let cont :: ExecCont (MSS_State sym) rtp (CrucibleLang b r) 'Nothing
      cont st = do
        case st^.simTree^.actFrame^.gpValue of
           RF v -> returnValue st v
  checkForIntraFrameMerge cont mp s'


{-# INLINABLE stepTerm #-}
stepTerm :: forall sym rtp blocks r ctx
          . IsSymInterface sym
         => CrucibleState sym rtp blocks r ctx
         -> Int  -- ^ Verbosity
         -> TermStmt blocks r ctx
         -> IO (IO (SimResult sym rtp))
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
  let cur_frame = s^.simTree^.actFrame^.crucibleTopFrame
  case cur_frame^.framePostdom of
    Nothing -> do
      stepReturnVariantCases s ls
    Just (Some pd_id) -> do
      stepVariantCases s pd_id ls
stepTerm s _ (MSwitchStmt e cases) = do
  case evalReg s e of
    RealArray a -> do
      return $! jumpToSwitchTarget s (matchRealArray cases) a
    IntArray a -> do
      return $! jumpToSwitchTarget s (matchIntArray cases) a
    UIntArray a -> do
      return $! jumpToSwitchTarget s (matchUIntArray cases) a
    LogicArray a -> do
      return $! jumpToSwitchTarget s (matchLogicArray cases) a
    CharArray a -> do
      return $! jumpToSwitchTarget s (matchCharArray cases) a
    CellArray a -> do
      return $! jumpToSwitchTarget s (matchCellArray cases) a
    MatlabStructArray a -> do
      return $! jumpToSwitchTarget s (matchStructArray cases) a
    FunctionHandle h -> do
      return $! jumpToSwitchTarget s (matchHandle cases) h
    SymLogicArray a -> do
      return $! jumpToSwitchTarget s (matchSymLogicArray cases) a
    SymRealArray a ->
      return $! jumpToSwitchTarget s (matchSymRealArray cases) a
    SymCplxArray a -> do
      return $! jumpToSwitchTarget s (matchSymCplxArray cases) a
    SymIntArray a -> do
      return $! jumpToSwitchTarget s (matchSymIntArray cases) a
    SymUIntArray a -> do
      return $! jumpToSwitchTarget s (matchSymUIntArray cases) a
    MatlabObjectArray a -> do
      return $! jumpToSwitchTarget s (matchObjectArray cases) a

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
      case replaceTailFrame (s^.simTree) (OF f) of
        Just t' -> do
          let s' = s & simTree .~ t'
          return $! overrideHandler o s'
        Nothing -> do
          let s' = s & simTree %~ callFn tailReturnToCrucible (OF f)
          return $! overrideHandler o s'
    SomeCF f ->
      case replaceTailFrame (s^.simTree) (MF f) of
        Just t' -> do
          let s' = s & simTree .~ t'
          return $! loopCrucible s'
        Nothing -> do
          let s' = s & simTree %~ callFn tailReturnToCrucible (MF f)
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

evalArgs :: forall sym rtp blocks r ctx args
           . CrucibleState sym rtp blocks r ctx
          -> Ctx.Assignment (Reg ctx) args
          -> RegMap sym args
evalArgs s args = evalArgs' (frameRegs (s^.stateCrucibleFrame)) args
{-# INLINE evalArgs #-}

-- | This continuation starts with a state with an active crucible frame
-- and runs it to completion.
--
-- It catches exceptions if a step throws an exception.
loopCrucible :: CrucibleState sym rtp blocks r ctx
             -> IO (SimResult sym rtp)
loopCrucible s = isSolverProof (s^.stateContext) $ do
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

data SomeState sym rtp where
  SomeState :: !(CrucibleState sym rtp blocks r ctx) -> SomeState sym rtp


continueCrucible :: IsSymInterface sym
                 => IORef (SomeState sym rtp)
                 -> Int
                 -> CrucibleState sym rtp blocks r ctx
                 -> IO (IO (SimResult sym rtp))
continueCrucible s_ref verb s = do
  writeIORef s_ref $! SomeState s
  loopCrucible' s_ref verb

-- | Internal loop for running the simulator.
--
-- This is allowed to throw user execeptions or SimError.
loopCrucible' :: IsSymInterface sym
              => IORef (SomeState sym rtp) -- ^ A reference to the current state value.
              -> Int -- ^ Current verbosity
              -> IO (IO (SimResult sym rtp))
loopCrucible' s_ref verb = do
  SomeState s <- readIORef s_ref
  let ctx = s^.stateContext
  let sym = ctx^.ctxSymInterface
  let top_frame = s^.simTree^.actFrame
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
            s & simTree . actFrame . gpGlobals %~ insertRef r v
              & stateCrucibleFrame %~ extendFrame (ReferenceRepr tpr) r rest
        ReadRefCell x -> do
          let ref = evalReg s x
          case lookupRef ref (s^.simTree^.actFrame^.gpGlobals) of
            Just v ->
              continueCrucible s_ref verb $
                s & stateCrucibleFrame %~ extendFrame (refType ref) v rest
            Nothing ->
              fail "Attempted to read undefined reference cell"
        WriteRefCell x y -> do
          let ref = evalReg s x
          let v   = evalReg s y
          continueCrucible s_ref verb $
            s & simTree . actFrame . gpGlobals %~ insertRef ref v
              & stateCrucibleFrame  . frameStmts .~ rest
        ReadGlobal global_var -> do
          case lookupGlobal global_var (top_frame^.gpGlobals) of
            Nothing -> fail $ "Attempt to read undefined global " ++ show global_var
            Just v ->
              continueCrucible s_ref verb $
                s & stateCrucibleFrame %~ extendFrame (globalType global_var) v rest
        WriteGlobal global_var local_reg -> do
          let updateFrame f = f & crucibleTopFrame . frameStmts .~ rest
                                & gpGlobals %~ insertGlobal global_var (evalReg s local_reg)
          continueCrucible s_ref verb $
            s & simTree . actFrame %~ updateFrame
        SetReg tp e -> do
          v <- evalExpr s e
          continueCrucible s_ref verb $ s & stateCrucibleFrame %~ extendFrame tp v rest
        CallHandle ret_type fnExpr _types arg_exprs -> do
          let hndl = evalReg s fnExpr
          let args = evalArgs s arg_exprs
          let bindings = s^.stateContext^.functionBindings
          case resolveCallFrame bindings hndl args of
            SomeOF o f -> do
              let s' = s & simTree %~ callFn (returnToCrucible ret_type rest) (OF f)
              return $ overrideHandler o $ s'
            SomeCF f -> do
              let s' = s & simTree %~ callFn (returnToCrucible ret_type rest) (MF f)
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
