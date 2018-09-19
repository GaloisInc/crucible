{-# Language TypeFamilies #-}
{-# Language PatternSynonyms #-}
module Goal where

import Control.Lens((^.))
import Control.Monad(forM, forM_)
import Data.IORef
import qualified Data.Sequence as Seq


import What4.Interface (notPred, falsePred, Pred, printSymExpr,asConstantPred)
import What4.ProgramLoc
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check )
import What4.Protocol.SMTWriter(mkFormula,assumeFormula,smtExprGroundEvalFn)

import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, getSolverProcess )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)
import Lang.Crucible.Simulator.SimError

import Types
import Model
import Log
import ProgressBar


data ProofResult = Proved
                 | NotProved (Maybe ModelViews)   -- ^ Counter example, if any

type LPred sym   = LabeledPred (Pred sym)

data ProvedGoals =
    AtLoc ProgramLoc (Maybe ProgramLoc) ProvedGoals
  | Branch ProvedGoals ProvedGoals
  | Goal [(Maybe Int,AssumptionReason,String)]
         (SimError,String) Bool ProofResult
    -- ^ Keeps only the explanations for the relevant assumptions.
    -- The 'Maybe Int' in the assumptions corresponds to its depth in the tree
    -- (i.e., the step number, if this is a path assumption)
    -- The 'Bool' indicates if the goal is trivial (i.e., the assumptions
    -- are inconsistent)

-- | Simplify the proved goals.
provedGoalsTree ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver) fs
  , OnlineSolver s solver
  ) =>
  SimCtxt sym ->
  Maybe (Goals (Assumption sym) (Assertion sym, ProofResult)) ->
  IO (Maybe ProvedGoals)
provedGoalsTree ctxt = traverse (go [])
  where
  go asmps gs =
    case gs of
      Assuming ps gs1 -> goAsmp asmps ps gs1

      Prove (p,r) ->
        -- For simplicity we call `simpProved` even when the goal wasn't proved
        -- This shouldn't really matter, as we won't be able to simplify things
        do (as1,triv) <- simpProved ctxt asmps p
           return (Goal (map mkAsmp as1) (mkP p) triv r)

      ProveConj g1 g2 -> Branch <$> go asmps g1 <*> go asmps g2

  goAsmp asmps Seq.Empty gs = go asmps gs
  goAsmp asmps (ps Seq.:|> p) gs =
        case p ^. labeledPredMsg of
          ExploringAPath from to -> AtLoc from to <$> goAsmp (p : asmps) ps gs
          _                      -> goAsmp (p : asmps) ps gs

  mkAsmp (n,a) = let (x,y) = mkP a
                 in (n,x,y)

  mkP a = (a ^. labeledPredMsg, show (printSymExpr (a ^. labeledPred)))


countGoals :: Goals a b -> Int
countGoals gs =
  case gs of
    Assuming _ gs1  -> countGoals gs1
    Prove _         -> 1
    ProveConj g1 g2 -> countGoals g1 + countGoals g2


-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
proveGoals ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver) fs
  , OnlineSolver s solver
  ) =>
  SimCtxt sym ->
  Maybe (Goals (LPred sym asmp) (LPred sym ast)) ->
  IO (Maybe (Goals (LPred sym asmp) (LPred sym ast, ProofResult)))

proveGoals _ctxt Nothing =
  do -- sayOK "Crux" $ unwords [ "No goals to prove." ]
     return Nothing

proveGoals ctxt (Just gs0) =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     goalNum <- newIORef (0,0) -- total, proved
     res <- inNewFrame (solverConn sp) (go sp goalNum gs0)
     (tot,proved) <- readIORef goalNum
     if proved /= tot
       then sayFail "Crux" $ unwords
             [ "Failed to prove", show (tot - proved)
             , "out of", show tot, "side consitions." ]
       else sayOK "Crux" $ unwords [ "Proved all", show tot, "side conditions." ]
     return (Just res)
  where
  (start,end) = prepStatus "Checking: " (countGoals gs0)

  go sp gn gs =
    case gs of

      Assuming ps gs1 ->
        do forM_ ps $ \p ->
             assumeFormula conn =<< mkFormula conn (p ^. labeledPred)
           res <- go sp gn gs1
           return (Assuming ps res)

      Prove p ->
        do num <- atomicModifyIORef' gn (\(val,y) -> ((val + 1,y), val))
           start num
           let sym  = ctxt ^. ctxSymInterface
           assumeFormula conn =<< mkFormula conn
                              =<< notPred sym (p ^. labeledPred)
           res <- check sp "prove"
           let mkRes status = Prove (p,status)
           ret <- fmap mkRes $
                    case res of
                      Unsat   -> do modifyIORef' gn (\(x,f) -> (x,f+1))
                                    return Proved
                      Sat ()  ->
                        do f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           let model = ctxt ^. cruciblePersonality
                           str <- ppModel f model
                           return (NotProved (Just str))
                      Unknown -> return (NotProved Nothing)
           end
           return ret

      ProveConj g1 g2 ->
        do g1' <- inNewFrame conn (go sp gn g1)
           -- NB, we don't need 'inNewFrame' here because
           --  we don't need to back up to this point again.
           g2' <- go sp gn g2
           return (ProveConj g1' g2')

    where
    conn = solverConn sp


-- XXX: Factor out common with proveGoals
canProve ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver) fs
  , OnlineSolver s solver
  ) =>
  SimCtxt sym ->
  String ->
  [LPred sym asmp] ->
  Pred sym ->
  IO ProofResult
canProve ctxt rsn asmpPs concP =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     let conn = solverConn sp
     asmps <- forM asmpPs $ \a -> mkFormula conn (a ^. labeledPred)
     conc  <- mkFormula conn =<< notPred sym concP
     inNewFrame conn $
       do mapM_ (assumeFormula conn) asmps
          assumeFormula conn conc
          res <- check sp rsn
          return $ case res of
                     Unsat   -> Proved
                     _       -> NotProved Nothing


simpProved ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver) fs
  , OnlineSolver s solver
  ) =>
  SimCtxt sym ->
  [ Assumption sym ] ->
  Assertion sym ->
  IO ( [ (Maybe Int,Assumption sym) ], Bool )

simpProved ctxt asmps0 conc =
  do let false = falsePred (ctxt ^. ctxSymInterface)
     res <- canProve ctxt "context satisfiability" asmps0 false
     let (triv,g) = case res of
                      Proved -> (True,false)
                      _      -> (False,conc ^. labeledPred)

     conn  <- solverConn <$> getSolverProcess (ctxt ^. ctxSymInterface)
     asmps1 <- inNewFrame conn (dropAsmps conn 0 [] asmps0 g)
     return (asmps1, triv)
  where
  -- A simple way to figure out what might be relevant assumptions.
  dropAsmps conn n keep{-already assumed-} asmps{-to be filtered-} g =
    case asmps of
      [] -> return keep
      a : as ->
        let aP = a ^. labeledPred
            next = case a ^. labeledPredMsg of
                     ExploringAPath {} -> n+1
                     _                 -> n
        in case asConstantPred aP of
             Just True -> dropAsmps conn next keep as g
             _ ->
               do res <- canProve ctxt "assumption simplification" as g
                  case res of
                    Proved       -> dropAsmps conn next keep as g
                    NotProved {} ->
                       do assumeFormula conn =<< mkFormula conn aP
                          let lab = if n == next then Nothing else Just n
                          dropAsmps conn next ((lab,a) : keep) as g
