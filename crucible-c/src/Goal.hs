{-# Language TypeFamilies #-}
{-# Language PatternSynonyms #-}
module Goal where

import Control.Lens((^.), (&), (.~))
import Control.Monad(forM)
import qualified Data.Sequence as Seq
import Data.IORef

import What4.Interface (notPred, falsePred)
import What4.ProgramLoc
import What4.SatResult(SatResult(..))
import What4.Expr.Builder (ExprBuilder)
import What4.Protocol.Online( OnlineSolver, inNewFrame, solverEvalFuns
                            , solverConn, check, SolverProcess )
import What4.Protocol.SMTWriter(mkFormula,assumeFormula,smtExprGroundEvalFn)

import Lang.Crucible.Backend
import Lang.Crucible.Backend.Online
        ( OnlineBackendState, getSolverProcess )
import Lang.Crucible.Simulator.ExecutionTree
        (ctxSymInterface, cruciblePersonality)
import Lang.Crucible.Simulator.SimError

import Types
import Model
import ProgressBar


data ProofResult = Proved
                 | NotProved (Maybe ModelViews)   -- ^ Counter example, if any

type BranchPoint = (ProgramLoc, Maybe ProgramLoc)
type Path        = [ BranchPoint ]


data ProvedGoals =
    AtLoc ProgramLoc (Maybe ProgramLoc) ProvedGoals
  | Branch [ ProvedGoals ]
  | Goal [AssumptionReason] SimError Bool ProofResult
    -- ^ Keeps only the explanations for the relevant assumptions.
    -- The 'Bool' indicates if the goal is trivial (i.e., the assumptions
    -- are inconsistent)


-- | Simplify the proved goals.
provedGoalsTree ::
 ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
  Goals (Assumption sym) (Assertion sym, ProofResult) ->
  IO ProvedGoals
provedGoalsTree ctxt = go []
  where
  go asmps gs =
    case gs of
      Assuming p gs1 ->
        case p ^. labeledPredMsg of
          ExploringAPath from to -> AtLoc from to <$> go (p : asmps) gs1
          _                      -> go (p : asmps) gs1
      Prove (p,r)  ->
        case r of
          Proved ->
            do (as1,triv) <- simpProved' ctxt ProofGoal
                                   { proofAssumptions = Seq.fromList asmps
                                   , proofGoal        = p
                                   }
               return (Goal (map (^. labeledPredMsg) as1)
                             (p ^. labeledPredMsg)
                             triv
                             Proved)

          _ -> return (Goal (map (^. labeledPredMsg) asmps)
                            (p ^. labeledPredMsg)
                            False
                            r)

      ProveAll gss -> Branch <$> mapM (go asmps) gss


countGoals :: Goals a b -> Int
countGoals gs =
  case gs of
    Assuming _ gs1 -> countGoals gs1
    Prove _        -> 1
    ProveAll gs1   -> sum (map countGoals gs1)




addLoopMarkers = go Map.empty
  where
  go mp gs = case gs of
               Assuming p ->
                 case p ^. labeledPredMsg of
                   ExploringAPath p _ ->
                     let mp1 = Map.insertWith (+) p 1 mp
                         cnt = mp1 Map.! p
                      in undefined
               Prove p -> Prove p
               ProveAll gss -> ProveAll (map (go mp) gss)



-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
proveGoals ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
  ProofObligations sym ->
  IO (Goals (Assumption sym) (Assertion sym, ProofResult))

proveGoals ctxt gs0 =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     goalNum <- newIORef 1
     go sp goalNum gs0
  where
  (start,end) = prepStatus "Proving: " (countGoals gs0)

  go sp gn gs =
    case gs of

      Assuming p gs1 ->
        do assumeFormula conn =<< mkFormula conn (p ^. labeledPred)
           res <- go sp gn gs1
           return (Assuming p res)

      Prove p ->
        do num <- atomicModifyIORef' gn (\val -> (val + 1, val))
           start num
           let sym  = ctxt ^. ctxSymInterface
           assumeFormula conn =<< mkFormula conn
                              =<< notPred sym (p ^. labeledPred)
           res <- check sp
           let mkRes status = Prove (p,status)
           ret <- fmap mkRes $
                    case res of
                      Unsat   -> return Proved
                      Sat ()  ->
                        do f <- smtExprGroundEvalFn conn (solverEvalFuns sp)
                           let model = ctxt ^. cruciblePersonality
                           str <- ppModel f model
                           return (NotProved (Just str))
                      Unknown -> return (NotProved Nothing)
           end
           return ret

      ProveAll xs ->
        do ys <- mapM (inNewFrame conn . go sp gn) xs
           return (ProveAll ys)

    where
    conn = solverConn sp


proveGoal ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO ProofResult

proveGoal ctxt g = proveGoal' ctxt g $ \sp ->
  do f <- smtExprGroundEvalFn (solverConn sp) (solverEvalFuns sp)
     let model = ctxt ^. cruciblePersonality
     str <- ppModel f model
     return (Just str)


canProve ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO ProofResult

canProve ctxt g = proveGoal' ctxt g $ \_sp -> return Nothing


proveGoal' ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
  ProofObligation sym ->
  (SolverProcess s solver -> IO (Maybe ModelViews)) ->
  IO ProofResult
proveGoal' ctxt g isSat =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     let conn = solverConn sp
     asmps <- forM (proofAssumptions g) $ \a ->
                 mkFormula conn (a ^. labeledPred)
     conc  <- mkFormula conn =<< notPred sym (proofGoal g ^. labeledPred)
     inNewFrame conn $
       do mapM_ (assumeFormula conn) asmps
          assumeFormula conn conc
          res <- check sp
          case res of
            Unsat  -> return Proved
            Sat () -> NotProved <$> isSat sp
            Unknown -> return (NotProved Nothing)


data SimpResult sym =
    Trivial
  | NotTrivial (ProofObligation sym)


simpProved ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO (SimpResult sym)
simpProved ctxt goal =
  do let false = falsePred (ctxt ^. ctxSymInterface)
         g1 = goal { proofGoal = (proofGoal goal) & labeledPred .~ false }
     res <- canProve ctxt g1
     case res of
       Proved -> return Trivial -- we should still minimize the asmps
       _      -> dropAsmps Seq.empty (proofAssumptions goal)

  where
  -- XXX: can use incremental for more efficient checking
  -- A simple way to figure out what might be relevant assumptions.
  dropAsmps keep asmps =
    case asmps of
      Seq.Empty -> return (NotTrivial goal { proofAssumptions = keep })
      a Seq.:<| as ->
        do res <- canProve ctxt goal { proofAssumptions = as Seq.>< keep }
           case res of
             Proved -> dropAsmps keep as
             NotProved {} -> dropAsmps (a Seq.:<| keep) as





simpProved' ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch -> ProofObligation sym -> IO ([ Assumption sym ], Bool)
simpProved' ctxt goal =
  do let false = falsePred (ctxt ^. ctxSymInterface)
         g1 = goal { proofGoal = (proofGoal goal) & labeledPred .~ false }
     res <- canProve ctxt g1
     case res of
       Proved ->
        do asmps <- dropAsmps Seq.empty (proofAssumptions g1) g1
           return (asmps, True)
       _ ->
        do asmps <- dropAsmps Seq.empty (proofAssumptions goal) goal
           return (asmps, False)

  where
  -- XXX: can use incremental for more efficient checking
  -- A simple way to figure out what might be relevant assumptions.
  dropAsmps keep asmps g =
    case asmps of
      Seq.Empty -> return (foldr (:) [] keep)
      a Seq.:<| as ->
        do res <- canProve ctxt g { proofAssumptions = as Seq.>< keep }
           case res of
             Proved       -> dropAsmps keep as g
             NotProved {} -> dropAsmps (a Seq.:<| keep) as g






