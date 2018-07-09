{-# Language TypeFamilies #-}
{-# Language PatternSynonyms #-}
module Goal where

import Control.Lens((^.), (&), (.~))
import Control.Monad(forM)
import qualified Data.Sequence as Seq
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.List(mapAccumL)
import Data.IORef

import What4.Interface (notPred, falsePred, Pred, printSymExpr)
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

type LPred sym   = LabeledPred (Pred sym)

data IsLoop      = NotLoop | LoopIter !Int
data PredLoc     = PL ProgramLoc IsLoop{-LAZY-}

data ProvedGoals =
    AtLoc PredLoc (Maybe ProgramLoc) ProvedGoals
  | Branch [ ProvedGoals ]
  | Goal [(AsmpLab,String)] (SimError,String) Bool ProofResult
    -- ^ Keeps only the explanations for the relevant assumptions.
    -- The 'Bool' indicates if the goal is trivial (i.e., the assumptions
    -- are inconsistent)

-- | Locations are annotated with loop information.
data AsmpLab = Exploring PredLoc (Maybe ProgramLoc)
             | OtherAsmp AssumptionReason {- Not ExploringAPat -}

-- | Simplify the proved goals.
provedGoalsTree ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
  Goals (LPred sym AsmpLab) (Assertion sym, ProofResult) ->
  IO ProvedGoals
provedGoalsTree ctxt = go []
  where
  go asmps gs =
    case gs of
      Assuming p gs1 ->
        case p ^. labeledPredMsg of
          Exploring from to -> AtLoc from to <$> go (p : asmps) gs1
          _                 -> go (p : asmps) gs1
      Prove (p,r)  ->
        case r of
          Proved ->
            do (as1,triv) <- simpProved ctxt ProofGoal
                                   { proofAssumptions = Seq.fromList asmps
                                   , proofGoal        = p
                                   }
               return (Goal (map mkAsmp as1) (mkAsmp p) triv Proved)

          _ -> return (Goal (map mkAsmp asmps) (mkAsmp p) False r)

      ProveAll gss -> Branch <$> mapM (go asmps) gss

  mkAsmp a = (a ^. labeledPredMsg, show (printSymExpr (a ^. labeledPred)))


countGoals :: Goals a b -> Int
countGoals gs =
  case gs of
    Assuming _ gs1 -> countGoals gs1
    Prove _        -> 1
    ProveAll gs1   -> sum (map countGoals gs1)




-- | Annotate exploration assumptions with how many times they've
-- been visited on a particular path.
addLoopMarkers :: Goals (LabeledPred p AssumptionReason) g ->
                  Goals (LabeledPred p AsmpLab) g
addLoopMarkers gs0 = finGs
  where
  (loopSet,finGs) = go loopSet Map.empty Set.empty gs0

  go finLoops mp loops gs =
    case gs of
      Assuming p gs1 ->
        let (lab,mp1) =
               case p ^. labeledPredMsg of
                 ExploringAPath from to ->
                   let mp' = Map.insertWith (+) from 1 mp
                       cnt = if from `Set.member` finLoops
                                then LoopIter (mp1 Map.! from)
                                else NotLoop
                   in (Exploring (PL from cnt) to, mp')
                 q -> (OtherAsmp q, mp)
            (ls1,res) = go finLoops mp1 loops gs1
        in (ls1, Assuming (p & labeledPredMsg .~ lab) res)
      Prove p ->
        let ls = Set.union (Map.keysSet (Map.filter (> 1) mp)) loops
        in (ls, Prove p)
      ProveAll gss ->
        let (ls1, res) = mapAccumL (go finLoops mp) loops gss
        in (ls1, ProveAll res)



-- | Prove a collection of goals.  The result is a goal tree, where
-- each goal is annotated with the outcome of the proof.
proveGoals ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
      Goals (LPred sym asmp) (LPred sym ast) ->
  IO (Goals (LPred sym asmp) (LPred sym ast, ProofResult))
proveGoals ctxt gs0 =
  do let sym = ctxt ^. ctxSymInterface
     sp <- getSolverProcess sym
     goalNum <- newIORef 1
     inNewFrame (solverConn sp) (go sp goalNum gs0)
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
  SimCtxt sym arch -> ProofGoal (Pred sym) asmp ast -> IO ProofResult

canProve ctxt g = proveGoal' ctxt g $ \_sp -> return Nothing


proveGoal' ::
  ( sym ~ ExprBuilder s (OnlineBackendState solver)
  , OnlineSolver s solver
  ) =>
  SimCtxt sym arch ->
  ProofGoal (Pred sym) asmp ast ->
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
  SimCtxt sym arch ->
  ProofGoal (Pred sym) asmp ast ->
  IO ( [ LPred sym asmp ], Bool )

simpProved ctxt goal =
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






