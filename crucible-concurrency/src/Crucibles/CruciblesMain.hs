{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module CrucesMain where

import Control.Lens
import Control.Monad
import Data.Foldable (toList)
import Data.List (groupBy, sortOn, find)
import Data.Text (pack)
import Data.String (IsString(..))
import System.Exit
import Text.Megaparsec as MP

import Data.Parameterized.Nonce
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some (Some(Some))

import qualified Lang.Crucible.CFG.Core as C
import Lang.Crucible.CFG.Reg
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Syntax.Concrete
import Lang.Crucible.Syntax.SExpr
import Lang.Crucible.Syntax.ExprParse (printSyntaxError)
import Lang.Crucible.Syntax.Atoms

import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.Backend
import Lang.Crucible.Backend.ProofGoals
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Simulator

import What4.Interface
import What4.ProgramLoc
import What4.SatResult
import What4.Solver (defaultLogData)
import Lang.Crucible.Backend.Online
import Data.Function (on)
import What4.FunctionName
import What4.Expr.Builder as B

import What4.Solver.Yices (runYicesInOverride)
import qualified Crux

import Primitives
import DPOR (DPOR)
import ExploreCrux
import ExploreTypes
import Data.Parameterized.Pair
import Crux.Types
import Crux.Goal
import qualified SimpleGetOpt as GetOpt
import Text.Read (readMaybe)

data CrucesOptions = CrucesOptions
  { noDpor :: Bool
  , debug  :: Bool
  , pedantic :: Bool
  , maxPreemptions :: Int
  , target :: FilePath
  }

defaultCrucesOptions :: CrucesOptions
defaultCrucesOptions = CrucesOptions
  { noDpor = False
  , debug  = False
  , pedantic = False
  , maxPreemptions = 0
  , target = ""
  }

cruciblesConfig :: Crux.Config CrucesOptions
cruciblesConfig = Crux.Config
  { Crux.cfgFile =  pure defaultCruciblesOptions
  , Crux.cfgEnv  = []
  , Crux.cfgCmdLineFlag =
      [ GetOpt.Option [] ["no-dpor"]
        "Enumerate all paths naively"
        (GetOpt.NoArg (\opts -> Right opts { noDpor = True }))
      , GetOpt.Option [] ["pedantic"]
        "Pedantic signal behavior (spurious wakeups)"
        (GetOpt.NoArg (\opts -> Right opts { pedantic = True }))
      , GetOpt.Option [] ["max-preemptions"]
        "Maximum number of preemptive context switches"
        (GetOpt.ReqArg "NUM" (\x opts ->
                                case readMaybe x of
                                  Just i  -> Right opts { maxPreemptions = i }
                                  Nothing -> Left "--max-preemptions requires an integer"))
      ]
  }

findMain :: FunctionName -> [ACFG] -> FnVal sym Ctx.EmptyCtx C.UnitType
findMain mainName cs =
  case find (isFn mainName) cs of
    Just (ACFG Ctx.Empty C.UnitRepr m) ->
      HandleFnVal (cfgHandle m)
    _ ->
      undefined
  where
    isFn x (ACFG _ _ g) = handleName (cfgHandle g) == x

run :: (Crux.Logs) => (Crux.CruxOptions, CruciblesOptions) -> IO ()
run (cruxOpts, opts) =
  do let ?dpor = not (noDpor opts)
     let ?bound = maxPreemptions opts
     let [fn] = Crux.inputFiles cruxOpts
     -- Some ng <- newIONonceGenerator
     ha      <- newHandleAllocator
     theInput <- readFile fn
     case MP.parse (skipWhitespace *> many (sexp atom) <* eof) fn (pack theInput) of
       Left err ->
         do putStrLn $ errorBundlePretty err
            exitFailure
       Right v ->
         withIONonceGenerator $ \nonceGen ->
           -- withYicesOnlineBackend FloatRealRepr nonceGen ProduceUnsatCores noFeatures $ \sym -> do
         do let mkSym :: forall s.
                  (IsSymInterface s, IsExprBuilder s) =>
                  s ->
                  IO ( FnVal s Ctx.EmptyCtx C.UnitType
                     , ExplorePrimitives (ThreadExec DPOR s () C.UnitType) s ()
                     , [Pair C.TypeRepr GlobalVar]
                     , FunctionBindings (ThreadExec DPOR s () C.UnitType) s ()
                     )
                mkSym _sym =
                  do exploreBuiltins <- mkExplorePrims ha (pedantic opts) (Some nonceGen)
                     let builtins = [ (SomeHandle h, InternalPos) | FnBinding h _ <- exploreBuiltins ]
                     parseResult <- top nonceGen ha builtins $ prog v
                     case parseResult of
                       Left (SyntaxParseError e) -> error $ show $ printSyntaxError e
                       Left err -> error $ show err
                       Right (gs, cs) ->
                         return ( findMain (fromString "main") cs
                                , crucibleSyntaxPrims
                                , toList gs
                                , fnBindingsFromList $
                                          [ case toSSA g of
                                              C.SomeCFG ssa ->
                                                FnBinding (cfgHandle g) (UseCFG ssa (postdomInfo ssa))
                                          | ACFG _ _ g <- cs
                                          ] ++ exploreBuiltins
                                )
            res <- Crux.runSimulator cruxOpts { Crux.solver = "yices"
                                              , Crux.pathSatSolver = Just "yices" } $
                     exploreCallback ha (view Crux.outputHandle ?outputConfig) mkSym -- fns gvs mainHdl
            let goo x = (fmap fst x, fmap snd x)
            case res of
              CruxSimulationResult ProgramIncomplete _ ->
                putStrLn "INCOMPLETE"
              CruxSimulationResult _ (goo -> (prs, gls)) ->
                do print (sum (fmap countTotalGoals gls), sum (fmap countProvedGoals gls), sum (fmap countDisprovedGoals gls))
                   print (sum (fmap totalProcessedGoals prs), sum (fmap provedGoals prs), sum (fmap disprovedGoals prs), sum (fmap incompleteGoals prs))

            return ()
                   -- checkSat <- pathSatisfiabilityFeature sym (considerSatisfiability sym)
                   -- (num, mfailed) <- exploreExecutions @DPOR sym ha debugH checkSat interpret mainHdl gvs fnBindings
                   -- hPutStrLn outh ("== Explored " ++ show num ++ " executions ==")
                   -- case mfailed of
                   --   Just failed ->
                   --     do hPutStrLn outh "UNSAFE:"
                   --        forM_ failed $ \((p,e):_) ->
                   --          do hPrint outh (ppSimError e)
                   --             hPutStrLn outh ("assert " ++ show (printSymExpr p) ++ " failed.")
                   --   Nothing ->
                   --      hPutStrLn outh "Proved all goals."

interpret ::
  YicesOnlineBackend scope x ->
  IO [[(B.Expr scope BaseBoolType, SimError)]]
interpret sym =
  do res <- getProofObligations sym >>= \case
       Nothing -> return []
       Just gs ->
         do let glist = goalsToList gs
            forM glist (\g ->
              do neggoal <- notPred sym (view labeledPred (proofGoal g))
                 let bs = neggoal : map (view labeledPred) (toList (proofAssumptions g))
                 runYicesInOverride sym defaultLogData bs (\case
                   Sat _   -> return (Left g)
                   Unsat _ -> return (Right g)
                   Unknown -> return (Left g)
                   )
              )
     let failed = groupBy ((==) `on` (simErrorLoc.snd)) $
           sortOn (simErrorLoc . snd) [ (proofGoal g ^. labeledPred, proofGoal g ^. labeledPredMsg)
                      | Left g <- res
                      ]
     return failed
