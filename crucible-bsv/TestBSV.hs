{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST
import           Data.List
import qualified Data.Vector as V
import           System.IO

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), integer, bool)

import           Data.Parameterized.Nonce
import qualified Data.Parameterized.Map as MapF

import           Lang.BSV.AST
import           Lang.BSV.TransAST

import           Lang.Crucible.Analysis.Postdom
import           Lang.Crucible.Core
import           Lang.Crucible.Config
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.FunctionName
import           Lang.Crucible.Simulator.CallFns
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.MSSim
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Simulator.SimError

import           Lang.Crucible.Solver.Interface
import qualified Lang.Crucible.Solver.SimpleBackend as SB
import qualified Lang.Crucible.Solver.SimpleBackend.ABC as ABC
import           Lang.Crucible.Solver.Symbol

import           Lang.Crucible.BSV.Analysis
import           Lang.Crucible.BSV.Translation

integer :: Type
integer = TypeCon "Integer" []

int :: Integer -> Type
int n = TypeCon "Int" [TypeNat n]

uint :: Integer -> Type
uint n = TypeCon "UInt" [TypeNat n]

bit :: Integer -> Type
bit n = TypeCon "Bit" [TypeNat n]

bool :: Type
bool = TypeCon "Bool" []

vector :: Integer -> Type -> Type
vector n t = TypeCon "Vector" [TypeNat n, t]

mainArgs :: CtxRepr (EmptyCtx ::> BVType 128
                              ::> BVType 128)
mainArgs = knownRepr

mainRes :: TypeRepr (BVType 128)
mainRes = knownRepr

mainFun :: FunDef
mainFun =
  FunDef
  { funAttributeInstances = []
  , funDefProto =
    FunProto
    { funResultType = bit 128
    , funName = "main"
    , funFormals = [ (bit 128, "pt")
                   , (bit 128, "key")
                   ]
    , funProvisos = []
    }
  , funBody =
    [ StmtReturn $ ExprFunCall (ExprVar "aesEncrypt") [ExprVar "pt",ExprVar "key"]
    ]
  }

-- | Abort the current execution.
abortTree :: IsSymInterface sym => SimError -> SimState SimContext sym rtp f args -> IO (ExecResult (SimState SimContext sym) rtp)
abortTree e s = do
  let t = _stateTree s
  v <- getConfigValue verbosity (simConfig (s^.stateContext))
  when (v > 0) $ do
    let frames = activeFrames t
    let msg = ppExceptionContext frames e
    -- Print error message.
    hPrint (printHandle (s^.stateContext)) $ msg
  -- Switch to new frame.
  abortExec e s

defaultErrorHandler :: IsSymInterface sym => ErrorHandler SimContext sym rtp
defaultErrorHandler = EH abortTree

registerCFG :: AnyCFG
            -> MSSim sym rtp l a ()
registerCFG (AnyCFG cfg) =
  registerFnBinding (cfgHandle cfg) (UseCFG cfg (postdomInfo cfg))

consumeBy :: Int -> ([a] -> b) -> [a] -> [b]
consumeBy n f = unfoldr h
 where h [] = Nothing
       h xs = let (hd,tl) = splitAt n xs
                  z = f hd
               in Just (z, tl)

main :: IO ()
main = do
  aesDefs <- read <$> hGetContents stdin
  let (Just res, errs) = trans aesDefs
  unless (null errs) $ do
     putStrLn "Errors!"
     putStrLn "================="
     mapM_ putStrLn errs
     putStrLn "================="
  let tenv = processTypedefs (packageStmts res) initialTypeEnv
  withHandleAllocator $ \halloc ->
    do venv0 <- stToIO $ initialValEnv halloc
       (venv,cfgs) <- stToIO $ translatePackageFuns halloc tenv venv0 (packageStmts res)
       mainHdl <- stToIO $ mkHandle' halloc (functionNameFromText $ "main") mainArgs mainRes
       (SomeCFG main_cfg,cfgs') <- stToIO $ translateFun halloc mainHdl tenv venv mainFun
       let allCfgs = cfgs++cfgs'

       withIONonceGenerator $ \ng ->
         do sym <- SB.newSimpleBackend ng
            config <- initialConfig 0 []
            let simctx = initSimContext sym MapF.empty config halloc stdout emptyHandleMap
            let globalstate = emptyGlobals
            let errorHandler = defaultErrorHandler
            res <- run simctx globalstate errorHandler UnitRepr $
                    do mapM_ registerCFG allCfgs
                       let Right ptnm  = userSymbol "pt"
                       let Right keynm = userSymbol "key"
                       pt  <- liftIO $ freshConstant sym ptnm  knownRepr
                       key <- liftIO $ freshConstant sym keynm knownRepr
                       let args = assignReg knownRepr key $
                                  assignReg knownRepr pt $
                                  emptyRegMap
                       x <- callCFG main_cfg args
                       liftIO $ do
                         putStrLn "Writing AIG..."
                         ABC.writeAig "output.aig" [Some (regValue x)] []

            case res of
              FinishedExecution _simctx' pr -> case pr of
                 TotalRes _ ->
                   do putStrLn "All paths succeeded"
                 PartialRes _p _gp ar ->
                   do putStrLn "Some paths failed"
                      ppAbortedResult ar
              AbortedResult _simctx' ar ->
                   do putStrLn "All paths failed"
                      ppAbortedResult ar


ppAbortedResult :: AbortedResult (s :: * -> fk -> argk -> *) -> IO ()
ppAbortedResult (AbortedExec err _) = print err
ppAbortedResult (AbortedBranch _ a1 a2) = ppAbortedResult a1 >> ppAbortedResult a2
