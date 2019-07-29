--{-# LANGUAGE DataKinds #-}

--{-# LANGUAGE GADTs #-}
--{-# LANGUAGE TypeFamilies #-}
--{-# LANGUAGE AllowAmbiguousTypes #-}



{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.LTLSafety
--(
  --testExecFeat
--)
where

import Lang.Crucible.Simulator.EvalStmt
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.CallFrame
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.Intrinsics
import Lang.Crucible.Simulator.SimError

import Lang.Crucible.Backend
import Lang.Crucible.FunctionHandle
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core

import Lang.Crucible.Types

import What4.FunctionName
import What4.Interface
import What4.ProgramLoc

import ABI.Itanium as ABI

import Control.Lens
import Control.Monad ( when )
import Control.Monad.ST
import Control.Monad.IO.Class(liftIO)

import Data.IORef
import Data.Parameterized.Nonce.Unsafe
import qualified Data.Parameterized.Map as MapF
import Data.Text (Text)
import Data.Text as Text
import Data.Vector as Vec
import Data.Set as Set
import Data.List as L
-- define helper types
data NFASym = Call String | Return String deriving (Show, Eq, Ord)
-- | CallWithArg String RegEntry
-- | Return String RegEntry
data NFAState =
  Error
  | Accept
  | St Int 
 -- | forall sym tp. StWithData Int (Maybe (RegEntry sym tp))
  deriving (Show, Eq, Ord) -- initial is ST 0
{-instance Show NFAState where
  show _ = "no"

instance Ord NFAState where
  Error <= _ = True
  Accept <= Error = False
  Accept <= _ = True
  St x <= St y = x <= y
  _ <= St _ = True

instance Eq NFAState where
  Error == Error = True
  Accept == Accept = True
  St x == St y = x == y
  StWithData x1 x2 == StWithData y1 y2 = (x1 == y1) && (x2 == y2)
  _ == _ = False
  -}


data NFA = NFA { stateSet :: Vector NFAState,
                 nfaState :: Set NFAState,
                 nfaAlphabet :: Set NFASym,
                 transitionFunction :: Vector [(NFASym,NFAState)]} deriving Show

stateTransition (St stid) tf symbol =
  Set.fromList $ Prelude.map snd (Prelude.filter (\edge -> symbol == (fst edge)) (tf ! stid))
stateTransition _ _ _ = Set.empty

nfaTransition nfa symbol =
  case (member symbol (nfaAlphabet nfa)) of
    True -> nfa {nfaState = unions $ Set.map (\state -> stateTransition state (transitionFunction nfa) symbol) (nfaState nfa)}
    _ -> nfa
    


edges0 = [(Call "A", St 1 ), (Call "B", St 2 ), (Call "C", Error)]
edges1 = [(Call "B", St 3 ), (Call "C", Error)]
edges2 = [(Call "A", St 3 ), (Call "C", Error)]
edges3 = [(Call "C", Accept)]
alphabet = Set.fromList [Call "A", Call "B", Call "C" ]
tf = Vec.fromList[edges0, edges1, edges2, edges3]
states = Vec.fromList[St 0, St 1, St 2, St 3]
initNFA = NFA states (Set.insert (St 0) Set.empty) alphabet tf
                              
{-
edges0 = [(Call "A()", St 1), (Call "B()", Error)]
--edges1 = [(Call "B()", St 0)]
edges1 = [(Call "B()", Accept)]
alphabet = Set.fromList [Call "A()", Call "B()"]
states = Vec.fromList [St 0, St 1]
tf = Vec.fromList [edges0, edges1]
initNFA = NFA states (insert (St 0) Set.empty) alphabet tf 
-}


-- define intrinsic type
data LTLData = LDat NFA 

instance IntrinsicClass sym "LTL" where
  type Intrinsic sym "LTL" ctx = LTLData

  muxIntrinsic _sym _iTypes _nm _ _p d1 d2 = combineData d1 d2

combineData (LDat(NFA {stateSet=ss, nfaState=state1, nfaAlphabet=alpha, transitionFunction=tf})) (LDat (NFA {nfaState=state2})) =
  do
    putStrLn "in mux"
    return $ LDat (NFA ss (Set.union state1 state2) alpha tf)

type LTLGlobal = GlobalVar (IntrinsicType "LTL" EmptyCtx)

-- helpers
nfaupdate gvRef ss symbol =
  do
    gv <- readIORef gvRef
    case (lookupGlobal gv (ss ^. stateGlobals)) of
      Just (LDat nfa) ->
        case (member Error (nfaState resultNFA)) of
          False ->
            do
              putStrLn $ show $ nfaState nfa
              putStrLn $ show $ nfaState resultNFA
              return $ Just (ss & stateGlobals %~ (insertGlobal gv (LDat resultNFA)))
          _ ->
            do
              putStrLn $ show $ nfaState nfa
              putStrLn $ show $ nfaState resultNFA
              return Nothing
        where resultNFA = (nfaTransition nfa symbol)
      _ -> return Nothing

withoutType funName =
  case (L.elemIndex '(' funName) of
    Just n -> L.take n funName
    _ -> "err"

pCallName (CrucibleCall _ CallFrame { _frameCFG = cfg}) =
  withoutType $ dN $ unpack $ functionName $ handleName $ cfgHandle cfg
pCallName _ = "Override called"

dN :: String -> String
dN name =
  case ABI.demangleName name of
    Left _ -> "err"
    Right nm -> cxxNameToString nm

--abortState :: (IsExprBuilder sym  , IsBoolSolver sym) =>  SimState p sym ext rtp f a ->
 --  IO (ExecutionFeatureResult p sym ext rtp)
errorMsg (CrucibleCall _ cf) ss =
  do
    let sym = ss^.stateSymInterface
    --loc <- getCurrentProgramLoc sym
    let loc =  frameProgramLoc cf
    let msg = "funciton dependency error at: " Prelude.++ (show (plFunction loc))Prelude.++ (show  (plSourceLoc loc))
    let err = SimError loc (GenericSimError msg)
    addProofObligation sym (LabeledPred (falsePred sym) err)
    return (AbortState (AssumedFalse (AssumingNoError err)) ss)
    --return $ ExecutionFeatureNewState (AbortState (AssumedFalse (AssumingNoError err)) ss) 

testExecFeat :: IORef LTLGlobal -> GenericExecutionFeature sym
testExecFeat gvRef = GenericExecutionFeature $ (onStep gvRef)
      
onStep :: (IsExprBuilder sym , IsBoolSolver sym ) => IORef LTLGlobal -> ExecState p sym ext rtp -> IO (ExecutionFeatureResult p sym ext rtp)
onStep gvRef (InitialState simctx globals ah cont) = do
  let halloc = simHandleAllocator simctx
  gv <- stToIO (freshGlobalVar halloc (pack "LTL") knownRepr)
  writeIORef gvRef gv
  putStrLn "initialize"
  let globals' = insertGlobal gv (LDat initNFA) globals
  let simctx' = simctx{ ctxIntrinsicTypes = MapF.insert (knownSymbol @"LTL") IntrinsicMuxFn (ctxIntrinsicTypes simctx) }
  return ( ExecutionFeatureModifiedState (InitialState simctx' globals' ah cont))

onStep gvRef (CallState rh rc ss) =
  do
    let symbol = Call $ pCallName rc
    putStrLn $ show symbol
    result <- (nfaupdate gvRef ss symbol)
    case result of
      Just ss' -> return $ ExecutionFeatureModifiedState (CallState rh rc ss')
      Nothing ->
        do
          abortState <- errorMsg rc ss 
          return $ ExecutionFeatureNewState abortState
      
onStep gvRef (ReturnState fname vfv regEntry ss) =
  do
    let fn = dN $ unpack $ functionName fname
    let retVal = show (regType regEntry)
    putStrLn (fn Prelude.++ " returning " Prelude.++ retVal)
    case (regType regEntry) of
      IntrinsicRepr _ _ -> putStrLn "intrinsic"
      _ -> putStrLn "not instrinsic"
    return ExecutionFeatureNoChange
        
onStep _ _ =
  do
    --putStrLn "test exec"
    return ExecutionFeatureNoChange


printReturn (TotalRes gp) =
   show $ gp ^. gpValue
printReturn _ = "no"
