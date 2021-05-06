{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module           : Main
-- Description      : Run the Crucible model-checker backend
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Main
  ( main,
  )
where

import Control.Exception (Exception (..), throwIO)
import qualified Control.Lens as L
import Control.Monad (forM_)
import Control.Monad.State
import Crux.LLVM.Simulate (registerFunctions)
import Crux.Model
import Data.Functor.Const
import Data.IORef (newIORef)
import qualified Data.LLVM.BitCode as BC
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Sequence (Seq)
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Run
import Lang.Crucible.ModelChecker.Fresh
import Lang.Crucible.Simulator
import Lang.Crucible.Types
-- import Language.Sally
import System.IO (stdout)
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import What4.Interface
import What4.LabeledPred (labeledPred)
import What4.Protocol.Online
import qualified What4.TransitionSystem as TS

-- NOTE: you must run the executable from the "crucible" directory
testFile :: FilePath
testFile = "crucible-mc/test/example.bc"

testFun :: String
testFun = "myFunction"

userSymbol' :: String -> SolverSymbol
userSymbol' s = case userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

type ConcreteSym scope solver =
  Online.OnlineBackend scope solver (Online.Flags Online.FloatIEEE)

setupCruxLLVM ::
  OnlineSolver scope solver =>
  Module ->
  ConcreteSym scope solver ->
  CruxLLVM ()
setupCruxLLVM llvmMod sym = CruxLLVM $ \mt ->
  withPtrWidthOf mt $
    case findCFG mt testFun of
      Nothing -> throwIO (UnknownFunction testFun)
      Just (Core.AnyCFG cfg) ->
        let -- handle = Core.cfgHandle cfg
            fnArgs = Core.cfgArgTypes cfg
            fnRet = Core.cfgReturnType cfg
            (fnArgsNames, _) =
              runState (namesOfCrucibleTypes fnArgs) initNamingCounter
            fnArgsAndRet = Ctx.extend fnArgs fnRet
            fnArgsAndRetNames = Ctx.extend fnArgsNames (Const "ret")
         in do
              bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
              let ?badBehaviorMap = bbMapRef
              regMap <- freshRegMap sym fnArgsNames fnArgs
              pure
                Setup
                  { cruxOutput = stdout,
                    cruxBackend = sym,
                    cruxInitCodeReturns = fnRet,
                    cruxInitCode = do
                      registerFunctions llvmMod mt
                      RegEntry _retType retValue <- callCFG cfg regMap
                      pure retValue,
                    cruxUserState = emptyModel,
                    cruxGo = runExecState fnArgsAndRet fnArgsAndRetNames
                  }

main :: IO ()
main =
  do
    llvmMod <- parseLLVM testFile
    _ts <-
      withZ3 $
        runCruxLLVM llvmMod defaultMemOptions False
          . setupCruxLLVM llvmMod
    return ()

printProofGoals ::
  IsExprBuilder sym =>
  sym ->
  Backend.ProofGoals (SymExpr sym BaseBoolType) Backend.AssumptionReason SimError ->
  IO ()
printProofGoals sym (Backend.Assuming asmps goals) = do
  printAssumptions sym asmps
  printProofGoals sym goals
printProofGoals _ (Backend.Prove goal) = print . PP.pretty . printSymExpr $ L.view labeledPred goal
printProofGoals sym (Backend.ProveConj goals1 goals2) = do
  printProofGoals sym goals1
  printProofGoals sym goals2

printAssumptions ::
  IsExprBuilder sym =>
  sym ->
  Seq (Backend.LabeledPred (Pred sym) msg) ->
  IO ()
printAssumptions _ assumptions =
  forM_ assumptions $ \assumption ->
    print . PP.pretty . printSymExpr $ L.view labeledPred assumption

data SymbolicInformation sym rtp
  = SymbolicInformation
      { assumptions :: Seq (Backend.LabeledPred (Pred sym) Backend.AssumptionReason),
        obligations :: Backend.ProofObligations sym,
        returnValue :: RegEntry sym rtp
      }

-- | The @BaseTypeOfCrucibleType@ type family maps Crucible types to What4
-- types.  All base types are accounted for, for other types, we map it to the
-- type that is convenient for the model checker.
type family BaseTypeOfCrucibleType (c :: CrucibleType) :: BaseType where
  BaseTypeOfCrucibleType BoolType = BaseBoolType
  BaseTypeOfCrucibleType IntegerType = BaseIntegerType
  BaseTypeOfCrucibleType NatType = BaseNatType
  BaseTypeOfCrucibleType RealValType = BaseRealType
  BaseTypeOfCrucibleType (LLVMPointerType w) = BaseBVType w

-- | @BaseTypesOfCrucibleTypes@ is essentially a type-level "fmap", but
-- specialized to the @CrucibleType@ to @BaseType@ transformation, since we
-- can't have unsaturated type families.
type family BaseTypesOfCrucibleTypes (c :: Ctx CrucibleType) :: Ctx BaseType where
  BaseTypesOfCrucibleTypes EmptyCtx = EmptyCtx
  BaseTypesOfCrucibleTypes (c ::> ctp) =
    BaseTypesOfCrucibleTypes c ::> BaseTypeOfCrucibleType ctp

-- | @baseTypeReprOfTypeRepr@ implements the Crucible to What4 type translation
-- at the representation level.
baseTypeReprOfTypeRepr :: TypeRepr c -> BaseTypeRepr (BaseTypeOfCrucibleType c)
baseTypeReprOfTypeRepr BoolRepr = BaseBoolRepr
baseTypeReprOfTypeRepr IntegerRepr = BaseIntegerRepr
baseTypeReprOfTypeRepr NatRepr = BaseNatRepr
baseTypeReprOfTypeRepr RealValRepr = BaseRealRepr
baseTypeReprOfTypeRepr (LLVMPointerRepr w) = BaseBVRepr w
baseTypeReprOfTypeRepr tp = error $ "baseTypeReprOfTypeRepr: missing " ++ show tp

baseTypesOfCrucibleTypes ::
  Core.CtxRepr init ->
  Ctx.Assignment BaseTypeRepr (BaseTypesOfCrucibleTypes init)
baseTypesOfCrucibleTypes ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctx' ctp -> Ctx.extend (baseTypesOfCrucibleTypes ctx') (baseTypeReprOfTypeRepr ctp)

data NamingCounter
  = NamingCounter
      { _boolCounter :: Int,
        _integerCounter :: Int,
        _natCounter :: Int,
        _realCounter :: Int,
        _pointerCounter :: Int
      }

initNamingCounter :: NamingCounter
initNamingCounter =
  NamingCounter
    { _boolCounter = 0,
      _integerCounter = 0,
      _natCounter = 0,
      _realCounter = 0,
      _pointerCounter = 0
    }

boolCounter :: L.Lens' NamingCounter Int
boolCounter = L.lens _boolCounter (\c s -> c {_boolCounter = s})

integerCounter :: L.Lens' NamingCounter Int
integerCounter = L.lens _integerCounter (\c s -> c {_integerCounter = s})

natCounter :: L.Lens' NamingCounter Int
natCounter = L.lens _natCounter (\c s -> c {_natCounter = s})

realCounter :: L.Lens' NamingCounter Int
realCounter = L.lens _realCounter (\c s -> c {_realCounter = s})

pointerCounter :: L.Lens' NamingCounter Int
pointerCounter = L.lens _pointerCounter (\c s -> c {_pointerCounter = s})

freshName ::
  MonadState NamingCounter m =>
  L.Lens' NamingCounter Int ->
  String ->
  m String
freshName field prefix =
  do
    counter <- gets (L.view field)
    modify (L.over field (+ 1))
    return $ prefix ++ show counter

-- TODO Eventually it'd be nice if we could reuse the names of arguments from
-- Crucible, but I have not yet found a way of reaching to an @ExprSymFn@ from a
-- @CFG@
nameOfTypeRepr ::
  MonadState NamingCounter m =>
  TypeRepr c ->
  m String
nameOfTypeRepr BoolRepr = freshName boolCounter "b"
nameOfTypeRepr IntegerRepr = freshName integerCounter "i"
nameOfTypeRepr NatRepr = freshName natCounter "n"
nameOfTypeRepr RealValRepr = freshName realCounter "r"
nameOfTypeRepr (LLVMPointerRepr _) = freshName pointerCounter "p"
nameOfTypeRepr tp = error $ "nameOfTypeRepr: missing " ++ show tp

namesOfCrucibleTypes ::
  MonadState NamingCounter m =>
  Core.CtxRepr init ->
  m (Ctx.Assignment (Const String) init)
namesOfCrucibleTypes ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> return Ctx.empty
    Ctx.AssignExtend ctx' ctp ->
      do
        -- Given how contexts are nested, it makes more sense to recurse first
        names <- namesOfCrucibleTypes ctx'
        name <- nameOfTypeRepr ctp
        return $ Ctx.extend names (L.Const name)

-- | @baseTypesNames@ is an unfortunate non-free no-op to convince the type
-- checker that a bunch of names for a Crucible type context can be seen as a
-- bunch of names for a What4 type context.
-- The other equivalent option would be to re-run @namesOfCrucibleTypes@, which
-- would be about the same amount of work...
asBaseTypesNames ::
  Ctx.Assignment (Const String) init ->
  Ctx.Assignment (Const String) (BaseTypesOfCrucibleTypes init)
asBaseTypesNames ctx =
    case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctx' (Const s) -> Ctx.extend (asBaseTypesNames ctx') (Const s)

runExecState ::
  forall arch init p scope solver rtp.
  OnlineSolver scope solver =>
  HasPtrWidth (ArchWidth arch) =>
  Core.CtxRepr init ->
  -- Ctx.Assignment (Const String) (BaseTypesOfCrucibleTypes init) ->
  Ctx.Assignment (Const String) init ->
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) rtp) ->
  IO ()
runExecState argsTypes argsNames st =
  executeCrucible [] st
    >>= \case
      FinishedResult ctx (TotalRes gp) ->
        let sym = L.view ctxSymInterface ctx
         in do
              -- Print assumptions
              assumptions <- Backend.collectAssumptions sym
              putStrLn "=== Assumptions ==="
              print $ length assumptions
              forM_ assumptions $ \assumption ->
                print . PP.pretty . printSymExpr $ L.view labeledPred assumption
              -- Print obligations
              putStrLn "=== Obligations ==="
              obligations <- Backend.getProofObligations sym
              case obligations of
                Just goals -> printProofGoals sym goals
                Nothing -> putStrLn "No obligation"
              -- Print result
              let ret = L.view gpValue gp
              print $ regType ret
              () <- case regType ret of
                LLVMPointerRepr _w -> print . ppPtr . regValue $ ret
                _ -> return ()
              retExpr :: Pred (ConcreteSym scope solver) <-
                    case regType ret of
                    LLVMPointerRepr w ->
                      case regValue ret of
                      (llvmPointerView -> (blk, bv))
                        | Just 0 <- asNat blk ->
                          do
                            retVar <- freshBoundedBV sym (userSymbol' "ret") w Nothing Nothing
                            bvEq sym retVar bv
                        | otherwise -> error "TODO"
                    _ -> error "TODO"
              print retExpr
              let _info =
                    SymbolicInformation
                      { assumptions,
                        obligations,
                        returnValue = ret
                      }
              -- FIXME: need to turn CrucibleType into BaseType
              let ts :: TS.TransitionSystem (ConcreteSym scope solver) (BaseTypesOfCrucibleTypes init) =
                    TS.TransitionSystem
                      { stateFieldsRepr = baseTypesOfCrucibleTypes argsTypes,
                        stateFieldsNames = asBaseTypesNames argsNames,
                        initialStatePred = \_ -> return (truePred sym),
                        stateTransition = \_ _ -> return retExpr -- (truePred sym)
                      }
              print . PP.pretty =<< TS.transitionSystemToSally sym TS.mySallyNames ts
              return ()
      FinishedResult _ctx PartialRes {} -> error "PartialRes"
      AbortedResult {} -> error "Aborted"
      TimeoutResult {} -> error "Timeout"

-- | Create a Z3 backend for the simulator.
withZ3 ::
  (forall s. Online.Z3OnlineBackend s (Online.Flags Online.FloatIEEE) -> IO a) ->
  IO a
withZ3 k =
  withIONonceGenerator $ \nonceGen ->
    Online.withZ3OnlineBackend Online.FloatIEEERepr nonceGen Online.ProduceUnsatCores k

-- | This exception is thrown when we fail to parse a bit-code file.
data Err
  = BitcodeError BC.Error
  | UnknownFunction String
  | UnsupportedFunType String
  deriving (Show)

instance Exception Err

-- | Parse an LLVM bit-code file.
parseLLVM :: FilePath -> IO Module
parseLLVM file =
  do
    ok <- BC.parseBitCodeFromFile file
    case ok of
      Left err -> throwIO (BitcodeError err)
      Right m -> pure m
