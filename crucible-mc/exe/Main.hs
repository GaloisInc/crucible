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
import Control.Monad (forM, forM_)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (MonadReader, asks, runReaderT)
import Control.Monad.State (MonadState, get, gets, modify, runState, runStateT)
import Crux.LLVM.Simulate (registerFunctions)
import Crux.Model
import Data.Foldable (toList)
import Data.Functor.Const
import Data.IORef (newIORef)
import qualified Data.LLVM.BitCode as BC
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Nonce (withIONonceGenerator)
import Data.Parameterized.TraversableFC
import Data.Proxy
-- import Data.Sequence (Seq)
import GHC.Natural
import qualified Lang.Crucible.Backend as Backend
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
-- import qualified Lang.Crucible.CFG.Expr as Expr
-- import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.Globals
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)
import Lang.Crucible.LLVM.MemType
import Lang.Crucible.LLVM.Run
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.LLVM.TypeContext
import Lang.Crucible.ModelChecker.Fresh
import Lang.Crucible.ModelChecker.MCReader
import Lang.Crucible.ModelChecker.MCState
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.GlobalState
import Lang.Crucible.Types
import Print
import System.IO (stdout)
import qualified Text.LLVM as TL
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import What4.Expr.Builder
import qualified What4.Interface as What4
import What4.LabeledPred (labeledPred)
import What4.Protocol.Online
import qualified What4.TransitionSystem as TS

-- NOTE: you must run the executable from the "crucible" directory
testFile :: FilePath
testFile = "crucible-mc/test/example.bc"

-- testFile = "crucible-mc/test/diamond.bc"

testFun :: String
testFun = "myFunction"

userSymbol' :: String -> What4.SolverSymbol
userSymbol' s = case What4.userSymbol s of
  Left e -> error $ show e
  Right symbol -> symbol

-- | @currentBlockVariable@ will be used for the name of the variable
-- representing the current basic block of execution
currentBlockVariable :: String
currentBlockVariable = "block__CRUCIBLEMC__"

-- | @returnValueVariable@ will be used for the name of the variable
-- representing the return value of the entire program
returnValueVariable :: String
returnValueVariable = "ret__CRUCIBLEMC__"

-- | @hasReturnedVariable@ will be used to indicate when the original program is
-- considered to have returned, so as to condition when the final result
-- equation is meant to hold
hasReturnedVariable :: String
hasReturnedVariable = "hasReturned__CRUCIBLEMC__"

type ConcreteSym scope solver =
  Online.OnlineBackend scope solver (Online.Flags Online.FloatIEEE)

-- | This functions sets up the Crux LLVM simulator we will use.  One particular
-- setup step is coming up with names for the arguments of the function: those
-- are not easily accessible here, so we generate fresh ones, using the type as
-- guidance for the prefix.
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
        let fnArgs = Core.cfgArgTypes cfg
            fnRet = Core.cfgReturnType cfg
            -- it seems that at this point, Crucible has not kept the names of
            -- variables, so we come up with fresh ones
            (fnArgsNames, _) =
              runState (namesOfCrucibleTypes fnArgs) initNamingCounter
            initInfos =
              Ctx.zipWith
                (\initTypeRepr (Const initSymbol) -> InitInfo {initSymbol, initTypeRepr})
                fnArgs
                fnArgsNames
            llvmCtx = L.view transContext mt
            globInit = globalInitMap mt
         in do
              bbMapRef <- newIORef (Map.empty :: LLVMAnnMap sym)
              let ?badBehaviorMap = bbMapRef
              regMap <- freshRegMap sym fnArgsNames fnArgs
              return
                Setup
                  { cruxOutput = stdout,
                    cruxBackend = sym,
                    cruxInitCodeReturns = fnRet,
                    cruxInitCode = do
                      registerFunctions llvmMod mt
                      RegEntry _ retValue <- callCFG cfg regMap
                      return retValue,
                    cruxUserState = emptyModel,
                    -- cruxGo = runExecState cfg fnArgsNames
                    cruxGo = runExecState cfg llvmCtx globInit initInfos
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

-- printProofGoals ::
--   IsExprBuilder sym =>
--   sym ->
--   Backend.ProofGoals (SymExpr sym BaseBoolType) Backend.AssumptionReason SimError ->
--   IO ()
-- printProofGoals sym (Backend.Assuming asmps goals) = do
--   printAssumptions sym asmps
--   printProofGoals sym goals
-- printProofGoals _ (Backend.Prove goal) = print . PP.pretty . printSymExpr $ L.view labeledPred goal
-- printProofGoals sym (Backend.ProveConj goals1 goals2) = do
--   printProofGoals sym goals1
--   printProofGoals sym goals2

-- printAssumptions ::
--   IsExprBuilder sym =>
--   sym ->
--   Seq (Backend.LabeledPred (Pred sym) msg) ->
--   IO ()
-- printAssumptions _ assumptions =
--   forM_ assumptions $ \assumption ->
--     print . PP.pretty . printSymExpr $ L.view labeledPred assumption

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

-- | @asBaseTypesNames@ is an unfortunate non-free no-op to convince the type
-- checker that a bunch of names for a Crucible type context can be seen as a
-- bunch of names for a What4 type context.  The other equivalent option would
-- be to re-run @namesOfCrucibleTypes@, which would be about the same amount of
-- work...
asBaseTypesNames ::
  Ctx.Assignment (Const String) init ->
  Ctx.Assignment (Const String) (BaseTypesOfCrucibleTypes init)
asBaseTypesNames ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend ctx' (Const s) -> Ctx.extend (asBaseTypesNames ctx') (Const s)

addNamespaceToVariables ::
  forall t st fs stateFields tp.
  ExprBuilder t st fs ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  What4.SymStruct (ExprBuilder t st fs) stateFields ->
  Expr t tp ->
  IO (Expr t tp)
addNamespaceToVariables sym stateFieldsRepr state = goExpr
  where
    -- @Expr@
    goExpr :: forall tp'. Expr t tp' -> IO (Expr t tp')
    goExpr sr@(SemiRingLiteral {}) = pure sr
    goExpr sr@(BoolExpr {}) = pure sr
    goExpr sr@(StringExpr {}) = pure sr
    goExpr (asApp -> Just a) = sbMakeExpr sym =<< goApp a
    goExpr (NonceAppExpr {}) = error "NonceApp"
    goExpr (BoundVarExpr e) =
      do
        let expectedType = bvarType e
        fieldAccess sym stateFieldsRepr (show $ bvarName e) expectedType state
    goExpr e = error $ show e
    -- @App@
    goApp :: forall tp'. App (Expr t) tp' -> IO (App (Expr t) tp')
    goApp = traverseApp goExpr

data MCBlock sym
  = MCBlock
      { _mcBlockID :: Natural,
        -- obligations that must hold while this is the current block
        _mcBlockObligations :: [What4.Pred sym],
        _mcBlockPres :: [What4.Pred sym],
        _mcBlockPosts :: [What4.Pred sym]
      }

data TransitionSystemInfo sym ret
  = TransitionSystemInfo
      { blocks :: [MCBlock sym],
        finalBlock :: Natural,
        finalObligations :: [What4.Pred sym],
        initialBlock :: Natural,
        functionArguments :: Some (Ctx.Assignment TypeRepr),
        globalStateInfo :: Some (Ctx.Assignment (GlobalInfo sym)),
        returnValue :: RegEntry sym ret,
        transitions :: [MCTransition sym]
      }

-- | @initialStateGlobal@ turns a @GlobInfo@ gathered information about a global
-- variable into a @Pred sym@ that can be used as a conjunct in the initial
-- state predicate.  The predicate simply asserts that the global variable is
-- equal to its initial value.
initialStateGlobal ::
  What4.IsSymExprBuilder sym =>
  sym ->
  GlobalInfo sym tp ->
  IO (What4.Pred sym)
initialStateGlobal sym (GlobalInfo {..}) =
  case globalTypeRepr of
    LLVMPointerRepr w ->
      do
        let (_, bv) = llvmPointerView globalRegValue
        v <- What4.freshBoundedBV sym (userSymbol' globalSymbol) w Nothing Nothing
        What4.bvEq sym v bv
    _ -> error "TODO"

-- | @makeTransitionSystem@ uses all of the gathered program information to
-- build the final transition system.
makeTransitionSystem ::
  forall globCtx initCtx retTp sym t st fs.
  sym ~ ExprBuilder t st fs =>
  What4.IsSymExprBuilder sym =>
  sym ->
  -- | Info about the global context
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  Ctx.Assignment InitInfo initCtx ->
  RegEntry sym retTp ->
  [MCBlock sym] ->
  [MCTransition sym] ->
  Natural ->
  Natural ->
  [What4.Pred sym] ->
  IO
    ( TS.TransitionSystem sym
        ( ( BaseTypesOfCrucibleTypes globCtx
              Ctx.<+> BaseTypesOfCrucibleTypes initCtx
          )
            Ctx.::> BaseTypeOfCrucibleType retTp -- return value
            Ctx.::> BaseBoolType -- whether the program has returned
            Ctx.::> BaseNatType -- current block
        )
    )
makeTransitionSystem sym globInfos initInfos retVal blocks transitions initialBlock finalBlock finalObligations =
  do
    let retTp = regType retVal
    -- NOTE: the structure of the next two variables must match exactly the
    -- structure of the return type of this function
    let stateFieldsRepr =
          ( baseTypesOfCrucibleTypes (globalTypeReprs globInfos)
              Ctx.<++> baseTypesOfCrucibleTypes (initTypeReprs initInfos)
          )
            `Ctx.extend` baseTypeReprOfTypeRepr retTp
            `Ctx.extend` BaseBoolRepr
            `Ctx.extend` BaseNatRepr
    let stateFieldsNames =
          ( asBaseTypesNames (globalSymbols globInfos)
              Ctx.<++> asBaseTypesNames (initSymbols initInfos)
          )
            `Ctx.extend` Const returnValueVariable
            `Ctx.extend` Const hasReturnedVariable
            `Ctx.extend` Const currentBlockVariable
    initialStatePredicates <- sequenceA $ toListFC (initialStateGlobal sym) globInfos
    currentBlock <- What4.freshConstant sym (userSymbol' currentBlockVariable) BaseNatRepr
    hasReturned <- What4.freshConstant sym (userSymbol' hasReturnedVariable) BaseBoolRepr
    initialBlockPredicate <-
      do
        initialBlockLit <- What4.natLit sym initialBlock
        What4.natEq sym currentBlock initialBlockLit
    initialStateHasNotReturned <- What4.notPred sym hasReturned
    initialState <-
      What4.andAllOf
        sym
        L.folded
        ( initialBlockPredicate
            : initialStateHasNotReturned
            : initialStatePredicates
        )
    blockQueries <- forM blocks $ \MCBlock {..} ->
      do
        thisBlock <- What4.natLit sym _mcBlockID
        isCurrentBlock <- What4.natEq sym currentBlock thisBlock
        obligations <- What4.andAllOf sym L.folded _mcBlockObligations
        What4.impliesPred sym isCurrentBlock obligations
    finalQuery <-
      do
        finalObligation <- What4.andAllOf sym L.folded finalObligations
        What4.impliesPred sym hasReturned finalObligation
    return $
      TS.TransitionSystem
        { stateFieldsRepr,
          stateFieldsNames,
          initialStatePred = \_ -> pure initialState,
          stateTransitions = makeStateTransitions sym stateFieldsRepr blocks transitions finalBlock retVal globInfos,
          -- NOTE: putting the final query last because it's nicer in the output
          queries = pure (blockQueries ++ [finalQuery])
        }

fieldAccessor ::
  What4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment BaseTypeRepr ctx ->
  String ->
  BaseTypeRepr fieldType ->
  IO (What4.SymFn sym (Ctx.EmptyCtx Ctx.::> What4.BaseStructType ctx) fieldType)
fieldAccessor sym stateType fieldName fieldType =
  What4.freshTotalUninterpFn
    sym
    (userSymbol' fieldName)
    (Ctx.Empty Ctx.:> BaseStructRepr stateType)
    fieldType

fieldAccess ::
  What4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment BaseTypeRepr ctx ->
  String ->
  BaseTypeRepr fieldType ->
  What4.SymStruct sym ctx ->
  IO (What4.SymExpr sym fieldType)
fieldAccess sym stateType fieldName fieldType state =
  do
    accessor <- fieldAccessor sym stateType fieldName fieldType
    What4.applySymFn sym accessor (Ctx.Empty Ctx.:> state)

preserveGlobal ::
  What4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  What4.SymStruct sym stateFields ->
  What4.SymStruct sym stateFields ->
  GlobalInfo sym tp ->
  IO (What4.Pred sym)
preserveGlobal sym stateFieldsRepr state next (GlobalInfo {..}) =
  do
    let accessGlobal =
          fieldAccess
            sym
            stateFieldsRepr
            globalSymbol
            (baseTypeReprOfTypeRepr globalTypeRepr)
    globalNow <- accessGlobal state
    globalNext <- accessGlobal next
    What4.isEq sym globalNow globalNext

-- | @makeStateTransitions@ builds the actual transitions of the transition
-- system based on information about the basic blocks and transitions across them.
makeStateTransitions ::
  sym ~ ExprBuilder t st fs =>
  What4.IsSymExprBuilder sym =>
  sym ->
  Ctx.Assignment BaseTypeRepr stateFields ->
  [MCBlock sym] ->
  [MCTransition sym] ->
  Natural ->
  RegEntry sym ret ->
  Ctx.Assignment (GlobalInfo sym) globCtx ->
  What4.SymStruct sym stateFields ->
  What4.SymStruct sym stateFields ->
  IO [(String, What4.Pred sym)]
makeStateTransitions sym stateFieldsRepr blocks transitions finalBlock ret globInfos state next =
  do
    let accessCurrentBlock = fieldAccess sym stateFieldsRepr currentBlockVariable BaseNatRepr
    stateBlock <- accessCurrentBlock state
    nextBlock <- accessCurrentBlock next
    stateHasReturned <- fieldAccess sym stateFieldsRepr hasReturnedVariable BaseBoolRepr state
    nextHasReturned <- fieldAccess sym stateFieldsRepr hasReturnedVariable BaseBoolRepr next
    -- FIXME: this is incorrect but here for debugging
    -- FIXME: currently assuming that global variables are never modified
    globsPreserved <- sequenceA $ toListFC (preserveGlobal sym stateFieldsRepr state next) globInfos
    blockTransitions <- forM blocks $ \MCBlock {..} ->
      do
        currentBlock <- What4.natLit sym _mcBlockID
        currentBlockEq <- What4.natEq sym stateBlock currentBlock
        let transitionsOutOfThisBlock = filter ((== _mcBlockID) . _fromBlock) transitions
        transitionsEqs <- forM transitionsOutOfThisBlock $ \MCTransition {..} ->
          do
            toBlock <- What4.natLit sym _toBlock
            -- FIXME: shouldn't this be condition implies eq?
            nextBlockEq <- What4.natEq sym nextBlock toBlock
            namespacedCondition <- addNamespaceToVariables sym stateFieldsRepr next _condition
            What4.impliesPred sym namespacedCondition nextBlockEq
        -- if this was the final block, set @hasReturned@ to true, and set
        -- @returnValue@ to the return value, otherwise, maintain @hasReturned@
        -- false
        returnPredicate <-
          if _mcBlockID == finalBlock
            then case regType ret of
              LLVMPointerRepr w ->
                case regValue ret of
                  (llvmPointerView -> (blk, bv))
                    | Just 0 <- What4.asNat blk ->
                      liftIO $ do
                        bv' <- addNamespaceToVariables sym stateFieldsRepr state bv
                        nextReturnVariable <- fieldAccess sym stateFieldsRepr returnValueVariable (BaseBVRepr w) next
                        retEq <- What4.bvEq sym nextReturnVariable bv'
                        What4.andPred sym retEq nextHasReturned
                    | otherwise -> error "TODO"
              _ -> error "TODO"
            else What4.notPred sym nextHasReturned
        blockPres <- forM _mcBlockPres (addNamespaceToVariables sym stateFieldsRepr state)
        blockPosts <- forM _mcBlockPosts (addNamespaceToVariables sym stateFieldsRepr state)
        hasNotReturned <- What4.notPred sym stateHasReturned
        t <-
          What4.andAllOf
            sym
            L.folded
            ( hasNotReturned
                : currentBlockEq
                : returnPredicate
                : transitionsEqs
                ++ globsPreserved
                ++ blockPres
                ++ blockPosts
            )
        return (transitionName _mcBlockID, t)
    programEndedTransition <-
      do
        programEnded <- What4.andAllOf sym L.folded (stateHasReturned : nextHasReturned : globsPreserved)
        return ("Program_Ended", programEnded)
    return (blockTransitions ++ [programEndedTransition])

transitionName :: Natural -> String
transitionName n = "Block_" ++ show n

runExecState ::
  forall arch blocks init p scope solver ret.
  OnlineSolver scope solver =>
  HasPtrWidth (ArchWidth arch) =>
  Core.CFG (LLVM arch) blocks init ret ->
  LLVMContext arch ->
  GlobalInitializerMap ->
  Ctx.Assignment InitInfo init ->
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) ret) ->
  IO ()
runExecState cfg llvmCtx globInit initInfos execState =
  do
    let mcReader =
          MCReader
            { _mcCFG = cfg,
              _mcGlobInit = globInit,
              _mcLLVMContext = llvmCtx
            }
    let mcState =
          MCState
            { _mcBlocksInformation = Map.empty,
              _mcCurrentBlock = Nothing,
              _mcInitialBlock = Nothing,
              _mcTransitions = [],
              _mcGlobals = Nothing
            }
    TransitionSystemInfo {..} <-
      (fst <$>)
        $ flip runStateT mcState
        $ flip runReaderT mcReader
        $ stepExecState Proxy execState
    case globalStateInfo of
      Core.Some globInfos ->
        do
          -- print $ Core.ppCFG True cfg
          let sym = L.view ctxSymInterface (execStateContext execState)
          ts <- makeTransitionSystem sym globInfos initInfos returnValue blocks transitions initialBlock finalBlock finalObligations
          print . PP.pretty =<< TS.transitionSystemToSally sym TS.mySallyNames ts
          return ()

getGlobInfo ::
  HasPtrWidth (ArchWidth arch) =>
  OnlineSolver scope solver =>
  (?lc :: TypeContext) =>
  Proxy arch ->
  ConcreteSym scope solver ->
  MemImpl (ConcreteSym scope solver) ->
  (TL.Symbol, (TL.Global, Either String (MemType, Maybe LLVMConst))) ->
  IO (Some (GlobalInfo (ConcreteSym scope solver)))
getGlobInfo _ sym mem (TL.Symbol s, (_, e)) =
  case e of
    Right (mt, Just c) ->
      llvmTypeAsRepr mt $ \tp ->
        do
          c' <- constToLLVMVal sym mem c
          rv <- unpackMemValue sym tp c'
          return $ Core.Some $
            GlobalInfo
              { globalSymbol = s,
                globalTypeRepr = tp,
                globalRegValue = rv
              }
    _ -> error "getGlobInfo: encountered badly initialized global"

dumpAssumptions ::
  OnlineSolver scope solver =>
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) ret) ->
  IO ()
dumpAssumptions execState =
  do
    let sym = L.view ctxSymInterface (execStateContext execState)
    assumptions <- Backend.collectAssumptions sym
    putStrLn $ "Assumptions : " ++ show (length assumptions)
    forM_ assumptions $ \assumption ->
      print . PP.pretty . What4.printSymExpr $ L.view labeledPred assumption

proofGoalExpr ::
  ExprBuilder scope st fs ->
  Backend.ProofGoal
    (Backend.LabeledPred (Expr scope BaseBoolType) Backend.AssumptionReason)
    (Backend.LabeledPred (Expr scope BaseBoolType) SimError) ->
  IO (Expr scope BaseBoolType)
proofGoalExpr sym Backend.ProofGoal {..} =
  do
    assumptions <- What4.andAllOf sym L.folded (L.view labeledPred <$> proofAssumptions)
    let conclusion = L.view labeledPred proofGoal
    What4.impliesPred sym assumptions conclusion

dumpObligations ::
  OnlineSolver scope solver =>
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) ret) ->
  IO ()
dumpObligations execState =
  do
    let sym = L.view ctxSymInterface (execStateContext execState)
    obligations <- Backend.proofGoalsToList <$> Backend.getProofObligations sym
    putStrLn $ "Obligations : " ++ show (length obligations)
    forM_ obligations $ \o -> print . What4.printSymExpr =<< proofGoalExpr sym o

dumpMemory ::
  forall arch blocks init m p ret scope solver.
  MonadIO m =>
  MonadReader (MCReader arch blocks init ret) m =>
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) ret) ->
  m ()
dumpMemory execState = do
  llvmCtx <- asks (L.view mcLLVMContext)
  case execStateSimState execState of
    Nothing -> return ()
    Just (SomeSimState simState) ->
      liftIO $ do
        let var = llvmMemVar llvmCtx
        let gs = L.view stateGlobals simState
        case lookupGlobal var gs of
          Nothing -> return ()
          Just m -> doDumpMem stdout m

controlResumptionBlock :: ControlResumption p sym ext rtp f -> Natural
controlResumptionBlock = \case
  ContinueResumption (ResolvedJump bID _) -> blockID bID
  CheckMergeResumption (ResolvedJump bID _) -> blockID bID
  SwitchResumption _ -> error "TODO: SwitchResumption"
  OverrideResumption _ _ -> error "TODO: OverrideResumption"

blockID :: Core.BlockID ctx tp -> Natural
blockID = intToNatural . Ctx.indexVal . Core.blockIDIndex

inspectExecState ::
  forall arch blocks init m p ret scope solver.
  HasPtrWidth (ArchWidth arch) =>
  MonadIO m =>
  MonadReader (MCReader arch blocks init ret) m =>
  MonadState (MCState (ConcreteSym scope solver)) m =>
  OnlineSolver scope solver =>
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) ret) ->
  m ()
-- In the @InitialState@, we are looking for the names of global variables
inspectExecState execState@(InitialState _ gs _ _ _) =
  do
    let sym = L.view ctxSymInterface (execStateContext execState)
    llvmCtx <- asks (L.view mcLLVMContext)
    globInit <- asks (L.view mcGlobInit)
    let ?lc = L.view llvmTypeCtx llvmCtx
    let mem =
          fromMaybe
            (error "Memory was not initialized correctly")
            (lookupGlobal (llvmMemVar llvmCtx) gs)
    globCtx <-
      liftIO $
        Ctx.fromList
          <$> mapM (getGlobInfo (Proxy :: Proxy arch) sym mem) (Map.toList globInit)
    liftIO $ putStrLn "Inspected the initial state and populated the global variables info"
    modify (L.set mcGlobals (Just globCtx))
    return ()
inspectExecState execState@(RunningState (RunBlockStart block) _) =
  do
    liftIO . putStrLn $ "Starting to track block " ++ show block
    modify (setCurrentBlock block)
    -- if this is the first block we encounter, register it as the initial block
    modify (L.over mcInitialBlock (Just . maybe (SomeBlock block) id))
    let bID = blockID block
    let sym = L.view ctxSymInterface (execStateContext execState)
    assumptions <- liftIO $ toList . (L.view labeledPred <$>) <$> Backend.collectAssumptions sym
    obligations <- liftIO $ mapM (proofGoalExpr sym) =<< Backend.proofGoalsToList <$> Backend.getProofObligations sym
    let blockInfo =
          BlockInformation
            { _mcBlockStartAssumptions = assumptions,
              _mcBlockStartObligations = obligations,
              _mcBlockEndAssumptions = [], -- will be filled later
              _mcBlockEndObligations = [] -- will be filled later
            }
    liftIO $ putStrLn $ "INSERTING BLOCK " ++ show bID
    modify
      $ L.over mcBlocksInformation
      $ Map.insert bID blockInfo
inspectExecState execState@(RunningState (RunBlockEnd (Core.Some block)) _) =
  do
    let bID = blockID block
    let sym = L.view ctxSymInterface (execStateContext execState)
    assumptions <- liftIO $ toList . (L.view labeledPred <$>) <$> Backend.collectAssumptions sym
    obligations <- liftIO $ mapM (proofGoalExpr sym) =<< Backend.proofGoalsToList <$> Backend.getProofObligations sym
    modify
      $ L.over mcBlocksInformation
      $ Map.update (Just . L.set mcBlockEndAssumptions assumptions) bID
        . Map.update (Just . L.set mcBlockEndObligations obligations) bID
inspectExecState
  execState@( ControlTransferState
                (CheckMergeResumption (ResolvedJump nextBlock _))
                _
              ) =
    do
      mcState <- get
      fromMaybe
        (liftIO $ putStrLn $ "/!\\ WARNING /!\\ Control Transfer State with no current block!")
        $ withCurrentBlock mcState
        $ \currentBlock ->
          do
            let sym = L.view ctxSymInterface (execStateContext execState)
            registerUnconditionalTransition sym (blockID currentBlock) (blockID nextBlock)
      modify unsetCurrentBlock
inspectExecState execState@(SymbolicBranchState truePred truePath falsePath _mergePoint _) =
  do
    mcState <- get
    fromMaybe
      (liftIO $ putStrLn $ "/!\\ WARNING /!\\ Symbolic Branch State with no current block!")
      $ withCurrentBlock mcState
      $ \currentBlock -> do
        let sym = L.view ctxSymInterface (execStateContext execState)
        falsePred <- liftIO $ What4.notPred sym truePred
        let trueBlock = controlResumptionBlock (resume truePath)
        let falseBlock = controlResumptionBlock (resume falsePath)
        registerConditionalTransition (blockID currentBlock) truePred trueBlock
        registerConditionalTransition (blockID currentBlock) falsePred falseBlock
-- We watch for the very first @CallState@ as it can easily tell us what the
-- initial block of execution will be.
inspectExecState _execState@(CallState _ (CrucibleCall block _) _) =
  do
    modify $ checkAndRegisterInitialBlock block
    return ()
inspectExecState execState =
  do
    if False
      then do
        dumpMemory execState
        liftIO $ dumpAssumptions execState
        liftIO $ dumpObligations execState
        liftIO $ print $ ppExecState execState
      else return ()
    return ()

makeBlock :: (Natural, BlockInformation sym) -> MCBlock sym
makeBlock (iID, info) =
  MCBlock
    { _mcBlockID = iID,
      _mcBlockPres = L.view mcBlockStartAssumptions info,
      _mcBlockPosts = L.view mcBlockEndAssumptions info,
      _mcBlockObligations = L.view mcBlockStartObligations info
    }

stepExecState ::
  forall arch blocks init m p ret scope solver.
  HasPtrWidth (ArchWidth arch) =>
  MonadIO m =>
  MonadReader (MCReader arch blocks init ret) m =>
  MonadState (MCState (ConcreteSym scope solver)) m =>
  OnlineSolver scope solver =>
  Proxy arch ->
  ExecState p (ConcreteSym scope solver) (LLVM arch) (RegEntry (ConcreteSym scope solver) ret) ->
  m (TransitionSystemInfo (ConcreteSym scope solver) ret)
stepExecState proxy execState =
  do
    liftIO $ print $ ppExecState execState
    inspectExecState execState
    case execState of
      -- In the result state, we can obtain the return value of the program, and
      -- build the transition system information.
      ResultState (FinishedResult ctx (TotalRes gp)) ->
        do
          -- FIXME: this assumes that there is a single returning block, which I
          -- am not sure is true
          s <- get
          let finalBlock =
                fromMaybe
                  (error "Reached the ResultState with no current block set")
                  (withCurrentBlock s blockID)
          let initialBlock =
                fromMaybe
                  (error "Reached the ResultState with no initial block set")
                  (withInitialBlock s blockID)
          let sym = L.view ctxSymInterface ctx
          finalObligations <- liftIO $ mapM (proofGoalExpr sym) =<< Backend.proofGoalsToList <$> Backend.getProofObligations sym
          globalStateInfo <-
            fromMaybe (error "No global state info was registered")
              <$> gets (L.view mcGlobals)
          cfg <- asks (L.view mcCFG)
          let functionArguments = Core.cfgArgTypes cfg
          blocksInfo <- gets (L.view mcBlocksInformation)
          let blocks = makeBlock <$> Map.toList blocksInfo
          transitions <- gets (L.view mcTransitions)
          return $
            TransitionSystemInfo
              { blocks,
                finalBlock,
                finalObligations,
                functionArguments = Core.Some functionArguments,
                initialBlock,
                globalStateInfo,
                returnValue = L.view gpValue gp,
                transitions
              }
      -- for any non-result state, we just keep stepping forward
      _ ->
        do
          nextExecState <- liftIO $ do
            -- _ <- getLine
            singleStepCrucible 0 execState
          stepExecState proxy nextExecState

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
