{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module SAWScript.LLVMMethodSpec
  ( ValidationPlan(..)
  , LLVMMethodSpecIR
  , specFunction
  , specName
  , specValidationPlan
  , SymbolicRunHandler
  , initializeVerification
  , runValidation
  , mkSpecVC
  , ppPathVC
  , scLLVMValue
  , VerifyParams(..)
  , VerifyState(..)
  , EvalContext(..)
  , ExpectedStateDef(..)
  ) where

import Control.Applicative hiding (empty)
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Error (ErrorT, runErrorT, MonadError) -- , throwError)
import Control.Monad.State
import qualified Data.ABC as ABC
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Text.PrettyPrint.Leijen hiding ((<$>))

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.LLVMExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.LLVMMethodSpecIR
import SAWScript.Proof

import Verifier.LLVM.Simulator hiding (State)
import Verifier.LLVM.Simulator.Internals hiding (State)
import Verifier.LLVM.Codebase
-- import Verifier.LLVM.Codebase.AST
import Verifier.LLVM.Backend hiding (asBool)
import Verifier.LLVM.Backend.SAW
import Verinf.Symbolic (Lit)
import Verinf.Utils.LogMonad

import Verifier.SAW.Evaluator
-- import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm hiding (Ident)
import Verifier.SAW.TypedAST hiding (Ident)

type SpecBackend = SAWBackend LSSCtx
type SpecPathState = Path SpecBackend
type SpecLLVMValue = SharedTerm LSSCtx

storePathState :: SBE SpecBackend
               -> SharedTerm LSSCtx
               -> MemType
               -> SharedTerm LSSCtx
               -> SpecPathState
               -> IO SpecPathState
storePathState sbe dst tp val ps = do
  (c, m') <- sbeRunIO sbe (memStore sbe (ps ^. pathMem) dst tp val 0)
  ps' <- addAssertion sbe c ps
  -- FIXME: don't discard ps'!
  return (ps & pathMem .~ m')

loadPathState :: SBE SpecBackend
              -> SharedTerm LSSCtx
              -> MemType
              -> SpecPathState
              -> IO SpecLLVMValue
loadPathState sbe src tp ps = do
  (c, v) <- sbeRunIO sbe (memLoad sbe (ps ^. pathMem) tp src 0)
  ps' <- addAssertion sbe c ps
  -- FIXME: don't discard ps'!
  return v

loadGlobal :: SBE SpecBackend
           -> GlobalMap SpecBackend
           -> Symbol
           -> MemType
           -> SpecPathState
           -> IO SpecLLVMValue
loadGlobal sbe gm sym tp ps = do
  case Map.lookup sym gm of
    Just addr -> loadPathState sbe addr tp ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

storeGlobal :: SBE SpecBackend
            -> GlobalMap SpecBackend
            -> Symbol
            -> MemType
            -> SpecLLVMValue
            -> SpecPathState
            -> IO SpecPathState
storeGlobal sbe gm sym tp v ps = do
  case Map.lookup sym gm of
    Just addr -> storePathState sbe addr tp v ps
    Nothing -> fail $ "Global " ++ show sym ++ " not found"

-- | Add assumption for predicate to path state.
addAssumption :: SBE SpecBackend -> SharedTerm LSSCtx -> SpecPathState -> IO SpecPathState
addAssumption sbe x p = do
  p & pathAssertions %%~ \a -> liftIO (sbeRunIO sbe (applyAnd sbe a x))

-- | Add assertion for predicate to path state.
addAssertion :: SBE SpecBackend -> SharedTerm LSSCtx -> SpecPathState -> IO SpecPathState
addAssertion sbe x p = do
  -- TODO: p becomes an additional VC in this case
  p & pathAssertions %%~ \a -> liftIO (sbeRunIO sbe (applyAnd sbe a x))

-- | Contextual information needed to evaluate expressions.
data EvalContext
  = EvalContext {
      ecContext :: SharedContext LSSCtx
    , ecBackend :: SBE SpecBackend
    , ecGlobalMap :: GlobalMap SpecBackend
    , ecArgs :: [(Ident, SharedTerm LSSCtx)]
    , ecPathState :: SpecPathState
    , ecLLVMExprs :: Map String (TC.LLVMActualType, TC.LLVMExpr)
    }

evalContextFromPathState :: Map String (TC.LLVMActualType, TC.LLVMExpr)
                         -> SharedContext LSSCtx
                         -> SBE SpecBackend
                         -> GlobalMap SpecBackend
                         -> SpecPathState
                         -> EvalContext
evalContextFromPathState m sc sbe gm ps
  = EvalContext {
      ecContext = sc
    , ecBackend = sbe
    , ecGlobalMap = gm
    , ecArgs = case ps ^.. pathCallFrames of
                 f:_ -> cfArgValues f
                 [] -> error "empty call stack"
    , ecPathState = ps
    , ecLLVMExprs = m
    }

type ExprEvaluator a = ErrorT TC.LLVMExpr IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either TC.LLVMExpr b)
runEval v = liftIO (runErrorT v)

-- | Evaluate an LLVM expression, and return its value (r-value) as an
-- internal term.
evalLLVMExpr :: (MonadIO m) => TC.LLVMExpr -> EvalContext -> m SpecLLVMValue
evalLLVMExpr expr ec = eval expr
  where eval e@(CC.Term app) =
          case app of
            TC.Arg _ n _ ->
              case lookup n (ecArgs ec) of
                Just v -> return v
                Nothing -> fail $ "evalLLVMExpr: argument not found: " ++ show e
            TC.Global n tp -> do
              liftIO $ loadGlobal sbe (ecGlobalMap ec) n tp ps
            TC.Deref ae tp -> do
              addr <- evalLLVMExpr ae ec
              liftIO $ loadPathState sbe addr tp ps
            TC.StructField _ _ _ _ -> fail "struct fields not yet supported" -- TODO
        sbe = ecBackend ec
        ps = ecPathState ec

-- | Evaluate an LLVM expression, and return the location it describes
-- (l-value) as an internal term.
evalLLVMRefExpr :: (MonadIO m) => TC.LLVMExpr -> EvalContext -> m SpecLLVMValue
evalLLVMRefExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.Arg _ _ _ -> fail "evalLLVMRefExpr: applied to argument"
            TC.Global n _ -> do
              case Map.lookup n gm of
                Just addr -> return addr
                Nothing -> fail $ "evalLLVMRefExpr: global " ++ show n ++ " not found"
            TC.Deref ae _ -> evalLLVMExpr ae ec
            TC.StructField _ _ _ _ -> fail "struct fields not yet supported" -- TODO
        gm = ecGlobalMap ec

evalDerefLLVMExpr :: (MonadIO m) => TC.LLVMExpr -> EvalContext -> m (SharedTerm LSSCtx)
evalDerefLLVMExpr expr ec = do
  val <- evalLLVMExpr expr ec
  case TC.lssTypeOfLLVMExpr expr of
    PtrType (MemType tp) -> liftIO $
      loadPathState (ecBackend ec) val tp (ecPathState ec)
    PtrType _ -> fail "Pointer to weird type."
    _ -> return val

-- | Build the application of LLVM.mkValue to the given string.
scLLVMValue :: SharedContext s -> SharedTerm s -> String -> IO (SharedTerm s)
scLLVMValue sc ty name = do
  s <- scString sc name
  ty' <- scRemoveBitvector sc ty
  mkValue <- scGlobalDef sc (parseIdent "LLVM.mkValue")
  nt <- scApplyAll sc mkValue [ty', s]
  return nt

-- | Evaluate a typed expression in the context of a particular state.
evalLogicExpr :: (MonadIO m) => TC.LogicExpr -> EvalContext -> m SpecLLVMValue
evalLogicExpr initExpr ec = do
  let sc = ecContext ec
  t <- liftIO $ TC.useLogicExpr sc initExpr
  rules <- forM (Map.toList (ecLLVMExprs ec)) $ \(name, (at, expr)) ->
             do lt <- evalLLVMExpr expr ec
                 -- TODO: error handling!
                Just ty <- liftIO $ TC.logicTypeOfActual sc at
                nt <- liftIO $ scLLVMValue sc ty name
                return (ruleOfTerms nt lt)
  let ss = addRules rules emptySimpset
  liftIO $ rewriteSharedTerm sc ss t

-- | Return Java value associated with mixed expression.
evalMixedExpr :: (MonadIO m) =>
                 TC.MixedExpr -> EvalContext
              -> m SpecLLVMValue
evalMixedExpr (TC.LogicE expr) ec = evalLogicExpr expr ec
evalMixedExpr (TC.LLVME expr) ec = evalLLVMExpr expr ec

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         ocsLoc :: SymBlockID
       , ocsEvalContext :: !EvalContext
       , ocsResultState :: !SpecPathState
       , ocsReturnValue :: !(Maybe (SharedTerm LSSCtx))
       , ocsErrors :: [OverrideError]
       }

data OverrideError
   = UndefinedExpr TC.LLVMExpr
   | FalseAssertion Pos
   | AliasingInputs !TC.LLVMExpr !TC.LLVMExpr
   | SimException String
   | Abort
   deriving (Show)

ppOverrideError :: OverrideError -> String
ppOverrideError (UndefinedExpr expr) =
  "Could not evaluate " ++ show (TC.ppLLVMExpr expr) ++ "."
ppOverrideError (FalseAssertion p)   = "Assertion at " ++ show p ++ " is false."
ppOverrideError (AliasingInputs x y) =
 "The expressions " ++ show (TC.ppLLVMExpr x) ++ " and " ++ show (TC.ppLLVMExpr y)
    ++ " point to the same memory location, but are not allowed to alias each other."
ppOverrideError (SimException s)     = "Simulation exception: " ++ s ++ "."
ppOverrideError Abort                = "Path was aborted."

data OverrideResult
   = SuccessfulRun SpecPathState (Maybe SymBlockID) (Maybe SpecLLVMValue)
   | FalseAssumption
   | FailedRun SpecPathState (Maybe SymBlockID) [OverrideError]

type RunResult = ( SpecPathState
                 , Maybe SymBlockID
                 , Either [OverrideError] (Maybe SpecLLVMValue)
                 )

orParseResults :: [OverrideResult] -> [RunResult]
orParseResults l =
  [ (ps, block, Left  e) | FailedRun     ps block e <- l ] ++
  [ (ps, block, Right v) | SuccessfulRun ps block v <- l ]

type OverrideComputation = ContT OverrideResult (StateT OCState IO)

ocError :: OverrideError -> OverrideComputation ()
ocError e = modify $ \ocs -> ocs { ocsErrors = e : ocsErrors ocs }

ocAssumeFailed :: OverrideComputation a
ocAssumeFailed = ContT (\_ -> return FalseAssumption)

-- | Runs an evaluate within an override computation.
ocEval :: (EvalContext -> ExprEvaluator b)
       -> (b -> OverrideComputation ())
       -> OverrideComputation ()
ocEval fn m = do
  ec <- gets ocsEvalContext
  res <- runEval (fn ec)
  case res of
    Left expr -> ocError $ UndefinedExpr expr
    Right v   -> m v

-- Modify result state
{-
ocModifyResultState :: (SpecPathState -> SpecPathState) -> OverrideComputation ()
ocModifyResultState fn = do
  bcs <- get
  put $! bcs { ocsResultState = fn (ocsResultState bcs) }
-}

ocModifyResultStateIO :: (SpecPathState -> IO SpecPathState)
                      -> OverrideComputation ()
ocModifyResultStateIO fn = do
  bcs <- get
  new <- liftIO $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

-- | Add assumption for predicate.
ocAssert :: Pos -> String -> SharedTerm LSSCtx -> OverrideComputation ()
ocAssert p _nm x = do
  sbe <- (ecBackend . ocsEvalContext) <$> get
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultStateIO (addAssertion sbe x)

ocStep :: BehaviorCommand -> OverrideComputation ()
ocStep (AssertPred pos expr) =
  ocEval (evalLogicExpr expr) $ \p ->
    ocAssert pos "Override predicate" p
ocStep (AssumePred expr) = do
  sbe <- gets (ecBackend . ocsEvalContext)
  ocEval (evalLogicExpr expr) $ \v ->
    case asBool v of
      Just True -> return ()
      Just False -> ocAssumeFailed
      _ -> ocModifyResultStateIO $ addAssumption sbe v
ocStep (Ensure _pos lhsExpr rhsExpr) = do
  sbe <- gets (ecBackend . ocsEvalContext)
  ocEval (evalLLVMRefExpr lhsExpr) $ \lhsRef ->
    ocEval (evalMixedExpr rhsExpr) $ \value -> do
      let tp = TC.lssTypeOfLLVMExpr lhsExpr
      ocModifyResultStateIO $
        storePathState sbe lhsRef tp value
ocStep (Modify lhsExpr tp) = do
  sbe <- gets (ecBackend . ocsEvalContext)
  sc <- gets (ecContext . ocsEvalContext)
  ocEval (evalLLVMRefExpr lhsExpr) $ \lhsRef -> do
    Just lty <- liftIO $ TC.logicTypeOfActual sc tp
    value <- liftIO $ scFreshGlobal sc "_" lty
    ocModifyResultStateIO $
      storePathState sbe lhsRef tp value
ocStep (Return expr) = do
  ocEval (evalMixedExpr expr) $ \val ->
    modify $ \ocs -> ocs { ocsReturnValue = Just val }

execBehavior :: [BehaviorSpec] -> EvalContext -> SpecPathState -> IO [RunResult]
execBehavior bsl ec ps = do
  -- Get state of current execution path in simulator.
  fmap orParseResults $ forM bsl $ \bs -> do
    let initOCS =
          OCState { ocsLoc = bsLoc bs
                  , ocsEvalContext = ec
                  , ocsResultState = ps
                  , ocsReturnValue = Nothing
                  , ocsErrors = []
                  }
    let resCont () = do
          OCState { ocsLoc = loc
                  , ocsResultState = resPS
                  , ocsReturnValue = v
                  , ocsErrors = l } <- get
          return $
            if null l then
              SuccessfulRun resPS (Just loc) v
            else
              FailedRun resPS (Just loc) l
    flip evalStateT initOCS $ flip runContT resCont $ do
       let sc = ecContext ec
       -- Verify the initial logic assignments
       forM_ (Map.toList (bsExprDecls bs)) $ \(lhs, (_ty, mrhs)) ->
         case mrhs of
           Just rhs -> do
             ocEval (evalDerefLLVMExpr lhs) $ \lhsVal ->
               ocEval (evalLogicExpr rhs) $ \rhsVal ->
                 ocAssert (PosInternal "FIXME") "Override value assertion"
                    =<< liftIO (scEq sc lhsVal rhsVal)
           Nothing -> return ()
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

execOverride :: (MonadIO m, Functor m) =>
                SharedContext LSSCtx
             -> Pos
             -> LLVMMethodSpecIR
             -> [(MemType, SpecLLVMValue)]
             -> Simulator SpecBackend m (Maybe (SharedTerm LSSCtx))
execOverride sc pos ir args = do
  initPS <- fromMaybe (error "no path during override") <$> getPath
  let bsl = specBehavior ir
  let func = specFunction ir
      cb = specCodebase ir
      Just funcDef = lookupDefine func cb
  sbe <- gets symBE
  gm <- use globalTerms
  let ec = EvalContext { ecContext = sc
                       , ecBackend = sbe
                       , ecGlobalMap = gm
                       , ecArgs = zip (map fst (sdArgs funcDef)) (map snd args)
                       , ecPathState = initPS
                       , ecLLVMExprs = specLLVMExprNames ir
                       }
  res <- liftIO $ execBehavior [bsl] ec initPS
  case res of
    [(_, _, Left el)] -> do
      let msg = vcat [ hcat [ text "Unsatisified assertions in "
                            , specName ir
                            , char ':'
                            ]
                     , vcat (map (text . ppOverrideError) el)
                     ]
      -- TODO: turn this message into a proper exception
      fail (show msg)
    [(_, _, Right mval)] -> return mval
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: (MonadIO m, Functor m) =>
                    SharedContext LSSCtx
                 -> Pos
                 -> LLVMMethodSpecIR
                 -> Simulator SpecBackend m ()
overrideFromSpec sc pos ir = do
  let ovd = Override (\_ _ -> execOverride sc pos ir)
  -- TODO: check argument types?
  tryRegisterOverride (specFunction ir) (const (Just ovd))

-- | Describes expected result of computation.
data ExpectedStateDef = ESD {
         -- | Location that we started from.
         esdStartLoc :: SymBlockID
         -- | Initial path state (used for evaluating expressions in
         -- verification).
       , esdBackend :: SBE SpecBackend
       , esdGlobalMap :: GlobalMap SpecBackend
       , esdInitialPathState :: SpecPathState
         -- | Stores initial assignments.
       , esdInitialAssignments :: [(TC.LLVMExpr, SpecLLVMValue)]
         -- | Expected return value or Nothing if method returns void.
       , esdReturnValue :: Maybe SpecLLVMValue
       }

esdArgs :: ExpectedStateDef -> [(Ident, SpecLLVMValue)]
esdArgs = mapMaybe getArg . esdInitialAssignments
  where
    getArg (CC.Term (TC.Arg _ nm _), v) = Just (nm, v)
    getArg _ = Nothing

-- | State for running the behavior specifications in a method override.
data ESGState = ESGState {
         esContext :: SharedContext LSSCtx
       , esBackend :: SBE SpecBackend
       , esGlobalMap :: GlobalMap SpecBackend
       , esLLVMExprs :: Map String (TC.LLVMActualType, TC.LLVMExpr)
       , esInitialAssignments :: [(TC.LLVMExpr, SpecLLVMValue)]
       , esInitialPathState :: SpecPathState
       , esReturnValue :: Maybe SpecLLVMValue
       }

-- | Monad used to execute statements in a behavior specification for a method
-- override.
type ExpectedStateGenerator = StateT ESGState IO

esEval :: (EvalContext -> ExprEvaluator b) -> ExpectedStateGenerator b
esEval fn = do
  sc <- gets esContext
  m <- gets esLLVMExprs
  sbe <- gets esBackend
  gm <- gets esGlobalMap
  initPS <- gets esInitialPathState
  let ec = evalContextFromPathState m sc sbe gm initPS
  res <- runEval (fn ec)
  case res of
    Left expr -> fail $ "internal: esEval given " ++ show expr ++ "."
    Right v   -> return v

esGetInitialPathState :: ExpectedStateGenerator SpecPathState
esGetInitialPathState = gets esInitialPathState

esPutInitialPathState :: SpecPathState -> ExpectedStateGenerator ()
esPutInitialPathState ps = modify $ \es -> es { esInitialPathState = ps }

{-
esModifyInitialPathState :: (SpecPathState -> SpecPathState)
                         -> ExpectedStateGenerator ()
esModifyInitialPathState fn =
  modify $ \es -> es { esInitialPathState = fn (esInitialPathState es) }
-}

esModifyInitialPathStateIO :: (SpecPathState -> IO SpecPathState)
                         -> ExpectedStateGenerator ()
esModifyInitialPathStateIO fn =
  do s0 <- esGetInitialPathState
     esPutInitialPathState =<< liftIO (fn s0)

{-
esAddEqAssertion :: SBE SpecBackend -> String -> SharedTerm LSSCtx -> SharedTerm LSSCtx
                 -> ExpectedStateGenerator ()
esAddEqAssertion sbe _nm x y =
  do sc <- gets esContext
     prop <- liftIO (scEq sc x y)
     esModifyInitialPathStateIO (addAssertion sbe prop)

-- | Assert that two terms are equal.
esAssertEq :: String -> SpecLLVMValue -> SpecLLVMValue
           -> ExpectedStateGenerator ()
esAssertEq nm x y = do
  sbe <- gets esBackend
  esAddEqAssertion sbe nm x y
-}

-- | Set value in initial state.
esSetLLVMValue :: TC.LLVMExpr -> SpecLLVMValue -> ExpectedStateGenerator ()
esSetLLVMValue (CC.Term exprF) v = do
  case exprF of
    TC.Global n tp -> do
      sbe <- gets esBackend
      gm <- gets esGlobalMap
      ps <- esGetInitialPathState
      ps' <- liftIO $ storeGlobal sbe gm n tp v ps
      esPutInitialPathState ps'
    TC.Arg _ _ _ -> fail "Can't set the value of arguments."
    TC.Deref addrExp tp -> do
      assgns <- gets esInitialAssignments
      sbe <- gets esBackend
      case lookup addrExp assgns of
        Just addr -> do
          ps <- esGetInitialPathState
          ps' <- liftIO $ storePathState sbe addr tp v ps
          esPutInitialPathState ps'
        Nothing -> fail "internal: esSetLLVMValue on address not assigned a value"
    -- TODO: the following is ugly, and doesn't make good use of lenses
    TC.StructField _ _ _ _ -> fail "Can't set the value of structure fields."

createLogicValue :: Codebase SpecBackend
                 -> SBE SpecBackend
                 -> SharedContext LSSCtx
                 -> SpecPathState
                 -> MemType
                 -> Maybe TC.LogicExpr
                 -> IO (SpecLLVMValue, SpecPathState)
createLogicValue cb _ sc _ (PtrType _) (Just _) =
  fail "Pointer variables cannot be given initial values."
createLogicValue cb sbe sc ps (PtrType (MemType mtp)) _ = do
  let dl = cbDataLayout cb
      sz = memTypeSize dl mtp
      w = ptrBitwidth dl
  let m = ps ^. pathMem
  szTm <- scBvConst sc (fromIntegral w) (fromIntegral sz)
  rslt <- sbeRunIO sbe (heapAlloc sbe m mtp w szTm 0)
  case rslt of
    AError msg -> fail msg
    AResult c addr m' -> do
      ps' <- addAssertion sbe c (ps & pathMem .~ m')
      mbltp <- TC.logicTypeOfActual sc mtp
      case mbltp of
        Just ty -> do
          v <- scFreshGlobal sc "_" ty
          ps'' <- storePathState sbe addr mtp v ps'
          return (addr, ps'')
createLogicValue cb _ sc ps mtp mrhs = do
  mbltp <- TC.logicTypeOfActual sc mtp
  -- Get value of rhs.
  tm <- case (mrhs, mbltp) of
          (Just v, _) -> TC.useLogicExpr sc v
          (Nothing, Just tp) -> scFreshGlobal sc "_" tp
          (Nothing, Nothing) -> fail "Can't calculate type for fresh input."
  return (tm, ps)

esSetLogicValue :: Codebase SpecBackend
                -> SharedContext LSSCtx
                -> TC.LLVMExpr
                -> MemType
                -> Maybe TC.LogicExpr
                -> ExpectedStateGenerator ()
-- Skip arguments because we've already done them. A bit of a hack.
esSetLogicValue _ _ (CC.Term (TC.Arg _ _ _)) _ Nothing = return ()
esSetLogicValue cb sc expr mtp mrhs = do
  sbe <- gets esBackend
  ps <- gets esInitialPathState
  -- Create the value to associate with this LLVM expression: either
  -- an assigned value or a fresh input.
  (value, ps') <- liftIO $ createLogicValue cb sbe sc ps mtp mrhs
  -- Update the initial assignments in the expected state.
  modify $ \es -> es { esInitialAssignments =
                         (expr, value) : esInitialAssignments es }
  -- Update the LLVM value in the stored path state.
  esSetLLVMValue expr value

esStep :: BehaviorCommand -> ExpectedStateGenerator ()
esStep (AssertPred _ expr) = do
  sbe <- gets esBackend
  v <- esEval $ evalLogicExpr expr
  esModifyInitialPathStateIO $ addAssumption sbe v
esStep (AssumePred expr) = do
  sbe <- gets esBackend
  v <- esEval $ evalLogicExpr expr
  esModifyInitialPathStateIO $ addAssumption sbe v
esStep (Return expr) = do
  v <- esEval $ evalMixedExpr expr
  modify $ \es -> es { esReturnValue = Just v }
esStep (Ensure _pos lhsExpr rhsExpr) = do
  sbe <- gets esBackend
  ref    <- esEval $ evalLLVMRefExpr lhsExpr
  value  <- esEval $ evalMixedExpr rhsExpr
  let tp = TC.lssTypeOfLLVMExpr lhsExpr
  esModifyInitialPathStateIO $
    storePathState sbe ref tp value
esStep (Modify lhsExpr tp) = do
  sbe <- gets esBackend
  sc <- gets esContext
  ref <- esEval $ evalLLVMRefExpr lhsExpr
  Just lty <- liftIO $ TC.logicTypeOfActual sc tp
  value <- liftIO $ scFreshGlobal sc "_" lty
  esModifyInitialPathStateIO $
    storePathState sbe ref tp value

-- | Initialize verification of a given 'LLVMMethodSpecIR'. The design
-- principles for now include:
-- 
--   * All pointers must be concrete and distinct
--
--   * All types must be of known size
--
--   * Values pointed to become fresh variables, unless initialized by
--     assertions
initializeVerification :: (MonadIO m, Functor m) =>
                          SharedContext LSSCtx
                       -> LLVMMethodSpecIR
                       -> Simulator SpecBackend m ExpectedStateDef
initializeVerification sc ir = do
  let exprs = specLLVMExprNames ir
      bs = specBehavior ir
      fn = specFunction ir
      cb = specCodebase ir
      Just fnDef = lookupDefine fn (specCodebase ir)
      isArgAssgn (CC.Term (TC.Arg _ _ _), _) = True
      isArgAssgn _ = False
      isPtrAssgn (e, _) = TC.isPtrLLVMExpr e
      assignments = map getAssign $ Map.toList (bsExprDecls bs)
      getAssign (e, (_, v)) = (e, v)
      argAssignments = filter isArgAssgn assignments
      ptrAssignments = filter isPtrAssgn assignments
      otherAssignments =
        filter (\a -> not (isArgAssgn a || isPtrAssgn a)) assignments
      setPS ps = do
        Just cs <- use ctrlStk
        ctrlStk ?= (cs & currentPath .~ ps)

  sbe <- gets symBE
  -- Create argument list. For pointers, allocate enough space to
  -- store the pointed-to value. For scalar and array types,
  -- initialize this space to a fresh input. For structures, wait
  -- until later to initialize the fields.
  argAssignments' <- forM argAssignments $ \(expr, mle) ->
    case (expr, mle) of
      (CC.Term (TC.Arg i _ ty), Just _) -> fail "argument assignments not allowed"
      (CC.Term (TC.Arg i _ ty), Nothing) -> do
        ps <- fromMaybe (error "initializeVerification") <$> getPath
        (tm, ps') <- liftIO $ createLogicValue cb sbe sc ps ty mle
        setPS ps'
        return (Just (expr, tm))
      _ -> return Nothing

  let argAssignments'' = catMaybes argAssignments'

  let args = flip map argAssignments'' $ \(expr, mle) ->
               case (expr, mle) of
                 (CC.Term (TC.Arg i _ ty), tm) ->
                   Just (i, (ty, tm))
                 _ -> Nothing

  gm <- use globalTerms
  let rreg =  (,Ident "__sawscript_result") <$> sdRetType fnDef
      cmpFst (i, _) (i', _) = i `compare` i'
  callDefine' False fn rreg (map snd (sortBy cmpFst (catMaybes args)))

  initPS <- fromMaybe (error "initializeVerification") <$> getPath
  let initESG = ESGState { esContext = sc
                         , esBackend = sbe
                         , esGlobalMap = gm
                         , esLLVMExprs = exprs
                         , esInitialAssignments = argAssignments''
                         , esInitialPathState = initPS
                         , esReturnValue = Nothing
                         }

  es <- liftIO $ flip execStateT initESG $ do
    -- Allocate space for all pointers that aren't directly parameters.
    forM_ ptrAssignments $ \(expr, v) -> do
      let Just (mtp, _) = Map.lookup expr (bsExprDecls bs)
      esSetLogicValue cb sc expr mtp v
    -- Set initial logic values for everything except arguments and
    -- pointers, including values pointed to by pointers from directly
    -- above, and fields of structures from anywhere.
    forM_ otherAssignments $ \(expr, v) -> do
      let Just (mtp, _) = Map.lookup expr (bsExprDecls bs)
      esSetLogicValue cb sc expr mtp v
    -- Process commands
    mapM esStep (bsCommands bs)

  Just cs <- use ctrlStk
  ctrlStk ?= (cs & currentPath .~ esInitialPathState es)

  return ESD { esdStartLoc = bsLoc bs
             , esdBackend = sbe
             , esdGlobalMap = gm
             , esdInitialPathState = esInitialPathState es
             , esdInitialAssignments = reverse (esInitialAssignments es)
             , esdReturnValue = esReturnValue es
             }

data VerificationCheck
  = AssertionCheck String (SharedTerm LSSCtx) -- ^ Name of assertion.
  -- | Check that equalitassertion is true.
  | EqualityCheck String -- ^ Name of value to compare
                  (SharedTerm LSSCtx) -- ^ Value returned by JVM symbolic simulator.
                  (SharedTerm LSSCtx) -- ^ Expected value in Spec.
  -- deriving (Eq, Ord, Show)

vcName :: VerificationCheck -> String
vcName (AssertionCheck nm _) = nm
vcName (EqualityCheck nm _ _) = nm

-- | Returns goal that one needs to prove.
vcGoal :: SharedContext LSSCtx -> VerificationCheck -> IO (SharedTerm LSSCtx)
vcGoal _ (AssertionCheck _ n) = return n
vcGoal sc (EqualityCheck _ x y) = scEq sc x y

type CounterexampleFn = (SharedTerm LSSCtx -> IO Value) -> IO Doc

-- | Returns documentation for check that fails.
vcCounterexample :: VerificationCheck -> CounterexampleFn
vcCounterexample (AssertionCheck nm n) _ =
  return $ text ("Assertion " ++ nm ++ " is unsatisfied:") <+> scPrettyTermDoc n
vcCounterexample (EqualityCheck nm lssNode specNode) evalFn =
  do ln <- evalFn lssNode
     sn <- evalFn specNode
     return (text nm <$$>
        nest 2 (text $ "Encountered: " ++ show ln) <$$>
        nest 2 (text $ "Expected:    " ++ show sn))

-- | Describes the verification result arising from one symbolic execution path.
data PathVC = PathVC {
          pvcStartLoc :: SymBlockID
        , pvcEndLoc :: Maybe SymBlockID
        , pvcInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
          -- | Assumptions on inputs.
        , pvcAssumptions :: SharedTerm LSSCtx
          -- | Static errors found in path.
        , pvcStaticErrors :: [Doc]
          -- | What to verify for this result.
        , pvcChecks :: [VerificationCheck]
        }

ppPathVC :: PathVC -> Doc
ppPathVC pvc =
  nest 2 $
  vcat [ text "Path VC:"
       , nest 2 $ vcat $
         text "Initial assignments:" :
         map ppAssignment (pvcInitialAssignments pvc)
       , nest 2 $
         vcat [ text "Assumptions:"
              , scPrettyTermDoc (pvcAssumptions pvc)
              ]
       , nest 2 $ vcat $
         text "Static errors:" :
         pvcStaticErrors pvc
       , nest 2 $ vcat $
         text "Checks:" :
         map ppCheck (pvcChecks pvc)
       ]
  where ppAssignment (expr, tm) = hsep [ TC.ppLLVMExpr expr
                                       , text ":="
                                       , scPrettyTermDoc tm
                                       ]
        ppCheck (AssertionCheck nm tm) =
          hsep [ text (nm ++ ":")
               , scPrettyTermDoc tm
               ]
        ppCheck (EqualityCheck nm tm tm') =
          hsep [ text (nm ++ ":")
               , scPrettyTermDoc tm
               , text ":="
               , scPrettyTermDoc tm'
               ]

type PathVCGenerator m = StateT PathVC (Simulator SpecBackend m)

-- | Add verification condition to list.
pvcgAssertEq :: (Monad m) =>
                String -> SharedTerm LSSCtx -> SharedTerm LSSCtx -> PathVCGenerator m ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: (Monad m) =>
              String -> SharedTerm LSSCtx -> PathVCGenerator m ()
pvcgAssert nm v =
  modify $ \pvc -> pvc { pvcChecks = AssertionCheck nm v : pvcChecks pvc }

pvcgFail :: Monad m =>
            Doc -> PathVCGenerator m ()
pvcgFail msg =
  modify $ \pvc -> pvc { pvcStaticErrors = msg : pvcStaticErrors pvc }

-- | Compare result with expected state.
generateVC :: (MonadIO m) =>
              SharedContext LSSCtx
           -> LLVMMethodSpecIR
           -> ExpectedStateDef -- ^ What is expected
           -> RunResult -- ^ Results of symbolic execution.
           -> Simulator SpecBackend m PathVC
generateVC sc ir esd (ps, endLoc, res) = do
  let initState  =
        PathVC { pvcInitialAssignments = esdInitialAssignments esd
               , pvcStartLoc = esdStartLoc esd
               , pvcEndLoc = endLoc
               , pvcAssumptions = ps ^. pathAssertions
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  flip execStateT initState $ do
    case res of
      Left oe -> pvcgFail (vcat (map (ftext . ppOverrideError) oe))
      Right maybeRetVal -> do
        -- Check return value
        case (maybeRetVal, esdReturnValue esd) of
          (Nothing,Nothing) -> return ()
          (Just rv, Just srv) -> pvcgAssertEq "return value" rv srv
          (Just _, Nothing) -> fail "simulator returned value when not expected"
          (Nothing, Just _) -> fail "simulator did not return value when expected"

        -- For all expressions mentioned in the spec, check that they
        -- have the same value in the expected and actual states.
        forM_ (bsExprs (specBehavior ir)) $ \e -> case e of
          (CC.Term (TC.Arg _ _ _)) -> return () -- Don't need to compare values of arguments
          _ -> do
            let sbe = esdBackend esd
                eps = esdInitialPathState esd
                m = specLLVMExprNames ir
                gm = esdGlobalMap esd
                expectedContext = evalContextFromPathState m sc sbe gm eps
                actualContext =
                  EvalContext { ecContext = sc
                              , ecBackend = sbe
                              , ecGlobalMap = gm
                              , ecArgs = esdArgs esd
                              , ecPathState = ps
                              , ecLLVMExprs = m
                              }
            expectedValue <- runEval (evalLLVMExpr e expectedContext)
            actualValue <- runEval (evalLLVMExpr e actualContext)
            case (expectedValue, actualValue) of
              (Right ev, Right av) -> pvcgAssertEq (show e) av ev
              (Left err, _) -> fail $ show err
              (_, Left err) -> fail $ show err
        -- Check assertions
        pvcgAssert "final assertions" (ps ^. pathAssertions)

mkSpecVC :: (MonadIO m, Functor m, MonadException m) =>
            SharedContext LSSCtx
         -> VerifyParams
         -> ExpectedStateDef
         -> Simulator SpecBackend m [PathVC]
mkSpecVC sc params esd = do
  let ir = vpSpec params
  -- Log execution.
  setVerbosity (simVerbose (vpOpts params))
  -- Add method spec overrides.
  mapM_ (overrideFromSpec sc (specPos ir)) (vpOver params)
  -- Execute code.
  run
  returnVal <- getProgramReturnValue
  ps <- fromMaybe (error "no path in mkSpecVC") <$> getPath
  -- TODO: handle exceptional or breakpoint terminations
  mapM (generateVC sc ir esd) [(ps, Nothing, Right returnVal)]

data VerifyParams = VerifyParams
  { vpCode    :: Codebase (SAWBackend LSSCtx)
  , vpContext :: SharedContext LSSCtx
  , vpOpts    :: Options
  , vpSpec    :: LLVMMethodSpecIR
  , vpOver    :: [LLVMMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext LSSCtx -> ExpectedStateDef -> [PathVC] -> IO ()
type Prover =
  VerifyState -> ProofScript SAWCtx () -> SharedTerm LSSCtx -> IO ()

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc esd results = do
  let ir = vpSpec params
      verb = verbLevel (vpOpts params)
      ps = esdInitialPathState esd
      m = specLLVMExprNames ir
      sbe = esdBackend esd
      gm = esdGlobalMap esd
  case specValidationPlan ir of
    Skip -> putStrLn $ "WARNING: skipping verification of " ++
                       show (specFunction ir)
    RunVerify script -> do
      forM_ results $ \pvc -> do
        let mkVState nm cfn =
              VState { vsVCName = nm
                     , vsMethodSpec = ir
                     , vsVerbosity = verb
                     -- , vsFromBlock = esdStartLoc esd
                     , vsEvalContext = evalContextFromPathState m sc sbe gm ps
                     , vsInitialAssignments = pvcInitialAssignments pvc
                     , vsCounterexampleFn = cfn
                     , vsStaticErrors = pvcStaticErrors pvc
                     }
        if null (pvcStaticErrors pvc) then
         forM_ (pvcChecks pvc) $ \vc -> do
           let vs = mkVState (vcName vc) (vcCounterexample vc)
           g <- scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc
           when (verb >= 3) $ do
             putStr $ "Checking " ++ vcName vc
             when (verb >= 4) $ putStr $ " (" ++ show g ++ ")"
             putStrLn ""
           prover vs script g
        else do
          let vsName = "an invalid path"
          let vs = mkVState vsName (\_ -> return $ vcat (pvcStaticErrors pvc))
          false <- scBool sc False
          g <- scImplies sc (pvcAssumptions pvc) false
          when (verb >= 4) $ do
            putStrLn $ "Checking " ++ vsName
            print $ pvcStaticErrors pvc
            putStrLn $ "Calling prover to disprove " ++
                     scPrettyTerm (pvcAssumptions pvc)
          prover vs script g

data VerifyState = VState {
         vsVCName :: String
       , vsMethodSpec :: LLVMMethodSpecIR
       , vsVerbosity :: Verbosity
         -- | Starting Block is used for checking VerifyAt commands.
       -- , vsFromBlock :: SymBlockId
         -- | Evaluation context used for parsing expressions during
         -- verification.
       , vsEvalContext :: EvalContext
       , vsInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
       , vsCounterexampleFn :: CounterexampleFn
       , vsStaticErrors :: [Doc]
       }

type Verbosity = Int
