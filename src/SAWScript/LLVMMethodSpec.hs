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

-- Imports {{{1

import Control.Applicative hiding (empty)
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Error (ErrorT, runErrorT, throwError, MonadError)
import Control.Monad.State
import Data.Int
import Data.List (intercalate) -- foldl', intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.LLVMExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.LLVMMethodSpecIR
import SAWScript.Proof

import Verifier.LLVM.Simulator hiding (State)
import Verifier.LLVM.Simulator.Internals hiding (State)
import Verifier.LLVM.Codebase
import Verifier.LLVM.Codebase.AST
import Verifier.LLVM.Backend hiding (asBool)
import Verifier.LLVM.Backend.SAW
import Verinf.Symbolic (Lit)
import Verinf.Utils.LogMonad

import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm hiding (Ident)
import Verifier.SAW.TypedAST hiding (Ident)

-- LSS Utilities {{{1

type SpecBackend = SAWBackend LSSCtx Lit
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
  return (ps' & pathMem .~ m')

loadPathState :: SBE SpecBackend
              -> SharedTerm LSSCtx
              -> MemType
              -> SpecPathState
              -> IO (SpecPathState, SharedTerm LSSCtx)
loadPathState sbe src tp ps = do
  (c, v) <- sbeRunIO sbe (memLoad sbe (ps ^. pathMem) tp src 0)
  ps' <- addAssertion sbe c ps
  return (ps', v)

-- | Add assumption for predicate to path state.
addAssumption :: SBE SpecBackend -> SharedTerm LSSCtx -> SpecPathState -> IO SpecPathState
addAssumption sbe x p = do
  p & pathAssertions %%~ \a -> liftIO (sbeRunIO sbe (applyAnd sbe a x))

-- | Add assertion for predicate to path state.
addAssertion :: SBE SpecBackend -> SharedTerm LSSCtx -> SpecPathState -> IO SpecPathState
addAssertion sbe x p = do
  -- TODO: p becomes an additional VC in this case
  p & pathAssertions %%~ \a -> liftIO (sbeRunIO sbe (applyAnd sbe a x))

-- EvalContext {{{1

-- | Contextual information needed to evaluate expressions.
data EvalContext
  = EvalContext {
      ecContext :: SharedContext LSSCtx
    , ecBackend :: SBE SpecBackend
    , ecArgs :: [(Ident, SharedTerm LSSCtx)]
    , ecPathState :: SpecPathState
    , ecLLVMExprs :: Map String TC.LLVMExpr
    }

evalContextFromPathState :: Map String TC.LLVMExpr
                         -> SharedContext LSSCtx
                         -> SBE SpecBackend
                         -> SpecPathState
                         -> EvalContext
evalContextFromPathState m sc sbe ps
  = EvalContext {
      ecContext = sc
    , ecBackend = sbe
    , ecArgs = cfArgValues (head (ps ^.. pathCallFrames))
    , ecPathState = ps
    , ecLLVMExprs = m
    }

type ExprEvaluator a = ErrorT TC.LLVMExpr IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either TC.LLVMExpr b)
runEval v = liftIO (runErrorT v)

-- N.B. This method assumes that the LLVM path state is well-formed.
-- It does not assume that all the memory references in the
-- LLVMEvalContext are initialized.
evalLLVMExpr :: TC.LLVMExpr -> EvalContext -> IO SpecLLVMValue
evalLLVMExpr expr ec = eval expr
  where eval e@(CC.Term app) =
          case app of
            TC.Arg _ n _ ->
              case lookup n (ecArgs ec) of
                Just v -> return v
                Nothing -> fail (show e) -- TODO
            TC.Global n _ -> do
              fail "globals not yet implemented"
            TC.Deref e tp -> do
              addr <- evalLLVMExpr e ec 
              loadPathState (ecBackend ec) addr tp (ecPathState ec)
              fail "deref not yet supported"
            TC.StructField e n i _ -> fail "struct fields not yet supported" -- TODO
              {- do
              JSS.RValue ref <- eval r
              let ifields = (ecPathState ec) ^. JSS.pathMemory . JSS.memInstanceFields
              case Map.lookup (ref, f) ifields of
                Just v -> return v
                Nothing -> fail (show e) -- TODO -}

{-
evalJavaRefExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator JSS.Ref
evalJavaRefExpr expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue ref -> return ref
    _ -> error "internal: evalJavaRefExpr encountered illegal value."
-}

{-
evalLLVMExprAsLogic :: TC.LLVMExpr -> EvalContext -> ExprEvaluator (SharedTerm LSSCtx)
evalLLVMExprAsLogic expr ec = do
  val <- evalLLVMExpr expr ec
  case val of
    JSS.RValue r ->
      let arrs = (ecPathState ec) ^. JSS.pathMemory . JSS.memScalarArrays in
      case Map.lookup r arrs of
        Nothing    -> throwError expr
        Just (_,n) -> return n
    JSS.IValue n -> return n
    JSS.LValue n -> return n
    _ -> error "internal: evalJavaExprAsExpr encountered illegal value."
-}

scLLVMValue :: SharedContext s -> SharedTerm s -> String -> IO (SharedTerm s)
scLLVMValue sc ty name = do
  s <- scString sc name
  ty' <- scRemoveBitvector sc ty
  mkValue <- scGlobalDef sc (parseIdent "LLVM.mkValue")
  scApplyAll sc mkValue [ty', s]

-- | Evaluates a typed expression in the context of a particular state.
evalLogicExpr :: TC.LogicExpr -> EvalContext -> ExprEvaluator (SharedTerm LSSCtx)
evalLogicExpr initExpr ec = liftIO $ do
  let sc = ecContext ec
  t <- TC.useLogicExpr sc initExpr
  rules <- forM (Map.toList (ecLLVMExprs ec)) $ \(name, expr) ->
             do lt <- evalLLVMExpr expr ec
                ty <- scTypeOf sc lt
                nt <- scLLVMValue sc ty name
                return (ruleOfTerms nt lt)
  let ss = addRules rules emptySimpset
  rewriteSharedTerm sc ss t

-- | Return Java value associated with mixed expression.
evalMixedExpr :: TC.MixedExpr -> EvalContext
              -> ExprEvaluator SpecLLVMValue
evalMixedExpr (TC.LogicE expr) ec = evalLogicExpr expr ec
evalMixedExpr (TC.LLVME expr) ec = liftIO $ evalLLVMExpr expr ec

-- Method specification overrides {{{1
-- OverrideComputation definition {{{2

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
   -- deriving (Show)

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

-- OverrideComputation utilities {{{2

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
ocModifyResultState :: (SpecPathState -> SpecPathState) -> OverrideComputation ()
ocModifyResultState fn = do
  bcs <- get
  put $! bcs { ocsResultState = fn (ocsResultState bcs) }

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

-- ocStep {{{2

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
{-
ocStep (EnsureScalar _pos lhsExpr rhsExpr) = do
  ocEval (evalLLVMExpr lhsExpr) $ \lhsRef ->
    ocEval (evalMixedExpr rhsExpr) $ \value ->
      undefined
ocStep (EnsureArray _pos lhsExpr rhsExpr) = do
  ocEval (evalLLVMRefExpr lhsExpr) $ \lhsTerm ->
    ocEval (evalLogicExpr   rhsExpr) $ \rhsVal ->
      ocModifyResultState $ setArrayValue lhsRef rhsVal
ocStep (ModifyScalar lhsExpr) =
  ocEval (evalJavaExpr lhsExpr) $ \lhsTerm -> do
    sc <- gets (ecContext . ocsEvalContext)
    let tp = JSS.fieldIdType f
        w = fromIntegral $ JSS.stackWidth tp
    logicType <- liftIO $ scBitvector sc (fromInteger w)
    n <- liftIO $ scFreshGlobal sc "_" logicType
    ocModifyResultState $ setInstanceFieldValue lhsRef f n
ocStep (ModifyArray refExpr ty) = do
  ocEval (evalJavaRefExpr refExpr) $ \ref -> do
    sc <- gets (ecContext . ocsEvalContext)
    mtp <- liftIO $ TC.logicTypeOfActual sc ty
    rhsVal <- maybe (fail "can't convert") (liftIO . scFreshGlobal sc "_") mtp
    ocModifyResultState $ setArrayValue ref rhsVal
-}
ocStep (Return expr) = do
  ocEval (evalMixedExpr expr) $ \val ->
    modify $ \ocs -> ocs { ocsReturnValue = Just val }

-- Executing overrides {{{2

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
       -- Check that all expressions that reference each other may do so.
       {- TODO
       do -- Build map from references to expressions that map to them.
          let exprs = bsRefExprs bs
          ocEval (\_ -> mapM (flip evalLLVMRefExpr ec) exprs) $ \refs -> do
            let refExprMap = Map.fromListWith (++) $ refs `zip` [[e] | e <- exprs]
            --- Get counterexamples.
            let mayAliasSet = bsMayAliasSet bs
            let badPairs = catMaybes
                         $ map (\cl -> CC.checkEquivalence cl mayAliasSet)
                         $ Map.elems refExprMap
            -- Throw error if counterexample is found.
            case badPairs of
              [] -> return ()
              (x,y):_ -> ocError (AliasingInputs x y)
       -}
       let sc = ecContext ec
       -- Verify the initial logic assignments
       {- TODO
       forM_ (bsLogicAssignments bs) $ \(pos, lhs, rhs) -> do
         ocEval (evalLLVMExprAsLogic lhs) $ \lhsVal ->
           ocEval (evalLogicExpr rhs) $ \rhsVal ->
             ocAssert pos "Override value assertion"
                =<< liftIO (scEq sc lhsVal rhsVal)
       -}
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
      m = specLLVMExprNames ir
  sbe <- gets symBE
  let ec = EvalContext { ecContext = sc
                       , ecBackend = sbe
                       , ecArgs = zip (map fst (sdArgs func)) (map snd args)
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
  let sym = sdName (specFunction ir)
      ovd = Override (\_ _ -> execOverride sc pos ir)
  -- TODO: check argument types?
  tryRegisterOverride sym (const (Just ovd))

-- ExpectedStateDef {{{1

-- | Describes expected result of computation.
data ExpectedStateDef = ESD {
         -- | Location that we started from.
         esdStartLoc :: SymBlockID
         -- | Initial path state (used for evaluating expressions in
         -- verification).
       , esdBackend :: SBE SpecBackend
       , esdInitialPathState :: SpecPathState
         -- | Stores initial assignments.
       , esdInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
         -- | Map from references back to Java expressions denoting them.
       -- , esdRefExprMap :: Map JSS.Ref [TC.LLVMExpr]
         -- | Expected return value or Nothing if method returns void.
       , esdReturnValue :: Maybe (SharedTerm LSSCtx)
       }

{-
esdRefName :: JSS.Ref -> ExpectedStateDef -> String
esdRefName JSS.NullRef _ = "null"
esdRefName ref esd =
  case Map.lookup ref (esdRefExprMap esd) of
    Just cl -> ppJavaExprEquivClass cl
    Nothing -> "fresh allocation"
-}

-- Initial state generation {{{1

-- | State for running the behavior specifications in a method override.
data ESGState = ESGState {
         esContext :: SharedContext LSSCtx
       , esBackend :: SBE SpecBackend
       , esDef :: SymDefine (SharedTerm LSSCtx)
       , esLLVMExprs :: Map String TC.LLVMExpr
       -- , esExprRefMap :: Map TC.LLVMExpr JSS.Ref -- FIXME
       , esInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
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
  initPS <- gets esInitialPathState
  let ec = evalContextFromPathState m sc sbe initPS
  res <- runEval (fn ec)
  case res of
    Left expr -> fail $ "internal: esEval given " ++ show expr ++ "."
    Right v   -> return v

esGetInitialPathState :: ExpectedStateGenerator SpecPathState
esGetInitialPathState = gets esInitialPathState

esPutInitialPathState :: SpecPathState -> ExpectedStateGenerator ()
esPutInitialPathState ps = modify $ \es -> es { esInitialPathState = ps }

esModifyInitialPathState :: (SpecPathState -> SpecPathState)
                         -> ExpectedStateGenerator ()
esModifyInitialPathState fn =
  modify $ \es -> es { esInitialPathState = fn (esInitialPathState es) }

esModifyInitialPathStateIO :: (SpecPathState -> IO SpecPathState)
                         -> ExpectedStateGenerator ()
esModifyInitialPathStateIO fn =
  do s0 <- esGetInitialPathState
     esPutInitialPathState =<< liftIO (fn s0)

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
esAssertEq _ _ _ = error "internal: esAssertEq given illegal arguments."

-- | Set value in initial state.
esSetLLVMValue :: TC.LLVMExpr -> SpecLLVMValue -> ExpectedStateGenerator ()
esSetLLVMValue e@(CC.Term exprF) v = do
  case exprF of
    -- TODO: the following is ugly, and doesn't make good use of lenses
    TC.Global _ _ -> fail "Can't set the value of globals."
    TC.Arg _ name _ -> fail "Can't set the value of arguments."
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
    TC.StructField refExpr f fi _ -> fail "Can't set the value of structure fields."

esResolveLogicExprs :: SharedTerm LSSCtx -> [TC.LogicExpr]
                    -> ExpectedStateGenerator (SharedTerm LSSCtx)
esResolveLogicExprs tp [] = do
  sc <- gets esContext
  -- Create input variable.
  liftIO $ scFreshGlobal sc "_" tp
esResolveLogicExprs _ (hrhs:rrhs) = do
  sc <- gets esContext
  sbe <- gets esBackend
  t <- esEval $ evalLogicExpr hrhs
  -- Add assumptions for other equivalent expressions.
  forM_ rrhs $ \rhsExpr -> do
    rhs <- esEval $ evalLogicExpr rhsExpr
    esModifyInitialPathStateIO $ \s0 -> do prop <- scEq sc t rhs
                                           addAssumption sbe prop s0
  -- Return value.
  return t

esSetLogicValues :: SharedContext LSSCtx -> [TC.LLVMExpr] -> SharedTerm LSSCtx
                 -> [TC.LogicExpr]
                 -> ExpectedStateGenerator ()
esSetLogicValues sc cl tp lrhs = do
  -- Get value of rhs.
  value <- esResolveLogicExprs tp lrhs
  -- Update Initial assignments.
  modify $ \es -> es { esInitialAssignments =
                         map (\e -> (e,value)) cl ++  esInitialAssignments es }
  ty <- liftIO $ scTypeOf sc value
  -- Update value.
  mapM_ (flip esSetLLVMValue value) cl -- TODO: different for arrays?
{-
  case ty of
    (isVecType (const (return ())) -> Just _) -> do
       refs <- forM cl $ \expr -> do
                 JSS.RValue ref <- esEval $ evalJavaExpr expr
                 return ref
       forM_ refs $ \r -> esModifyInitialPathState (setArrayValue r value)
    _ -> error "internal: initializing LLVM values given bad rhs."
-}

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
{-
esStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  value <- esEval $ evalMixedExpr rhsExpr
  -- Get dag engine
  sc <- gets esContext
  -- Check that instance field is already defined, if so add an equality check for that.
  ifMap <- gets esInstanceFields
  case (Map.lookup (ref, f) ifMap, value) of
    (Nothing, _) -> return ()
    (Just Nothing, _) -> return ()
    (Just (Just (JSS.RValue prev)), JSS.RValue new)
      | prev == new -> return ()
    (Just (Just (JSS.IValue prev)), JSS.IValue new) ->
       esAddEqAssertion sc (show refExpr) prev new
    (Just (Just (JSS.LValue prev)), JSS.LValue new) ->
       esAddEqAssertion sc (show refExpr) prev new
    -- TODO: See if we can give better error message here.
    -- Perhaps this just ends up meaning that we need to verify the assumptions in this
    -- behavior are inconsistent.
    _ -> error "internal: Incompatible values assigned to instance field."
  -- Define instance field post condition.
  modify $ \es ->
    es { esInstanceFields = Map.insert (ref,f) (Just value) (esInstanceFields es) }
esStep (ModifyInstanceField refExpr f) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember (ref, f) (esInstanceFields es)) $ do
    put es { esInstanceFields = Map.insert (ref,f) Nothing (esInstanceFields es) }
esStep (EnsureArray _pos lhsExpr rhsExpr) = do
  -- Evaluate expressions.
  ref    <- esEval $ evalJavaRefExpr lhsExpr
  value  <- esEval $ evalLogicExpr rhsExpr
  -- Get dag engine
  sc <- gets esContext
  let l = case value of
            (STApp _ (FTermF (ArrayValue _ vs))) -> fromIntegral (V.length vs)
            _ -> error "internal: right hand side of array ensure clause isn't an array"
  -- Check if array has already been assigned value.
  aMap <- gets esArrays
  case Map.lookup ref aMap of
    Just (Just (oldLen, prev))
      | l /= fromIntegral oldLen -> error "internal: array changed size."
      | otherwise -> esAddEqAssertion sc (show lhsExpr) prev value
    _ -> return ()
  -- Define instance field post condition.
  modify $ \es -> es { esArrays = Map.insert ref (Just (l, value)) (esArrays es) }
esStep (ModifyArray refExpr _) = do
  ref <- esEval $ evalJavaRefExpr refExpr
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember ref (esArrays es)) $ do
    put es { esArrays = Map.insert ref Nothing (esArrays es) }
-}

-- TODO: this doesn't support aliasing
initializeVerification :: (MonadIO m, Functor m) =>
                          SharedContext LSSCtx
                       -> LLVMMethodSpecIR
                       -> Simulator SpecBackend m ExpectedStateDef
initializeVerification sc ir = do
  let exprs = specLLVMExprNames ir
      bs = specBehavior ir
      fn = specFunction ir
      newArg (Ident nm, mty) = do
        Just ty <- TC.logicTypeOfActual sc mty
        tm <- scFreshGlobal sc nm ty
        return (mty, tm)
  sbe <- gets symBE
  args <- liftIO $ mapM newArg (sdArgs fn)
  let rreg =  (,Ident "__sawscript_result") <$> sdRetType fn
  callDefine' False (sdName (specFunction ir)) rreg args

  initPS <- fromMaybe (error "initializeVerification") <$> getPath
  let initESG = ESGState { esContext = sc
                         , esBackend = sbe
                         , esDef = fn
                         , esLLVMExprs = exprs
                         -- , esExprRefMap = Map.fromList
                         --    [ (e, r) | (cl,r) <- refAssignments, e <- cl ]
                         , esInitialAssignments = []
                         , esInitialPathState = initPS
                         , esReturnValue = Nothing
                         }
  es <- liftIO $ flip execStateT initESG $ do
{-
          -- Set references
          forM_ refAssignments $ \(cl,r) ->
            forM_ cl $ \e -> esSetLLVMValue e (JSS.RValue r)
-}
{-
          -- Set initial logic values.
          lcs <- liftIO $ bsLogicClasses sc exprs bs ptrConfig
          case lcs of
            Nothing ->
              let msg = "Unresolvable cyclic dependencies between assumptions."
               in throwIOExecException (specPos ir) (ftext msg) ""
            Just assignments -> mapM_ (\(l,t,r) -> esSetLogicValues sc l t r) assignments
-}
          -- Process commands
          mapM esStep (bsCommands bs)

  Just cs <- use ctrlStk
  ctrlStk ?= (cs & currentPath .~ esInitialPathState es)

  return ESD { esdStartLoc = bsLoc bs
             , esdBackend = sbe
             , esdInitialPathState = esInitialPathState es
             , esdInitialAssignments = reverse (esInitialAssignments es)
{-
             , esdRefExprMap =
                  Map.fromList [ (r, cl) | (cl,r) <- refAssignments ]
-}
             , esdReturnValue = esReturnValue es
             }

-- MethodSpec verification {{{1

-- VerificationCheck {{{2

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

-- PathVC {{{2

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

type PathVCGenerator = State PathVC

-- | Add verification condition to list.
pvcgAssertEq :: String -> SharedTerm LSSCtx -> SharedTerm LSSCtx -> PathVCGenerator ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: String -> SharedTerm LSSCtx -> PathVCGenerator ()
pvcgAssert nm v =
  modify $ \pvc -> pvc { pvcChecks = AssertionCheck nm v : pvcChecks pvc }

pvcgFail :: Doc -> PathVCGenerator ()
pvcgFail msg =
  modify $ \pvc -> pvc { pvcStaticErrors = msg : pvcStaticErrors pvc }

-- generateVC {{{2

-- | Compare result with expected state.
generateVC :: LLVMMethodSpecIR 
           -> ExpectedStateDef -- ^ What is expected
           -> RunResult -- ^ Results of symbolic execution.
           -> PathVC -- ^ Proof oblications
generateVC ir esd (ps, endLoc, res) = do
  let initState  =
        PathVC { pvcInitialAssignments = esdInitialAssignments esd
               , pvcStartLoc = esdStartLoc esd
               , pvcEndLoc = endLoc
               , pvcAssumptions = ps ^. pathAssertions
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  flip execState initState $ do
    case res of
      Left oe -> pvcgFail (vcat (map (ftext . ppOverrideError) oe))
      Right maybeRetVal -> do
        -- Check return value
        case (maybeRetVal, esdReturnValue esd) of
          (Nothing,Nothing) -> return ()
          (Just rv, Just srv) -> pvcgAssertEq "return value" rv srv
{-
        -- Check value arrays
        forM_ (Map.toList (ps ^. JSS.pathMemory . JSS.memScalarArrays)) $ \(ref,(jlen,jval)) -> do
          case Map.lookup ref (esdArrays esd) of
            Nothing -> pvcgFail $ ftext $ "Allocates an array."
            Just Nothing -> return ()
            Just (Just (slen, sval))
              | jlen /= slen -> pvcgFail $ ftext $ "Array changes size."
              | otherwise -> pvcgAssertEq (esdRefName ref esd) jval sval
        -- Check ref arrays
        when (not (Map.null (ps ^. JSS.pathMemory . JSS.memRefArrays))) $ do
          pvcgFail $ ftext "Modifies references arrays."
-}
        -- Check assertions
        pvcgAssert "final assertions" (ps ^. pathAssertions)

-- verifyMethodSpec and friends {{{2

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
  return $ map (generateVC ir esd) [(ps, Nothing, Right returnVal)]

data VerifyParams = VerifyParams
  { vpCode    :: Codebase (SAWBackend LSSCtx Lit)
  , vpContext :: SharedContext LSSCtx
  , vpOpts    :: Options
  , vpSpec    :: LLVMMethodSpecIR
  , vpOver    :: [LLVMMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext LSSCtx -> ExpectedStateDef -> [PathVC] -> IO ()
type Prover =
  VerifyState -> ProofScript SAWCtx ProofResult -> SharedTerm LSSCtx -> IO ()

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc esd results = do
  let ir = vpSpec params
      verb = verbLevel (vpOpts params)
      ps = esdInitialPathState esd
      m = specLLVMExprNames ir
      sbe = esdBackend esd
  case specValidationPlan ir of
    Skip -> putStrLn $ "WARNING: skipping verification of " ++
                       show (sdName (specFunction ir))
    RunVerify script -> do
      forM_ results $ \pvc -> do
        let mkVState nm cfn =
              VState { vsVCName = nm
                     , vsMethodSpec = ir
                     , vsVerbosity = verb
                     -- , vsFromBlock = esdStartLoc esd
                     , vsEvalContext = evalContextFromPathState m sc sbe ps
                     , vsInitialAssignments = pvcInitialAssignments pvc
                     , vsCounterexampleFn = cfn
                     , vsStaticErrors = pvcStaticErrors pvc
                     }
        if null (pvcStaticErrors pvc) then
         forM_ (pvcChecks pvc) $ \vc -> do
           let vs = mkVState (vcName vc) (vcCounterexample vc)
           g <- scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc
           when (verb >= 4) $ do
             putStrLn $ "Checking " ++ vcName vc ++ " (" ++ show g ++ ")"
           prover vs script g
        else do
          let vsName = "an invalid path " {-
                         ++ (case esdStartLoc esd of
                               0 -> ""
                               block -> " from " ++ show loc)
                         ++ maybe "" (\loc -> " to " ++ show loc)
                                  (pvcEndLoc pvc) -}
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
