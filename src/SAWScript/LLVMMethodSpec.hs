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
  , VerifyParams(..)
  , VerifyState(..)
  , EvalContext(..)
  , ExpectedStateDef(..)
  ) where

-- Imports {{{1

import Control.Applicative hiding (empty)
--import Control.Exception (finally)
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
--import Data.Set (Set)
import qualified Data.Set as Set
--import qualified Data.Vector.Storable as SV
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP
--import System.Directory(doesFileExist)
--import System.FilePath (splitExtension, addExtension)
--import System.IO

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.LLVMExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.LLVMMethodSpecIR
import SAWScript.Proof

import qualified Verifier.LLVM.Simulator as LSS
import qualified Verifier.LLVM.Simulator.Internals as LSS
import qualified Verifier.LLVM.Codebase as LSS
import qualified Verifier.LLVM.Codebase.AST as LSS
import Verifier.LLVM.Backend.SAW
import Verinf.Symbolic (Lit)
import Verinf.Utils.LogMonad

import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

-- LSS Utilities {{{1

type SpecBackend = SAWBackend LSSCtx Lit
type SpecPathState = LSS.Path SpecBackend
type SpecLLVMValue = SharedTerm LSSCtx

{-
-- | Set value of bound to struct field in path state.
setStructFieldValue :: JSS.Ref -> JSS.FieldId -> SpecJavaValue
                      -> SpecPathState -> SpecPathState
setStructFieldValue r f v =
  JSS.pathMemory . JSS.memInstanceFields %~ Map.insert (r, f) v

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValue :: JSS.Ref -> SharedTerm LSSCtx
              -> SpecPathState -> SpecPathState
setArrayValue r v@(STApp _ (FTermF (ArrayValue _ vs))) =
  JSS.pathMemory . JSS.memScalarArrays %~ Map.insert r (w, v)
    where w = fromIntegral $ V.length vs
setArrayValue _ _ = error "internal: setArrayValue called with non-array value"
-}
-- | Add assumption for predicate to path state.
addAssumption :: SharedContext LSSCtx -> SharedTerm LSSCtx -> SpecPathState -> IO SpecPathState
addAssumption sc x p = do
  andOp <- liftIO $ scApplyPreludeAnd sc
  p & LSS.pathAssertions %%~ \a -> liftIO (andOp a x)

-- | Add assertion for predicate to path state.
addAssertion :: SharedContext LSSCtx -> SharedTerm LSSCtx -> SpecPathState -> IO SpecPathState
addAssertion sc x p = do
  -- TODO: p becomes an additional VC in this case
  andOp <- liftIO $ scApplyPreludeAnd sc
  p & LSS.pathAssertions %%~ \a -> liftIO (andOp a x)

-- EvalContext {{{1

-- | Contextual information needed to evaluate expressions.
data EvalContext
  = EvalContext {
      ecContext :: SharedContext LSSCtx
    , ecRegs :: LSS.RegMap (SharedTerm LSSCtx)
    , ecPathState :: SpecPathState
    , ecLLVMValues :: Map String (SharedTerm LSSCtx)
    }

evalContextFromPathState :: SharedContext LSSCtx -> SpecPathState -> EvalContext
evalContextFromPathState sc ps
  = EvalContext {
      ecContext = sc
    , ecRegs = (head (ps ^.. LSS.pathCallFrames)) ^. LSS.cfRegs
    , ecPathState = ps
    , ecLLVMValues = Map.empty
    }

type ExprEvaluator a = ErrorT TC.LLVMExpr IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either TC.LLVMExpr b)
runEval v = liftIO (runErrorT v)

addLLVMValues :: (Monad m) =>
                 Map String TC.LLVMExpr -> EvalContext
              -> m EvalContext
addLLVMValues m ec = do
  vs <- forM (Map.toList m) $
          \(name, expr) -> do v <- evalLLVMExpr expr ec
                              return (name, v)
  return ec { ecLLVMValues = Map.fromList vs }

-- N.B. This method assumes that the LLVM path state is well-formed.
-- It does not assume that all the memory references in the
-- LLVMEvalContext are initialized.
evalLLVMExpr :: (Monad m) => TC.LLVMExpr -> EvalContext -> m SpecLLVMValue
evalLLVMExpr expr ec = undefined
  {- eval expr
  where eval e@(CC.Term app) =
          case app of
            TC.Local _ idx _ ->
              case Map.lookup idx (ecLocals ec) of
                Just v -> return v
                Nothing -> fail (show e) -- TODO
            TC.InstanceField r f -> do
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

scLLVMValue :: SharedContext LSSCtx -> SharedTerm LSSCtx -> String -> IO (SharedTerm LSSCtx)
scLLVMValue sc ty name = do
  s <- scString sc name
  mkValue <- scGlobalDef sc (parseIdent "LLVM.mkValue")
  scApplyAll sc mkValue [ty, s]

-- | Evaluates a typed expression in the context of a particular state.
evalLogicExpr :: TC.LogicExpr -> EvalContext -> ExprEvaluator (SharedTerm LSSCtx)
evalLogicExpr initExpr ec = liftIO $ do
  let sc = ecContext ec
  t <- TC.useLogicExpr sc initExpr
  rules <- forM (Map.toList (ecLLVMValues ec)) $ \(name, lt) ->
             do ty <- scTypeOf sc lt
                ty' <- scRemoveBitvector sc ty
                nt <- scLLVMValue sc ty' name
                return (ruleOfTerms nt lt)
  let ss = addRules rules emptySimpset
  rewriteSharedTerm sc ss t

-- | Return Java value associated with mixed expression.
evalMixedExpr :: TC.MixedExpr -> EvalContext
              -> ExprEvaluator SpecLLVMValue
evalMixedExpr (TC.LogicE expr) ec = evalLogicExpr expr ec
evalMixedExpr (TC.LLVME expr) ec = evalLLVMExpr expr ec

-- Method specification overrides {{{1
-- OverrideComputation definition {{{2

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         ocsLoc :: LSS.SymBlockID
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
   = SuccessfulRun SpecPathState (Maybe LSS.SymBlockID) (Maybe SpecLLVMValue)
   | FalseAssumption
   | FailedRun SpecPathState (Maybe LSS.SymBlockID) [OverrideError]
   -- deriving (Show)

type RunResult = ( SpecPathState
                 , Maybe LSS.SymBlockID
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
  sc <- (ecContext . ocsEvalContext) <$> get
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultStateIO (addAssertion sc x)

-- ocStep {{{2

ocStep :: BehaviorCommand -> OverrideComputation ()
ocStep (AssertPred pos expr) =
  ocEval (evalLogicExpr expr) $ \p ->
    ocAssert pos "Override predicate" p
ocStep (AssumePred expr) = do
  sc <- gets (ecContext . ocsEvalContext)
  ocEval (evalLogicExpr expr) $ \v ->
    case asBool v of
      Just True -> return ()
      Just False -> ocAssumeFailed
      _ -> ocModifyResultStateIO $ addAssumption sc v
{-
ocStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef ->
    ocEval (evalMixedExpr rhsExpr) $ \value ->
      ocModifyResultState $ setInstanceFieldValue lhsRef f value
ocStep (EnsureArray _pos lhsExpr rhsExpr) = do
  ocEval (evalJavaRefExpr lhsExpr) $ \lhsRef ->
    ocEval (evalLogicExpr   rhsExpr) $ \rhsVal ->
      ocModifyResultState $ setArrayValue lhsRef rhsVal
ocStep (ModifyInstanceField refExpr f) =
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef -> do
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
             -> [(LSS.MemType, SpecLLVMValue)]
             -> LSS.Simulator SpecBackend m SpecLLVMValue
execOverride sc pos ir args = do
  -- Execute behaviors.
  initPS <- fromMaybe (error "no path during override") <$> LSS.getPath
  let bsl = specBehaviors ir -- Map.lookup entryBlock (specBehaviors ir) -- TODO
  let method = specFunction ir
      m = specLLVMExprNames ir
  let ec0 = EvalContext { ecContext = sc
                        , ecRegs = undefined args -- TODO
                        , ecPathState = initPS
                        , ecLLVMValues = Map.empty
                        }
  ec <- addLLVMValues m ec0
  -- Execute behavior.
  res <- liftIO . execBehavior [bsl] ec =<< 
         (fromMaybe (error "no path during override") <$> LSS.getPath)
  -- Create function for generation resume actions.
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
    [(_, _, Right mval)] -> undefined
  {-
      JSS.modifyPathM_ (PP.text "path result") $ \ps ->
        return $
        case (mval, ps ^. JSS.pathStack) of
          (Just val, [])     -> ps & set JSS.pathRetVal (Just val)
          (Just val, (f:fr)) -> ps & set JSS.pathStack  (f' : fr)
            where f' = f & JSS.cfOpds %~ (val :)
          (Nothing,  [])     -> ps & set JSS.pathRetVal Nothing
          (Nothing,  _:_)    -> ps
-}
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: (MonadIO m, Functor m) =>
                    SharedContext LSSCtx
                 -> Pos
                 -> LLVMMethodSpecIR
                 -> LSS.Simulator SpecBackend m ()
overrideFromSpec sc pos ir = do
  let sym = LSS.sdName (specFunction ir)
      ovd = LSS.override (execOverride sc pos ir)
  -- TODO: check argument types?
  LSS.tryRegisterOverride sym (const (Just ovd))

-- ExpectedStateDef {{{1

-- | Describes expected result of computation.
data ExpectedStateDef = ESD {
         -- | Location that we started from.
         esdStartLoc :: LSS.SymBlockID
         -- | Initial path state (used for evaluating expressions in
         -- verification).
       , esdInitialPathState :: SpecPathState
         -- | Stores initial assignments.
       , esdInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
         -- | Map from references back to Java expressions denoting them.
       --, esdRefExprMap :: Map JSS.Ref [TC.LLVMExpr]
         -- | Expected return value or Nothing if method returns void.
       , esdReturnValue :: Maybe (SharedTerm LSSCtx)
         -- | Maps instance fields to expected value, or Nothing if value may
         -- be arbitrary.
       --, esdInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe (JSS.Value (SharedTerm LSSCtx)))
         -- | Maps reference to expected node, or Nothing if value may be arbitrary.
       --, esdArrays :: Map JSS.Ref (Maybe (Int32, SharedTerm LSSCtx))
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
       , esDef :: LSS.SymDefine (SharedTerm LSSCtx)
       , esLLVMExprs :: Map String TC.LLVMExpr
       -- , esExprRefMap :: Map TC.LLVMExpr JSS.Ref -- FIXME
       , esInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
       , esInitialPathState :: SpecPathState
       , esReturnValue :: Maybe SpecLLVMValue
       -- , esInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe SpecJavaValue) -- FIXME
       -- , esArrays :: Map JSS.Ref (Maybe (Int32, SharedTerm LSSCtx)) -- FIXME
       }

-- | Monad used to execute statements in a behavior specification for a method
-- override.
type ExpectedStateGenerator = StateT ESGState IO

esEval :: (EvalContext -> ExprEvaluator b) -> ExpectedStateGenerator b
esEval fn = do
  sc <- gets esContext
  m <- gets esLLVMExprs 
  initPS <- gets esInitialPathState
  let ec0 = evalContextFromPathState sc initPS
  ec <- addLLVMValues m ec0
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

esAddEqAssertion :: SharedContext LSSCtx -> String -> SharedTerm LSSCtx -> SharedTerm LSSCtx
                 -> ExpectedStateGenerator ()
esAddEqAssertion sc _nm x y =
  do prop <- liftIO (scEq sc x y)
     esModifyInitialPathStateIO (addAssertion sc prop)

-- | Assert that two terms are equal.
esAssertEq :: String -> SpecLLVMValue -> SpecLLVMValue
           -> ExpectedStateGenerator ()
esAssertEq nm x y = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq _ _ _ = error "internal: esAssertEq given illegal arguments."

{-
-- | Set value in initial state.
esSetJavaValue :: TC.JavaExpr -> SpecJavaValue -> ExpectedStateGenerator ()
esSetJavaValue e@(CC.Term exprF) v = do
  case exprF of
    -- TODO: the following is ugly, and doesn't make good use of lenses
    TC.Local _ idx _ -> do
      ps <- esGetInitialPathState
      let ls = case JSS.currentCallFrame ps of
                 Just cf -> cf ^. JSS.cfLocals
                 Nothing -> Map.empty
          ps' = (JSS.pathStack %~ updateLocals) ps
          updateLocals (f:r) = (JSS.cfLocals %~ Map.insert idx v) f : r
          updateLocals [] = error "internal: esSetJavaValue of local with empty call stack"
      case Map.lookup idx ls of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing -> esPutInitialPathState ps'
    -- TODO: the following is ugly, and doesn't make good use of lenses
    TC.InstanceField refExpr f -> do
      -- Lookup refrence associated to refExpr
      Just ref <- Map.lookup refExpr <$> gets esExprRefMap
      ps <- esGetInitialPathState
      case Map.lookup (ref,f) (ps ^. JSS.pathMemory . JSS.memInstanceFields) of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing -> esPutInitialPathState $
          (JSS.pathMemory . JSS.memInstanceFields %~ Map.insert (ref,f) v) ps
-}

esResolveLogicExprs :: SharedTerm LSSCtx -> [TC.LogicExpr]
                    -> ExpectedStateGenerator (SharedTerm LSSCtx)
esResolveLogicExprs tp [] = do
  sc <- gets esContext
  -- Create input variable.
  liftIO $ scFreshGlobal sc "_" tp
esResolveLogicExprs _ (hrhs:rrhs) = do
  sc <- gets esContext
  t <- esEval $ evalLogicExpr hrhs
  -- Add assumptions for other equivalent expressions.
  forM_ rrhs $ \rhsExpr -> do
    rhs <- esEval $ evalLogicExpr rhsExpr
    esModifyInitialPathStateIO $ \s0 -> do prop <- scEq sc t rhs
                                           addAssumption sc prop s0
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
  case ty of
{-
    (isVecType (const (return ())) -> Just _) -> do
       refs <- forM cl $ \expr -> do
                 JSS.RValue ref <- esEval $ evalJavaExpr expr
                 return ref
       forM_ refs $ \r -> esModifyInitialPathState (setArrayValue r value)
    (asBitvectorType -> Just 32) ->
       mapM_ (flip esSetJavaValue (JSS.IValue value)) cl
    (asBitvectorType -> Just 64) ->
       mapM_ (flip esSetJavaValue (JSS.LValue value)) cl
-}
    _ -> error "internal: initializing LLVM values given bad rhs."

esStep :: BehaviorCommand -> ExpectedStateGenerator ()
esStep (AssertPred _ expr) = do
  sc <- gets esContext
  v <- esEval $ evalLogicExpr expr
  esModifyInitialPathStateIO $ addAssumption sc v
esStep (AssumePred expr) = do
  sc <- gets esContext
  v <- esEval $ evalLogicExpr expr
  esModifyInitialPathStateIO $ addAssumption sc v
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

initializeVerification :: (MonadIO m, Functor m) =>
                          SharedContext LSSCtx
                       -> LLVMMethodSpecIR
                       -> BehaviorSpec
                       -> PtrEquivConfiguration
                       -> LSS.Simulator SpecBackend m ExpectedStateDef
initializeVerification sc ir bs ptrConfig = do
  let m = specLLVMExprNames ir
{-
  exprRefs <- mapM (JSS.genRef . TC.jssTypeOfActual . snd) ptrConfig
  let refAssignments = (map fst refConfig `zip` exprRefs)
      clName = JSS.className (specThisClass ir)
      --key = JSS.methodKey (specMethod ir)
      pushFrame cs = fromMaybe (error "internal: failed to push call frame") mcs'
        where
          mcs' = JSS.pushCallFrame clName
                                   (specMethod ir)
                                   -- FIXME: this is probably the cause of the empty operand stack
                                   JSS.entryBlock -- FIXME: not the right block
                                   Map.empty
                                   cs
  JSS.modifyCSM_ (return . pushFrame)
-}
  -- TODO: add breakpoints once local specs exist
  --forM_ (Map.keys (specBehaviors ir)) $ JSS.addBreakpoint clName key
  -- TODO: set starting PC
  initPS <- fromMaybe (error "initializeVerification") <$> LSS.getPath
  let initESG = ESGState { esContext = sc
                         , esDef = specFunction ir
                         , esLLVMExprs = m
                         -- , esExprRefMap = Map.fromList
                         --    [ (e, r) | (cl,r) <- refAssignments, e <- cl ]
                         , esInitialAssignments = []
                         , esInitialPathState = initPS
                         , esReturnValue = Nothing
                         --, esInstanceFields = Map.empty
                         --, esArrays = Map.empty
                         }
  es <- liftIO $ flip execStateT initESG $ do
{-
          -- Set references
          forM_ refAssignments $ \(cl,r) ->
            forM_ cl $ \e -> esSetJavaValue e (JSS.RValue r)
          -- Set initial logic values.
-}
          lcs <- liftIO $ bsLogicClasses sc m bs ptrConfig
          case lcs of
            Nothing ->
              let msg = "Unresolvable cyclic dependencies between assumptions."
               in throwIOExecException (specPos ir) (ftext msg) ""
{-
            Just assignments -> mapM_ (\(l,t,r) -> esSetLogicValues sc l t r) assignments
-}
          -- Process commands
          mapM esStep (bsCommands bs)
  let ps = esInitialPathState es
  -- TODO: JSS.modifyPathM_ (PP.text "initializeVerification") (\_ -> return ps)
  return ESD { esdStartLoc = bsLoc bs
             , esdInitialPathState = esInitialPathState es
             , esdInitialAssignments = reverse (esInitialAssignments es)
{-
             , esdRefExprMap =
                  Map.fromList [ (r, cl) | (cl,r) <- refAssignments ]
-}
             , esdReturnValue = esReturnValue es
               -- Create esdArrays map while providing entry for unspecified
               -- expressions.
{-
             , esdInstanceFields =
                 Map.union (esInstanceFields es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memInstanceFields))
-}
               -- Create esdArrays map while providing entry for unspecified
               -- expressions.
{-
             , esdArrays =
                 Map.union (esArrays es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memScalarArrays))
-}
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
          pvcStartLoc :: LSS.SymBlockID
        , pvcEndLoc :: Maybe LSS.SymBlockID
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
               , pvcAssumptions = ps ^. LSS.pathAssertions
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
        -- Check static fields
        do forM_ (Map.toList $ ps ^. JSS.pathMemory . JSS.memStaticFields) $ \(f,_jvmVal) -> do
             let clName = JSS.slashesToDots (JSS.fieldIdClass f)
             let fName = clName ++ "." ++ JSS.fieldIdName f
             pvcgFail $ ftext $ "Modifies the static field " ++ fName ++ "."
        -- Check instance fields
        forM_ (Map.toList (ps ^. JSS.pathMemory . JSS.memInstanceFields)) $ \((ref,f), jval) -> do
          let fieldName = show (JSS.fieldIdName f)
                            ++ " of " ++ esdRefName ref esd
          case Map.lookup (ref,f) (esdInstanceFields esd) of
            Nothing ->
              pvcgFail $ ftext $ "Modifies the undefined field " ++ fieldName ++ "."
            Just sval -> do
              case (jval,sval) of
                (_,Nothing) -> return ()
                (jv, Just sv) | jv == sv -> return ()
                (JSS.RValue jref, Just (JSS.RValue _)) ->
                  pvcgFail $ ftext $
                    "Assigns an unexpected value " ++ esdRefName jref esd
                       ++ " to " ++ fieldName ++ "."
                (JSS.IValue jvmNode, Just (JSS.IValue specNode)) ->
                  pvcgAssertEq fieldName jvmNode specNode
                (JSS.LValue jvmNode, Just (JSS.LValue specNode)) ->
                  pvcgAssertEq fieldName jvmNode specNode
                (_, Just _) ->
                  error "internal: comparePathStates encountered illegal field type."
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
        pvcgAssert "final assertions" (ps ^. LSS.pathAssertions)

-- verifyMethodSpec and friends {{{2

mkSpecVC :: (MonadIO m, Functor m, LSS.MonadException m) =>
            SharedContext LSSCtx
         -> VerifyParams
         -> ExpectedStateDef
         -> LSS.Simulator SpecBackend m [PathVC]
mkSpecVC sc params esd = do
  let ir = vpSpec params
  -- Log execution.
  setVerbosity (simVerbose (vpOpts params))
  -- Add method spec overrides.
  mapM_ (overrideFromSpec sc (specPos ir)) (vpOver params)
  -- Execute code.
  LSS.run
  returnVal <- LSS.getProgramReturnValue
  ps <- fromMaybe (error "no path in mkSpecVC") <$> LSS.getPath
  -- TODO: handle exceptional or breakpoint terminations
  return $ map (generateVC ir esd) [(ps, Nothing, Right returnVal)]

data VerifyParams = VerifyParams
  { vpCode    :: LSS.Codebase (SAWBackend LSSCtx Lit)
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
  case specValidationPlan ir of
    Skip -> putStrLn $ "WARNING: skipping verification of " ++
                       show (LSS.sdName (specFunction ir))
    RunVerify script -> do
      forM_ results $ \pvc -> do
        let mkVState nm cfn =
              VState { vsVCName = nm
                     , vsMethodSpec = ir
                     , vsVerbosity = verb
                     -- , vsFromBlock = esdStartLoc esd
                     , vsEvalContext = evalContextFromPathState sc ps
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
       -- , vsFromBlock :: LSS.SymBlockId
         -- | Evaluation context used for parsing expressions during
         -- verification.
       , vsEvalContext :: EvalContext
       , vsInitialAssignments :: [(TC.LLVMExpr, SharedTerm LSSCtx)]
       , vsCounterexampleFn :: CounterexampleFn
       , vsStaticErrors :: [Doc]
       }

type Verbosity = Int
