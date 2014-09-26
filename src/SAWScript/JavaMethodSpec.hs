{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
module SAWScript.JavaMethodSpec
  ( JavaMethodSpecIR
  , specMethod
  , specName
  , specMethodClass
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
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Error (Error(..), ErrorT, runErrorT, throwError)
import Control.Monad.State
import Data.Int
import Data.List (intercalate) -- foldl', intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP

import Language.JVM.Common (ppFldId)
import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.JavaExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.JavaMethodSpecIR
import SAWScript.VerificationCheck

import qualified Verifier.Java.Simulator as JSS
import qualified Data.JVM.Symbolic.AST as JSS
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm

import Verifier.SAW.Cryptol (scCryptolEq)

-- JSS Utilities {{{1

type SpecPathState = JSS.Path (SharedContext JSSCtx)
type SpecJavaValue = JSS.Value (SharedTerm JSSCtx)

type Verbosity = Int

-- | Set value of bound to instance field in path state.
setInstanceFieldValue :: JSS.Ref -> JSS.FieldId -> SpecJavaValue
                      -> SpecPathState -> SpecPathState
setInstanceFieldValue r f v =
  JSS.pathMemory . JSS.memInstanceFields %~ Map.insert (r, f) v

-- | Set value of bound to static field in path state.
setStaticFieldValue :: JSS.FieldId -> SpecJavaValue
                    -> SpecPathState -> SpecPathState
setStaticFieldValue f v =
  JSS.pathMemory . JSS.memStaticFields %~ Map.insert f v

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValue :: JSS.Ref -> Int32 -> SharedTerm JSSCtx
              -> SpecPathState -> SpecPathState
setArrayValue r n v =
  JSS.pathMemory . JSS.memScalarArrays %~ Map.insert r (n, v)

-- | Returns value constructor from node.
mkJSSValue :: JSS.Type -> n -> JSS.Value n
mkJSSValue JSS.BooleanType n = JSS.IValue n
mkJSSValue JSS.ByteType    n = JSS.IValue n
mkJSSValue JSS.CharType    n = JSS.IValue n
mkJSSValue JSS.IntType     n = JSS.IValue n
mkJSSValue JSS.LongType    n = JSS.LValue n
mkJSSValue JSS.ShortType   n = JSS.IValue n
mkJSSValue _ _ = error "internal: illegal type"

-- | Add assumption for predicate to path state.
addAssumption :: SharedContext JSSCtx -> SharedTerm JSSCtx -> SpecPathState -> IO SpecPathState
addAssumption sc x p = do
  andOp <- liftIO $ scApplyPreludeAnd sc
  p & JSS.pathAssertions %%~ \a -> liftIO (andOp a x)

-- | Add assertion for predicate to path state.
addAssertion :: SharedContext JSSCtx -> SharedTerm JSSCtx -> SpecPathState -> IO SpecPathState
addAssertion sc x p = do
  -- TODO: p becomes an additional VC in this case
  andOp <- liftIO $ scApplyPreludeAnd sc
  p & JSS.pathAssertions %%~ \a -> liftIO (andOp a x)

-- EvalContext {{{1

-- | Contextual information needed to evaluate expressions.
data EvalContext = EvalContext {
         ecContext :: SharedContext JSSCtx
       , ecLocals :: Map JSS.LocalVariableIndex SpecJavaValue
       , ecPathState :: SpecPathState
       , ecJavaExprs :: Map String TC.JavaExpr
       }

evalContextFromPathState :: SharedContext JSSCtx -> Map String TC.JavaExpr -> SpecPathState -> EvalContext
evalContextFromPathState sc m ps =
  let Just f = JSS.currentCallFrame ps
      localMap = f ^. JSS.cfLocals
  in EvalContext {
         ecContext = sc
       , ecLocals = localMap
       , ecPathState = ps
       , ecJavaExprs = m
       }

data ExprEvalError
  = EvalExprUndefined TC.JavaExpr
  | EvalExprBadJavaType String TC.JavaExpr
  | EvalExprBadLogicType String String
  | EvalExprUnknownArray TC.JavaExpr
  | EvalExprUnknownLocal JSS.LocalVariableIndex TC.JavaExpr
  | EvalExprUnknownField JSS.FieldId TC.JavaExpr
  | EvalExprOther String

evalErrExpr :: ExprEvalError -> TC.JavaExpr
evalErrExpr (EvalExprUndefined e) = e
evalErrExpr (EvalExprUnknownArray e) = e
evalErrExpr (EvalExprUnknownLocal _ e) = e
evalErrExpr (EvalExprUnknownField _ e) = e
evalErrExpr (EvalExprBadJavaType _ _) = error "evalErrExpr: EvalExprBadJavaType"
evalErrExpr (EvalExprBadLogicType _ _) = error "evalErrExpr: EvalExprBadLogicType"
evalErrExpr (EvalExprOther _) = error "evalErrExpr: EvalExprOther"

instance Error ExprEvalError where
  strMsg = EvalExprOther
  noMsg = EvalExprOther "empty ExprEvalError"

type ExprEvaluator a = ErrorT ExprEvalError IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either ExprEvalError b)
runEval v = liftIO (runErrorT v)

-- or undefined subexpression if not.
-- N.B. This method assumes that the Java path state is well-formed, the
-- the JavaExpression syntactically referes to the correct type of method
-- (static versus instance), and correct well-typed arguments.  It does
-- not assume that all the instanceFields in the JavaEvalContext are initialized.
evalJavaExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator SpecJavaValue
evalJavaExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.Local _ idx _ ->
              case Map.lookup idx (ecLocals ec) of
                Just v -> return v
                Nothing -> throwError $ EvalExprUnknownLocal idx expr
            TC.InstanceField r f -> do
              JSS.RValue ref <- eval r
              let ifields = (ecPathState ec) ^. JSS.pathMemory . JSS.memInstanceFields
              case Map.lookup (ref, f) ifields of
                Just v -> return v
                Nothing -> throwError $ EvalExprUnknownField f expr
            TC.StaticField f -> do
              let sfields = (ecPathState ec) ^. JSS.pathMemory . JSS.memStaticFields
              case Map.lookup f sfields of
                Just v -> return v
                Nothing -> throwError $ EvalExprUnknownField f expr

evalJavaRefExpr :: TC.JavaExpr -> EvalContext -> ExprEvaluator JSS.Ref
evalJavaRefExpr expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue ref -> return ref
    _ -> throwError $ EvalExprBadJavaType "evalJavaRefExpr" expr

evalJavaExprAsLogic :: TC.JavaExpr -> EvalContext -> ExprEvaluator (SharedTerm JSSCtx)
evalJavaExprAsLogic expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue r ->
      let arrs = (ecPathState ec) ^. JSS.pathMemory . JSS.memScalarArrays in
      case Map.lookup r arrs of
        Nothing    -> throwError $ EvalExprUnknownArray expr
        Just (_,n) -> return n
    JSS.IValue n -> return n
    JSS.LValue n -> return n
    _ -> throwError $ EvalExprBadJavaType "evalJavaExprAsLogic" expr

-- | Evaluates a typed expression in the context of a particular state.
evalLogicExpr :: TC.LogicExpr -> EvalContext -> ExprEvaluator (SharedTerm JSSCtx)
evalLogicExpr initExpr ec = do
  let sc = ecContext ec
      getExprs =
        filter (not . TC.isClassJavaExpr . snd) . Map.toList . ecJavaExprs
      exprs = getExprs ec
  args <- forM exprs $ \(_name, expr) -> do
    t <- evalJavaExprAsLogic expr ec
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) (TC.logicExprJavaExprs initExpr)
  liftIO $ TC.useLogicExpr sc initExpr argTerms

-- | Return Java value associated with mixed expression.
evalMixedExpr :: TC.MixedExpr -> EvalContext
              -> ExprEvaluator SpecJavaValue
evalMixedExpr (TC.LE expr) ec = do
  n <- evalLogicExpr expr ec
  let sc = ecContext ec
  ty <- liftIO $ scTypeOf sc n
  ss <- liftIO $ basic_ss sc
  ty' <- liftIO $ rewriteSharedTerm sc ss ty
  case (asBitvectorType ty', asBoolType ty') of
    (Just 32, _) -> return (JSS.IValue n)
    (Just 64, _) -> return (JSS.LValue n)
    (Just _, _) -> throwError (EvalExprBadLogicType "evalMixedExpr" (show ty'))
    (Nothing, Just _) -> do
      b <- liftIO $ do
        boolTy <- scBoolType sc
        false <- scBool sc False
        -- TODO: fix this to work in a different way. This is endian-specific.
        scVector sc boolTy (replicate 31 false ++ [n])
      return (JSS.IValue b)
    (Nothing, Nothing) ->
      throwError (EvalExprBadLogicType "evalMixedExpr" (show ty'))
evalMixedExpr (TC.JE expr) ec = evalJavaExpr expr ec

evalMixedExprAsLogic :: TC.MixedExpr -> EvalContext
                     -> ExprEvaluator (SharedTerm JSSCtx)
evalMixedExprAsLogic (TC.LE expr) = evalLogicExpr expr
evalMixedExprAsLogic (TC.JE expr) = evalJavaExprAsLogic expr

-- Method specification overrides {{{1
-- OverrideComputation definition {{{2

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         ocsLoc :: JSS.Breakpoint
       , ocsEvalContext :: !EvalContext
       , ocsResultState :: !SpecPathState
       , ocsReturnValue :: !(Maybe SpecJavaValue)
       , ocsErrors :: [OverrideError]
       }

data OverrideError
   = UndefinedExpr TC.JavaExpr
   | FalseAssertion Pos
   | AliasingInputs !TC.JavaExpr !TC.JavaExpr
   | JavaException JSS.Ref
   | SimException String
   | InvalidType String
   | Abort
   deriving (Show)

ppOverrideError :: OverrideError -> String
ppOverrideError (UndefinedExpr expr) =
  "Could not evaluate " ++ show (TC.ppJavaExpr expr) ++ "."
ppOverrideError (FalseAssertion p)   = "Assertion at " ++ show p ++ " is false."
ppOverrideError (AliasingInputs x y) =
 "The expressions " ++ show (TC.ppJavaExpr x) ++ " and " ++ show (TC.ppJavaExpr y)
    ++ " point to the same reference, but are not allowed to alias each other."
ppOverrideError (JavaException _)    = "A Java exception was thrown."
ppOverrideError (SimException s)     = "Simulation exception: " ++ s ++ "."
ppOverrideError (InvalidType ty)     = "Invalid type in modify clause: " ++ show ty
ppOverrideError Abort                = "Path was aborted."

data OverrideResult
   = SuccessfulRun (JSS.Path (SharedContext JSSCtx)) (Maybe JSS.Breakpoint) (Maybe SpecJavaValue)
   | FalseAssumption
   | FailedRun (JSS.Path (SharedContext JSSCtx)) (Maybe JSS.Breakpoint) [OverrideError]
   -- deriving (Show)

type RunResult = ( JSS.Path (SharedContext JSSCtx)
                 , Maybe JSS.Breakpoint
                 , Either [OverrideError] (Maybe SpecJavaValue)
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
    Left err -> ocError $ UndefinedExpr (evalErrExpr err)
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
ocAssert :: Pos -> String -> SharedTerm JSSCtx -> OverrideComputation ()
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
ocStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef ->
    ocEval (evalMixedExpr rhsExpr) $ \value ->
      ocModifyResultState $ setInstanceFieldValue lhsRef f value
ocStep (EnsureStaticField _pos f rhsExpr) = do
  ocEval (evalMixedExpr rhsExpr) $ \value ->
    ocModifyResultState $ setStaticFieldValue f value
ocStep (EnsureArray _pos lhsExpr rhsExpr) = do
  ocEval (evalJavaRefExpr lhsExpr) $ \lhsRef ->
    ocEval (evalMixedExprAsLogic rhsExpr) $ \rhsVal -> do
      sc <- gets (ecContext . ocsEvalContext)
      ss <- liftIO $ basic_ss sc
      ty <- liftIO $ scTypeOf sc rhsVal >>= rewriteSharedTerm sc ss
      case ty of
        (isVecType (const (return ())) -> Just (n :*: _)) ->
          ocModifyResultState $ setArrayValue lhsRef (fromIntegral n) rhsVal
        _ -> ocError (InvalidType (show ty))
ocStep (ModifyInstanceField refExpr f) =
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef -> do
    sc <- gets (ecContext . ocsEvalContext)
    let tp = JSS.fieldIdType f
        w = fromIntegral $ JSS.stackWidth tp
    logicType <- liftIO $ scBitvector sc (fromInteger w)
    n <- liftIO $ scFreshGlobal sc (TC.ppJavaExpr refExpr) logicType
    ocModifyResultState $ setInstanceFieldValue lhsRef f (mkJSSValue tp n)
ocStep (ModifyStaticField f) = do
  sc <- gets (ecContext . ocsEvalContext)
  let tp = JSS.fieldIdType f
      w = fromIntegral $ JSS.stackWidth tp
  logicType <- liftIO $ scBitvector sc (fromInteger w)
  n <- liftIO $ scFreshGlobal sc (ppFldId f) logicType
  ocModifyResultState $ setStaticFieldValue f (mkJSSValue tp n)
ocStep (ModifyArray refExpr ty) = do
  ocEval (evalJavaRefExpr refExpr) $ \ref -> do
    sc <- gets (ecContext . ocsEvalContext)
    mtp <- liftIO $ TC.logicTypeOfActual sc ty
    case mtp of
      Nothing -> ocError (InvalidType (show ty))
      Just tp -> do
        rhsVal <- liftIO $ scFreshGlobal sc (TC.ppJavaExpr refExpr) tp
        ss <- liftIO $ basic_ss sc
        lty <- liftIO $ scTypeOf sc rhsVal >>= rewriteSharedTerm sc ss
        case lty of
          (isVecType (const (return ())) -> Just (n :*: _)) ->
            ocModifyResultState $ setArrayValue ref (fromIntegral n) rhsVal
          _ -> ocError (InvalidType (show ty))
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
       do -- Build map from references to expressions that map to them.
          let exprs = bsRefExprs bs
          ocEval (\_ -> mapM (flip evalJavaRefExpr ec) exprs) $ \refs -> do
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
       let sc = ecContext ec
       -- Verify the initial logic assignments
       forM_ (bsLogicAssignments bs) $ \(pos, lhs, rhs) -> do
         ocEval (evalJavaExprAsLogic lhs) $ \lhsVal ->
           ocEval (evalMixedExprAsLogic rhs) $ \rhsVal ->
             ocAssert pos "Override value assertion"
                =<< liftIO (scEq sc lhsVal rhsVal)
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

checkClassesInitialized :: JSS.MonadSim (SharedContext JSSCtx) m =>
                           Pos -> String -> [String] -> JSS.Simulator (SharedContext JSSCtx) m ()
checkClassesInitialized pos nm requiredClasses = do
  forM_ requiredClasses $ \c -> do
    mem <- JSS.getMem (PP.text "checkClassesInitialized")
    let status = Map.lookup c (mem ^. JSS.memInitialization)
    when (status /= Just JSS.Initialized) $
      let msg = "The method spec \'" ++ nm ++ "\' requires that the class "
                  ++ JSS.slashesToDots c ++ " is initialized.  SAWScript does not "
                  ++ "currently support methods that initialize new classes."
       in throwIOExecException pos (ftext msg) ""

execOverride :: JSS.MonadSim (SharedContext JSSCtx) m
             => SharedContext JSSCtx
             -> Pos
             -> JavaMethodSpecIR
             -> Maybe JSS.Ref
             -> [JSS.Value (SharedTerm JSSCtx)]
             -> JSS.Simulator (SharedContext JSSCtx) m ()
execOverride sc pos ir mbThis args = do
  -- Execute behaviors.
  initPS <- JSS.getPath (PP.text "MethodSpec override")
  let bsl = specBehaviors ir -- Map.lookup (JSS.BreakPC 0) (specBehaviors ir) -- TODO
  let method = specMethod ir
      argLocals = map (JSS.localIndexOfParameter method) [0..] `zip` args
      m = specJavaExprNames ir
  let ec = EvalContext { ecContext = sc
                       , ecLocals =  Map.fromList $
                           case mbThis of
                             Just th -> (0, JSS.RValue th) : argLocals
                             Nothing -> argLocals
                       , ecPathState = initPS
                       , ecJavaExprs = m
                       }
  -- Check class initialization.
  checkClassesInitialized pos (specName ir) (specInitializedClasses ir)
  -- Execute behavior.
  res <- liftIO $ execBehavior [bsl] ec initPS
  -- Create function for generation resume actions.
  case res of
    [(_, _, Left el)] -> do
      let msg = "Unsatisified assertions in " ++ specName ir ++ ":\n"
                ++ intercalate "\n" (map ppOverrideError el)
      fail msg
    [(ps, _, Right mval)] ->
      JSS.modifyPathM_ (PP.text "path result") $ \_ ->
        return $
        case (mval, ps ^. JSS.pathStack) of
          (Just val, [])     -> ps & set JSS.pathRetVal (Just val)
          (Just val, (f:fr)) -> ps & set JSS.pathStack  (f' : fr)
            where f' = f & JSS.cfOpds %~ (val :)
          (Nothing,  [])     -> ps & set JSS.pathRetVal Nothing
          (Nothing,  _:_)    -> ps
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: JSS.MonadSim (SharedContext JSSCtx) m =>
                    SharedContext JSSCtx
                 -> Pos
                 -> JavaMethodSpecIR
                 -> JSS.Simulator (SharedContext JSSCtx) m ()
overrideFromSpec de pos ir
  | JSS.methodIsStatic method =
      JSS.overrideStaticMethod cName key $ \args ->
        execOverride de pos ir Nothing args
  | otherwise =
      JSS.overrideInstanceMethod cName key $ \thisVal args ->
        execOverride de pos ir (Just thisVal) args
 where cName = JSS.className (specMethodClass ir)
       method = specMethod ir
       key = JSS.methodKey method

-- ExpectedStateDef {{{1

-- | Describes expected result of computation.
data ExpectedStateDef = ESD {
         -- | Location that we started from.
         esdStartLoc :: JSS.Breakpoint
         -- | Initial path state (used for evaluating expressions in
         -- verification).
       , esdInitialPathState :: SpecPathState
       , esdJavaExprs :: Map String TC.JavaExpr
         -- | Stores initial assignments.
       , esdInitialAssignments :: [(TC.JavaExpr, SharedTerm JSSCtx)]
         -- | Map from references back to Java expressions denoting them.
       , esdRefExprMap :: Map JSS.Ref [TC.JavaExpr]
         -- | Expected return value or Nothing if method returns void.
       , esdReturnValue :: Maybe (JSS.Value (SharedTerm JSSCtx))
         -- | Maps instance fields to expected value, or Nothing if value may
         -- be arbitrary.
       , esdInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe (JSS.Value (SharedTerm JSSCtx)))
         -- | Maps static fields to expected value, or Nothing if value may
         -- be arbitrary.
       , esdStaticFields :: Map JSS.FieldId (Maybe (JSS.Value (SharedTerm JSSCtx)))
         -- | Maps reference to expected node, or Nothing if value may be arbitrary.
       , esdArrays :: Map JSS.Ref (Maybe (Int32, SharedTerm JSSCtx))
       }

esdRefName :: JSS.Ref -> ExpectedStateDef -> String
esdRefName JSS.NullRef _ = "null"
esdRefName ref esd =
  case Map.lookup ref (esdRefExprMap esd) of
    Just cl -> ppJavaExprEquivClass cl
    Nothing -> "fresh allocation"

-- Initial state generation {{{1

-- | State for running the behavior specifications in a method override.
data ESGState = ESGState {
         esContext :: SharedContext JSSCtx
       , esMethod :: JSS.Method
       , esJavaExprs :: Map String TC.JavaExpr
       , esExprRefMap :: Map TC.JavaExpr JSS.Ref
       , esInitialAssignments :: [(TC.JavaExpr, SharedTerm JSSCtx)]
       , esInitialPathState :: SpecPathState
       , esReturnValue :: Maybe SpecJavaValue
       , esInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe SpecJavaValue)
       , esStaticFields :: Map JSS.FieldId (Maybe SpecJavaValue)
       , esArrays :: Map JSS.Ref (Maybe (Int32, SharedTerm JSSCtx))
       , esErrors :: [String]
       }

-- | Monad used to execute statements in a behavior specification for a method
-- override.
type ExpectedStateGenerator = StateT ESGState IO

esEval :: (EvalContext -> ExprEvaluator b) -> ExpectedStateGenerator b
esEval fn = do
  sc <- gets esContext
  m <- gets esJavaExprs
  initPS <- gets esInitialPathState
  let ec = evalContextFromPathState sc m initPS
  res <- runEval (fn ec)
  case res of
    Left expr -> error "internal: esEval failed to evaluate expression"
    Right v   -> return v

esError :: String -> ExpectedStateGenerator ()
esError err = modify $ \es -> es { esErrors = err : esErrors es }

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

esAddEqAssertion :: SharedContext JSSCtx -> String -> SharedTerm JSSCtx -> SharedTerm JSSCtx
                 -> ExpectedStateGenerator ()
esAddEqAssertion sc _nm x y =
  do prop <- liftIO (scEq sc x y)
     esModifyInitialPathStateIO (addAssertion sc prop)

-- | Assert that two terms are equal.
esAssertEq :: String -> SpecJavaValue -> SpecJavaValue
           -> ExpectedStateGenerator ()
esAssertEq nm (JSS.RValue x) (JSS.RValue y) = do
  when (x /= y) $
    esError $ "internal: Asserted different references for " ++ nm ++ " are equal."
esAssertEq nm (JSS.IValue x) (JSS.IValue y) = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq nm (JSS.LValue x) (JSS.LValue y) = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq _ _ _ = esError "internal: esAssertEq given illegal arguments."

-- | Set value in initial state.
esSetJavaValue :: TC.JavaExpr -> SpecJavaValue -> ExpectedStateGenerator ()
esSetJavaValue e@(CC.Term exprF) v = do
  -- liftIO $ putStrLn $ "Setting Java value for " ++ show e
  case exprF of
    -- TODO: the following is ugly, and doesn't make good use of lenses
    TC.Local _ idx _ -> do
      ps <- esGetInitialPathState
      let ls = case JSS.currentCallFrame ps of
                 Just cf -> cf ^. JSS.cfLocals
                 Nothing -> Map.empty
          ps' = (JSS.pathStack %~ updateLocals) ps
          updateLocals (f:r) = (JSS.cfLocals %~ Map.insert idx v) f : r
          updateLocals [] =
            error "internal: esSetJavaValue of local with empty call stack"
      -- liftIO $ putStrLn $ "Local " ++ show idx ++ " with stack " ++ show ls
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
    TC.StaticField f -> do
      ps <- esGetInitialPathState
      case Map.lookup f (ps ^. JSS.pathMemory . JSS.memStaticFields) of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing -> esPutInitialPathState $
          (JSS.pathMemory . JSS.memStaticFields %~ Map.insert f v) ps

esResolveLogicExprs :: TC.JavaExpr -> SharedTerm JSSCtx -> [TC.LogicExpr]
                    -> ExpectedStateGenerator (SharedTerm JSSCtx)
esResolveLogicExprs e tp [] = do
  sc <- gets esContext
  -- Create input variable.
  -- liftIO $ putStrLn $ "Creating global of type: " ++ show tp
  -- TODO: look e up in map, instead
  liftIO $ scFreshGlobal sc (TC.ppJavaExpr e) tp
esResolveLogicExprs _ _ (hrhs:rrhs) = do
  sc <- gets esContext
  -- liftIO $ putStrLn $ "Evaluating " ++ show hrhs
  t <- esEval $ evalLogicExpr hrhs
  -- Add assumptions for other equivalent expressions.
  forM_ rrhs $ \rhsExpr -> do
    rhs <- esEval $ evalLogicExpr rhsExpr
    esModifyInitialPathStateIO $ \s0 -> do prop <- scCryptolEq sc t rhs
                                           addAssumption sc prop s0
  -- Return value.
  return t

esSetLogicValues :: SharedContext JSSCtx -> [TC.JavaExpr] -> SharedTerm JSSCtx
                 -> [TC.LogicExpr]
                 -> ExpectedStateGenerator ()
esSetLogicValues _ [] _ _ = esError "empty class passed to esSetLogicValues"
esSetLogicValues sc cl@(rep:_) tp lrhs = do
  -- liftIO $ putStrLn $ "Setting logic values for: " ++ show cl
  -- Get value of rhs.
  value <- esResolveLogicExprs rep tp lrhs
  -- Update Initial assignments.
  modify $ \es -> es { esInitialAssignments =
                         map (\e -> (e,value)) cl ++  esInitialAssignments es }
  ty <- liftIO $ scTypeOf sc value
  -- Update value.
  case ty of
    (isVecType (const (return ())) -> Just (n :*: _)) -> do
       refs <- forM cl $ \expr -> do
                 JSS.RValue ref <- esEval $ evalJavaExpr expr
                 return ref
       forM_ refs $
         \r -> esModifyInitialPathState (setArrayValue r (fromIntegral n) value)
    (asBitvectorType -> Just 32) ->
       mapM_ (flip esSetJavaValue (JSS.IValue value)) cl
    (asBitvectorType -> Just 64) ->
       mapM_ (flip esSetJavaValue (JSS.LValue value)) cl
    _ -> esError "internal: initializing Java values given bad rhs."

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
    _ -> esError "internal: Incompatible values assigned to instance field."
  -- Define instance field post condition.
  modify $ \es ->
    es { esInstanceFields = Map.insert (ref,f) (Just value) (esInstanceFields es) }
esStep (EnsureStaticField _pos f rhsExpr) = do
  value <- esEval $ evalMixedExpr rhsExpr
  -- Get dag engine
  sc <- gets esContext
  -- Check that instance field is already defined, if so add an equality check for that.
  sfMap <- gets esStaticFields
  case (Map.lookup f sfMap, value) of
    (Nothing, _) -> return ()
    (Just Nothing, _) -> return ()
    (Just (Just (JSS.RValue prev)), JSS.RValue new)
      | prev == new -> return ()
    (Just (Just (JSS.IValue prev)), JSS.IValue new) ->
       esAddEqAssertion sc (ppFldId f) prev new
    (Just (Just (JSS.LValue prev)), JSS.LValue new) ->
       esAddEqAssertion sc (ppFldId f) prev new
    -- TODO: See if we can give better error message here.
    -- Perhaps this just ends up meaning that we need to verify the assumptions in this
    -- behavior are inconsistent.
    _ -> esError "internal: Incompatible values assigned to static field."
  modify $ \es ->
    es { esStaticFields = Map.insert f (Just value) (esStaticFields es) }
esStep (ModifyInstanceField refExpr f) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember (ref, f) (esInstanceFields es)) $ do
    put es { esInstanceFields = Map.insert (ref,f) Nothing (esInstanceFields es) }
esStep (ModifyStaticField f) = do
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember f (esStaticFields es)) $ do
    put es { esStaticFields = Map.insert f Nothing (esStaticFields es) }
esStep (EnsureArray _pos lhsExpr rhsExpr) = do
  -- Evaluate expressions.
  ref    <- esEval $ evalJavaRefExpr lhsExpr
  value  <- esEval $ evalMixedExprAsLogic rhsExpr
  -- Get dag engine
  sc <- gets esContext
  ss <- liftIO $ basic_ss sc
  ty <- liftIO $ scTypeOf sc value >>= rewriteSharedTerm sc ss
  case ty of
    (isVecType (const (return ())) -> Just (w :*: _)) -> do
      let l = fromIntegral w
      -- Check if array has already been assigned value.
      aMap <- gets esArrays
      case Map.lookup ref aMap of
        Just (Just (oldLen, prev))
          | l /= fromIntegral oldLen -> esError "internal: array changed size."
          | otherwise -> esAddEqAssertion sc (show lhsExpr) prev value
        _ -> return ()
      -- Define instance field post condition.
      modify $ \es -> es { esArrays = Map.insert ref (Just (l, value)) (esArrays es) }
    _ -> esError "internal: right hand side of array ensure clause has non-array type."
esStep (ModifyArray refExpr _) = do
  ref <- esEval $ evalJavaRefExpr refExpr
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember ref (esArrays es)) $ do
    put es { esArrays = Map.insert ref Nothing (esArrays es) }

initializeVerification :: JSS.MonadSim (SharedContext JSSCtx) m =>
                          SharedContext JSSCtx
                       -> JavaMethodSpecIR
                       -> BehaviorSpec
                       -> RefEquivConfiguration
                       -> JSS.Simulator (SharedContext JSSCtx) m ExpectedStateDef
initializeVerification sc ir bs refConfig = do
  exprRefs <- mapM (JSS.genRef . TC.jssTypeOfActual . snd) refConfig
  let refAssignments = (map fst refConfig `zip` exprRefs)
      m = specJavaExprNames ir
      --key = JSS.methodKey (specMethod ir)
      pushFrame cs = fromMaybe (error "internal: failed to push call frame") mcs'
        where
          mcs' = JSS.pushCallFrame (JSS.className (specMethodClass ir))
                                   (specMethod ir)
                                   JSS.entryBlock -- FIXME: not the right block
                                   Map.empty
                                   cs
  -- liftIO $ print refAssignments
  JSS.modifyCSM_ (return . pushFrame)
  let updateInitializedClasses mem =
        foldr (flip JSS.setInitializationStatus JSS.Initialized)
              mem
              (specInitializedClasses ir)
  JSS.modifyPathM_ (PP.text "initializeVerification") $
    return . (JSS.pathMemory %~ updateInitializedClasses)
  -- TODO: add breakpoints once local specs exist
  --forM_ (Map.keys (specBehaviors ir)) $ JSS.addBreakpoint clName key
  -- TODO: set starting PC
  initPS <- JSS.getPath (PP.text "initializeVerification")
  let initESG = ESGState { esContext = sc
                         , esMethod = specMethod ir
                         , esJavaExprs = m
                         , esExprRefMap = Map.fromList
                             [ (e, r) | (cl,r) <- refAssignments, e <- cl ]
                         , esInitialAssignments = []
                         , esInitialPathState = initPS
                         , esReturnValue = Nothing
                         , esInstanceFields = Map.empty
                         , esStaticFields = Map.empty
                         , esArrays = Map.empty
                         , esErrors = []
                         }
  -- liftIO $ putStrLn "Starting to initialize state."
  es <- liftIO $ flip execStateT initESG $ do
          -- Set references
          -- liftIO $ putStrLn "Setting references."
          forM_ refAssignments $ \(cl,r) ->
            forM_ cl $ \e -> esSetJavaValue e (JSS.RValue r)
          -- Set initial logic values.
          -- liftIO $ putStrLn "Setting logic values."
          lcs <- liftIO $ bsLogicClasses sc m bs refConfig
          case lcs of
            Nothing ->
              let msg = "Unresolvable cyclic dependencies between assumptions."
               in throwIOExecException (specPos ir) (ftext msg) ""
            Just assignments -> mapM_ (\(l,t,r) -> esSetLogicValues sc l t r) assignments
          -- Process commands
          -- liftIO $ putStrLn "Running commands."
          mapM esStep (bsCommands bs)
  let ps = esInitialPathState es
      errs = esErrors es
      indent = (' ' :) . (' ' :)
  unless (null errs) $ fail . unlines $
    "Errors while initializing verification:" : map indent errs
  JSS.modifyPathM_ (PP.text "initializeVerification") (\_ -> return ps)
  return ESD { esdStartLoc = bsLoc bs
             , esdInitialPathState = esInitialPathState es
             , esdInitialAssignments = reverse (esInitialAssignments es)
             , esdJavaExprs = m
             , esdRefExprMap =
                  Map.fromList [ (r, cl) | (cl,r) <- refAssignments ]
             , esdReturnValue = esReturnValue es
               -- Create esdArrays map while providing entry for unspecified
               -- expressions.
             , esdInstanceFields =
                 Map.union (esInstanceFields es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memInstanceFields))
             , esdStaticFields =
                 Map.union (esStaticFields es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memStaticFields))
               -- Create esdArrays map while providing entry for unspecified
               -- expressions.
             , esdArrays =
                 Map.union (esArrays es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memScalarArrays))
             }

-- MethodSpec verification {{{1

-- PathVC {{{2

-- | Describes the verification result arising from one symbolic execution path.
data PathVC = PathVC {
          pvcStartLoc :: JSS.Breakpoint
        , pvcEndLoc :: Maybe JSS.Breakpoint
        , pvcInitialAssignments :: [(TC.JavaExpr, SharedTerm JSSCtx)]
          -- | Assumptions on inputs.
        , pvcAssumptions :: SharedTerm JSSCtx
          -- | Static errors found in path.
        , pvcStaticErrors :: [Doc]
          -- | What to verify for this result.
        , pvcChecks :: [VerificationCheck JSSCtx]
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
  where ppAssignment (expr, tm) = hsep [ text (TC.ppJavaExpr expr)
                                       , text ":="
                                       , scPrettyTermDoc tm
                                       ]

type PathVCGenerator = State PathVC

-- | Add verification condition to list.
pvcgAssertEq :: String -> SharedTerm JSSCtx -> SharedTerm JSSCtx -> PathVCGenerator ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: String -> SharedTerm JSSCtx -> PathVCGenerator ()
pvcgAssert nm v =
  modify $ \pvc -> pvc { pvcChecks = AssertionCheck nm v : pvcChecks pvc }

pvcgFail :: Doc -> PathVCGenerator ()
pvcgFail msg =
  modify $ \pvc -> pvc { pvcStaticErrors = msg : pvcStaticErrors pvc }

-- generateVC {{{2

-- | Compare result with expected state.
generateVC :: JavaMethodSpecIR
           -> ExpectedStateDef -- ^ What is expected
           -> RunResult -- ^ Results of symbolic execution.
           -> PathVC -- ^ Proof oblications
generateVC ir esd (ps, endLoc, res) = do
  let initState  =
        PathVC { pvcInitialAssignments = esdInitialAssignments esd
               , pvcStartLoc = esdStartLoc esd
               , pvcEndLoc = endLoc
               , pvcAssumptions = ps ^. JSS.pathAssertions
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
          (Just (JSS.IValue rv), Just (JSS.IValue srv)) ->
            pvcgAssertEq "return value" rv srv
          (Just (JSS.LValue rv), Just (JSS.LValue srv)) ->
            pvcgAssertEq "return value" rv srv
          (Just (JSS.RValue rv), Just (JSS.RValue srv)) ->
            when (rv /= srv) $
              pvcgFail $ ftext $ "Assigns unexpected return value."
          (Just _, Nothing) ->
            pvcgFail $ ftext $ "Missing return spec for method returning a value."
          _ ->  pvcgFail $ ftext $
                "internal: The Java method has an unsupported return type."
        -- Check initialization
        do let sinits = Set.fromList (specInitializedClasses ir)
           forM_ (Map.keys (ps ^. JSS.pathMemory . JSS.memInitialization)) $ \cl -> do
             when (cl `Set.notMember` sinits) $ do
               pvcgFail $ ftext $
                 "Initializes extra class " ++ JSS.slashesToDots cl ++ "."
        -- Check static fields
        forM_ (Map.toList $ ps ^. JSS.pathMemory . JSS.memStaticFields) $ \(f,jval) -> do
          let fieldName = show (JSS.fieldIdName f)
                            ++ " of class " ++ (JSS.fieldIdClass f)
          case Map.lookup f (esdStaticFields esd) of
            Nothing ->
              pvcgFail $ ftext $ "Modifies the undefined static field " ++ fieldName ++ "."
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
                  pvcgFail $
                  ftext "internal: comparePathStates encountered illegal field type."
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
                (_, Just _) -> pvcgFail $
                  ftext "internal: comparePathStates encountered illegal field type."
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
        -- Check assertions
        pvcgAssert "final assertions" (ps ^. JSS.pathAssertions)
        -- Check class objects
        forM_ (Map.keys (ps ^. JSS.pathMemory . JSS.memClassObjects)) $ \clNm ->
          pvcgFail $ ftext $ "Allocated class object for " ++ JSS.slashesToDots clNm ++ "."

-- verifyMethodSpec and friends {{{2

mkSpecVC :: JSS.MonadSim (SharedContext JSSCtx) m =>
            SharedContext JSSCtx
         -> VerifyParams
         -> ExpectedStateDef
         -> JSS.Simulator (SharedContext JSSCtx) m [PathVC]
mkSpecVC sc params esd = do
  let ir = vpSpec params
      vrb = simVerbose (vpOpts params)
      ovds = vpOver params
  -- Log execution.
  JSS.setVerbosity vrb
  -- Add method spec overrides.
  when (vrb >= 2) $ liftIO $
       putStrLn $ "Overriding: " ++ show (map specName ovds)
  mapM_ (overrideFromSpec sc (specPos ir)) ovds
  -- Execute code.
  JSS.run
  returnVal <- JSS.getProgramReturnValue
  ps <- JSS.getPath (PP.text "mkSpecVC")
  -- TODO: handle exceptional or breakpoint terminations
  return $ map (generateVC ir esd) [(ps, Nothing, Right returnVal)]

data VerifyParams = VerifyParams
  { vpCode    :: JSS.Codebase
  , vpContext :: SharedContext JSSCtx
  , vpOpts    :: Options
  , vpSpec    :: JavaMethodSpecIR
  , vpOver    :: [JavaMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext JSSCtx -> ExpectedStateDef -> [PathVC] -> IO ()
type Prover =
  VerifyState -> SharedTerm JSSCtx -> IO ()

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc esd results = do
  let ir = vpSpec params
      verb = verbLevel (vpOpts params)
      ps = esdInitialPathState esd
  forM_ results $ \pvc -> do
    let mkVState nm cfn =
          VState { vsVCName = nm
                 , vsMethodSpec = ir
                 , vsVerbosity = verb
                 -- , vsFromBlock = esdStartLoc esd
                 , vsEvalContext = evalContextFromPathState sc m ps
                 , vsInitialAssignments = pvcInitialAssignments pvc
                 , vsCounterexampleFn = cfn
                 , vsStaticErrors = pvcStaticErrors pvc
                 }
        m = esdJavaExprs esd
    if null (pvcStaticErrors pvc) then
     forM_ (pvcChecks pvc) $ \vc -> do
       let vs = mkVState (vcName vc) (vcCounterexample vc)
       g <- scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc
       when (verb >= 2) $ do
         putStr $ "Checking " ++ vcName vc
         when (verb >= 5) $ putStr $ " (" ++ scPrettyTerm g ++ ")"
         putStrLn ""
       prover vs g
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
      when (verb >= 2) $ do
        putStrLn $ "Checking " ++ vsName
        print $ pvcStaticErrors pvc
      when (verb >= 5) $ do
        putStrLn $ "Calling prover to disprove " ++
                 scPrettyTerm (pvcAssumptions pvc)
      prover vs g

data VerifyState = VState {
         vsVCName :: String
       , vsMethodSpec :: JavaMethodSpecIR
       , vsVerbosity :: Verbosity
         -- | Starting Block is used for checking VerifyAt commands.
       -- , vsFromBlock :: JSS.BlockId
         -- | Evaluation context used for parsing expressions during
         -- verification.
       , vsEvalContext :: EvalContext
       , vsInitialAssignments :: [(TC.JavaExpr, SharedTerm JSSCtx)]
       , vsCounterexampleFn :: CounterexampleFn JSSCtx
       , vsStaticErrors :: [Doc]
       }
