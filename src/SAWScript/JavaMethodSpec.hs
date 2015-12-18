{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.JavaMethodSpec
  ( JavaMethodSpecIR
  , specMethod
  , specName
  , specMethodClass
  , SymbolicRunHandler
  , initializeVerification
  , initializeVerification'
  , runValidation
  , checkFinalState
  , overrideFromSpec
  , mkSpecVC
  , PathVC(..)
  , pvcgAssertEq
  , pvcgAssert
  , pvcgFail
  , ppPathVC
  , VerifyParams(..)
  , VerifyState(..)
  , EvalContext(..)
  , ExpectedStateDef(..)
  ) where

-- Imports {{{1

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.State
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP

import Debug.Trace

import Language.JVM.Common (ppFldId)
import qualified SAWScript.CongruenceClosure as CC
import SAWScript.JavaExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.JavaMethodSpecIR
import SAWScript.JavaMethodSpec.Evaluator
import SAWScript.JavaMethodSpec.ExpectedStateDef
import SAWScript.JavaUtils
import SAWScript.PathVC
import SAWScript.TypedTerm
import SAWScript.Value (TopLevel, io)
import SAWScript.VerificationCheck

import Data.JVM.Symbolic.AST (entryBlock)

import Verifier.Java.Simulator hiding (asBool, State)
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

-- JSS Utilities {{{1

type Verbosity = Int

-- EvalContext {{{1

evalErrExpr :: ExprEvalError -> TC.JavaExpr
evalErrExpr (EvalExprUndefined e) = e
evalErrExpr (EvalExprUnknownArray e) = e
evalErrExpr (EvalExprUnknownLocal _ e) = e
evalErrExpr (EvalExprUnknownField _ e) = e
evalErrExpr (EvalExprBadJavaType _ _) =
  error "evalErrExpr: EvalExprBadJavaType"
evalErrExpr (EvalExprBadLogicType _ _) =
  error "evalErrExpr: EvalExprBadLogicType"
evalErrExpr EvalExprNoReturn =
  error "evalErrExpr: EvalExprNoReturn"
evalErrExpr (EvalExprOther _) =
  error "evalErrExpr: EvalExprOther"

-- Method specification overrides {{{1
-- OverrideComputation definition {{{2

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         ocsLoc :: Breakpoint
       , ocsEvalContext :: !EvalContext
       , ocsResultState :: !SpecPathState
       , ocsErrors :: [OverrideError]
       }

data OverrideError
   = UndefinedExpr TC.JavaExpr
   | FalseAssertion Pos
   | AliasingInputs !TC.JavaExpr !TC.JavaExpr
   | JavaExceptionThrown Ref
   | SimException String
   | InvalidType String
   | Abort
   deriving (Show)

ppOverrideError :: OverrideError -> String
ppOverrideError (UndefinedExpr expr) =
  "Could not evaluate " ++ show (TC.ppJavaExpr expr) ++ "."
ppOverrideError (FalseAssertion p)   =
  "Assertion at " ++ show p ++ " is false."
ppOverrideError (AliasingInputs x y) =
 "The expressions " ++ show (TC.ppJavaExpr x) ++ " and " ++
 show (TC.ppJavaExpr y) ++
 " point to the same reference, but are not allowed to alias each other."
ppOverrideError (JavaExceptionThrown _) = "A Java exception was thrown."
ppOverrideError (SimException s)     = "Simulation exception: " ++ s ++ "."
ppOverrideError (InvalidType ty)     =
  "Invalid type in modify clause: " ++ show ty
ppOverrideError Abort                = "Path was aborted."

data OverrideResult
   = SuccessfulRun (Path (SharedContext SAWCtx)) (Maybe Breakpoint) (Maybe SpecJavaValue)
   | FailedRun (Path (SharedContext SAWCtx)) (Maybe Breakpoint) [OverrideError]

type RunResult = ( Path (SharedContext SAWCtx)
                 , Maybe Breakpoint
                 , Either [OverrideError] (Maybe SpecJavaValue)
                 )

orParseResults :: [OverrideResult] -> [RunResult]
orParseResults l =
  [ (ps, block, Left  e) | FailedRun     ps block e <- l ] ++
  [ (ps, block, Right v) | SuccessfulRun ps block v <- l ]

type OverrideComputation m =
  ContT OverrideResult (StateT OCState (SAWJavaSim m))

ocError :: OverrideError -> OverrideComputation m ()
ocError e = modify $ \ocs -> ocs { ocsErrors = e : ocsErrors ocs }

-- OverrideComputation utilities {{{2

-- | Runs an evaluate within an override computation.
ocEval :: (EvalContext -> ExprEvaluator b)
       -> (b -> OverrideComputation m ())
       -> OverrideComputation m ()
ocEval fn m = do
  ec <- gets ocsEvalContext
  res <- runEval (fn ec)
  case res of
    Left e  -> ocError $ UndefinedExpr (evalErrExpr e)
    Right v -> m v

ocDoesEval :: (EvalContext -> ExprEvaluator b)
           -> OverrideComputation m Bool
ocDoesEval fn = do
  ec <- gets ocsEvalContext
  res <- runEval (fn ec)
  return $ either (const False) (const True) res

-- Modify result state
ocModifyResultState :: (SpecPathState -> SpecPathState)
                    -> OverrideComputation m ()
ocModifyResultState fn = do
  bcs <- get
  put $! bcs { ocsResultState = fn (ocsResultState bcs) }

ocModifyResultStateIO :: (SpecPathState -> IO SpecPathState)
                      -> OverrideComputation m ()
ocModifyResultStateIO fn = do
  bcs <- get
  new <- liftIO $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

ocSetReturnValue :: Maybe SpecJavaValue
                 -> OverrideComputation m ()
ocSetReturnValue mrv = do
  bcs <- get
  let ec = ocsEvalContext bcs
      ec' = ec { ecReturnValue = mrv }
  put $! bcs { ocsEvalContext = ec' }

ocSetJavaExpr :: JavaExpr -> SpecJavaValue
              -> OverrideComputation m ()
ocSetJavaExpr e v = do
  ocEval (setJavaExpr e v) $ \ec -> do
    modify $ \ocs -> ocs { ocsEvalContext = ec }
    ocModifyResultState (const (ecPathState ec))

-- | Add assumption for predicate.
ocAssert :: Pos -> String -> SharedTerm SAWCtx -> OverrideComputation m ()
ocAssert p _nm x = do
  sc <- (ecContext . ocsEvalContext) <$> get
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultStateIO (addAssertionPS sc x)

-- ocStep {{{2

evalOrCreate :: JavaExpr
             -> (Ref -> OverrideComputation m ())
             -> OverrideComputation m ()
evalOrCreate e f = do
  exists <- ocDoesEval (evalJavaExpr e)
  if exists
    then ocEval (evalJavaRefExpr e) f
    else do r <- lift $ lift $ genRef (exprType e)
            ocSetJavaExpr e (RValue r)
            f r

ocStep :: BehaviorCommand -> OverrideComputation m ()
ocStep (EnsureInstanceField _pos refExpr f rhsExpr) =
  evalOrCreate refExpr $ \lhsRef ->
  ocEval (evalMixedExpr rhsExpr) $ \value ->
  ocModifyResultState $ setInstanceFieldValuePS lhsRef f value
ocStep (EnsureStaticField _pos f rhsExpr) =
  ocEval (evalMixedExpr rhsExpr) $ \value ->
  ocModifyResultState $ setStaticFieldValuePS f value
ocStep (EnsureArray _pos lhsExpr rhsExpr) =
  evalOrCreate lhsExpr $ \lhsRef ->
  ocEval (evalMixedExprAsLogic rhsExpr) $ \rhsVal -> do
    sc <- gets (ecContext . ocsEvalContext)
    ty <- liftIO $ scTypeOf sc rhsVal >>= scWhnf sc
    case ty of
      (isVecType (const (return ())) -> Just (n :*: _)) ->
        ocModifyResultState $ setArrayValuePS lhsRef (fromIntegral n) rhsVal
      _ -> ocError (InvalidType (show ty))
ocStep (ModifyInstanceField refExpr f) =
  evalOrCreate refExpr $ \lhsRef -> do
    sc <- gets (ecContext . ocsEvalContext)
    let tp = fieldIdType f
        w = fromIntegral $ stackWidth tp
    logicType <- liftIO $ scBitvector sc (fromInteger w)
    n <- liftIO $ scFreshGlobal sc (TC.ppJavaExpr refExpr) logicType
    v <- liftIO $ mkJSSValue sc tp n
    ocModifyResultState $ setInstanceFieldValuePS lhsRef f v
ocStep (ModifyStaticField f) = do
  sc <- gets (ecContext . ocsEvalContext)
  let tp = fieldIdType f
      w = fromIntegral $ stackWidth tp
  logicType <- liftIO $ scBitvector sc (fromInteger w)
  n <- liftIO $ scFreshGlobal sc (ppFldId f) logicType
  v <- liftIO $ mkJSSValue sc tp n
  ocModifyResultState $ setStaticFieldValuePS f v
ocStep (ModifyArray refExpr ty) =
  evalOrCreate refExpr $ \ref -> do
    sc <- gets (ecContext . ocsEvalContext)
    mtp <- liftIO $ TC.logicTypeOfActual sc ty
    case mtp of
      Nothing -> ocError (InvalidType (show ty))
      Just tp -> do
        rhsVal <- liftIO $ scFreshGlobal sc (TC.ppJavaExpr refExpr) tp
        lty <- liftIO $ scTypeOf sc rhsVal >>= scWhnf sc
        case lty of
          (isVecType (const (return ())) -> Just (n :*: _)) ->
            ocModifyResultState $ setArrayValuePS ref (fromIntegral n) rhsVal
          _ -> ocError (InvalidType (show ty))
ocStep (ReturnValue expr) = do
  ocEval (evalMixedExpr expr) $ \val ->
    ocSetReturnValue (Just val)

-- Executing overrides {{{2

execBehavior :: BehaviorSpec
             -> SharedContext SAWCtx
             -> Maybe Ref
             -> [(LocalVariableIndex, SpecJavaValue)]
             -> SpecPathState
             -> SAWJavaSim m [RunResult]
execBehavior bsl sc mbThis argLocals ps = do

  -- Get state of current execution path in simulator.
  fmap orParseResults $ forM [bsl] $ \bs -> do
    let ec = EvalContext { ecContext = sc
                         , ecLocals =  Map.fromList $
                                       case mbThis of
                                       Just th -> (0, RValue th) : argLocals
                                       Nothing -> argLocals
                         , ecReturnValue = Nothing
                         , ecPathState = ps
                         }
    let initOCS =
          OCState { ocsLoc = bsLoc bs
                  , ocsEvalContext = ec
                  , ocsResultState = ps
                  , ocsErrors = []
                  }
    let resCont () = do
          OCState { ocsLoc = loc
                  , ocsResultState = resPS
                  , ocsEvalContext = ecres
                  , ocsErrors = l } <- get
          return $
            if null l then
              SuccessfulRun resPS (Just loc) (ecReturnValue ecres)
            else
              FailedRun resPS (Just loc) l
    flip evalStateT initOCS $ flip runContT resCont $ do
       -- If the return value is a reference, it must be allocated.
       forM_ (bsRefExprs bsl) $ \e -> do
         case e of
           CC.Term(ReturnVal _) -> do
             r <- lift $ lift $ genRef (exprType e)
             ocSetReturnValue (Just (RValue r))
           _ -> return () -- Nothing else to do?

       ec' <- gets ocsEvalContext
       -- Check that all expressions that reference each other may do so.
       do -- Build map from references to expressions that map to them.
          let exprs = bsRefExprs bs
          ocEval (\_ -> mapM (flip evalJavaRefExpr ec') exprs) $ \refs -> do
            let refExprMap =
                  Map.fromListWith (++) $ refs `zip` [[e] | e <- exprs]
            --- Get counterexamples.
            let mayAliasSet = bsMayAliasSet bs
            let badPairs = catMaybes
                         $ map (\cl -> CC.checkEquivalence cl mayAliasSet)
                         $ Map.elems refExprMap
            -- Throw error if counterexample is found.
            case badPairs of
              [] -> return ()
              (x,y):_ -> ocError (AliasingInputs x y)
       -- Verify the initial logic assignments
       forM_ (bsLogicAssignments bs) $ \(pos, lhs, rhs) -> do
         ocEval (evalJavaExprAsLogic lhs) $ \lhsVal ->
           ocEval (evalMixedExprAsLogic rhs) $ \rhsVal ->
             ocAssert pos "Override value assertion"
                =<< liftIO (scEq sc lhsVal rhsVal)
       -- Verify assumptions
       forM_ (bsAssumptions bs) $ \le -> do
         ocEval (evalLogicExpr le) $ \assumptions ->
           ocAssert (PosInternal "assumption") "Override assumption check" assumptions
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

checkClassesInitialized :: MonadSim (SharedContext SAWCtx) m =>
                           Pos -> String -> [String]
                        -> SAWJavaSim m ()
checkClassesInitialized pos nm requiredClasses = do
  forM_ requiredClasses $ \c -> do
    mem <- getMem (PP.text "checkClassesInitialized")
    let status = Map.lookup c (mem ^. memInitialization)
    when (status /= Just Initialized) $
      let msg = "The method spec \'" ++ nm ++
                "\' requires that the class " ++ slashesToDots c ++
                " is initialized.  SAWScript does not " ++
                "currently support methods that initialize new classes."
       in throwIOExecException pos (ftext msg) ""

execOverride :: MonadSim (SharedContext SAWCtx) m
             => SharedContext SAWCtx
             -> Pos
             -> JavaMethodSpecIR
             -> Maybe Ref
             -> [Value (SharedTerm SAWCtx)]
             -> SAWJavaSim m ()
execOverride sc pos ir mbThis args = do
  -- Execute behaviors.
  let bsl = specBehaviors ir -- Map.lookup (BreakPC 0) (specBehaviors ir) -- TODO
  let method = specMethod ir
      argLocals = map (localIndexOfParameter method) [0..] `zip` args
  -- Check class initialization.
  checkClassesInitialized pos (specName ir) (specInitializedClasses ir)
  initPS <- getPath "execOverride"
  res <- execBehavior bsl sc mbThis argLocals initPS
  -- Create function for generation resume actions.
  case res of
    [(_, _, Left el)] -> do
      let msg = "Unsatisified assertions in " ++ specName ir ++ ":\n"
                ++ intercalate "\n" (map ppOverrideError el)
      fail msg
    [(ps, _, Right mval)] ->
      modifyPathM_ (PP.text "path result") $ \_ ->
        return $
        case (mval, ps ^. pathStack) of
          -- If the current path stack is empty, the result of the
          -- override is the return value of the current method.
          (_, [])     -> ps & set pathRetVal mval
          -- If the current path stack is non-empty and the override
          -- returned a value, put it on the operand stack of the
          -- current call frame.
          (Just val, (f:fr)) -> ps & set pathStack  (f' : fr)
            where f' = f & cfOpds %~ (val :)
          -- If the current path stack is non-empty and the override
          -- returned no value, leave the state alone.
          (Nothing,  _:_)    -> ps
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: MonadSim (SharedContext SAWCtx) m =>
                    SharedContext SAWCtx
                 -> Pos
                 -> JavaMethodSpecIR
                 -> SAWJavaSim m ()
overrideFromSpec de pos ir
  | methodIsStatic method =
      overrideStaticMethod cName key $ \args ->
        execOverride de pos ir Nothing args
  | otherwise =
      overrideInstanceMethod cName key $ \thisVal args ->
        execOverride de pos ir (Just thisVal) args
 where cName = className (specMethodClass ir)
       method = specMethod ir
       key = methodKey method

-- MethodSpec verification {{{1

pvcgDeepAssertEq :: (Monad m) =>
                    String
                 -> Path (SharedContext SAWCtx)
                 -> SpecJavaValue
                 -> ExpectedStateDef
                 -> SpecJavaValue
                 -> PathVCGenerator Breakpoint m ()
-- TODO: should we only do this equality check on references?
pvcgDeepAssertEq _ _ jv _ sv | jv == sv = return ()
pvcgDeepAssertEq name _ (IValue jv) _ (IValue sv) =
  pvcgAssertEq name jv sv
pvcgDeepAssertEq name _ (LValue jv) _ (LValue sv) =
  pvcgAssertEq name jv sv
pvcgDeepAssertEq name ps (RValue jref) esd (RValue sref)  = do
  let psScalarArrays = ps ^. pathMemory . memScalarArrays
  case (Map.lookup jref psScalarArrays, esdArrayValue sref esd) of
    (Just _, NoExpectedValue) ->
      pvcgFail $ ftext "Assigned value to array when none expected."
    (Just _, AnyExpectedValue) -> return ()
    (Just (jlen, jval), AssignedExpectedValue (slen, sval))
      | jlen == slen -> pvcgAssertEq name jval sval
      | otherwise ->
          pvcgFail $ ftext $
          "Array changed size. Expected " ++ show slen ++
          " but found " ++ show jlen ++ "."
    (Nothing, NoExpectedValue) -> return ()
    (Nothing, AnyExpectedValue) ->
      pvcgFail $ ftext "No value assigned when arbitrary change expected."
    (Nothing, AssignedExpectedValue _) ->
      pvcgFail $ ftext "No value assigned when specific change expected."
  let instanceFields = Map.mergeWithKey pairUp pairLeft pairRight
                       (pathRefInstanceFields ps jref)
                       (esdRefInstanceFields esd sref)
      pairUp _ a b = Just (Just a, Just b)
      pairLeft = fmap (\a -> (Just a, Nothing))
      pairRight = fmap (\b -> (Nothing, Just b))
  forM_ (Map.toList instanceFields) $ \(fid, (mjval, msval)) ->
    case (mjval, msval) of
      -- Specified modification
      (Just jval, Just (Just sval)) ->
        pvcgDeepAssertEq (name ++ "." ++ fieldIdName fid) ps jval esd sval
      -- Arbitrary modification
      (Just _, Just Nothing) -> return ()
      (Just _, Nothing) -> pvcgFail $ ftext "Disallowed modification"
      (Nothing, Just (Just _)) ->
        pvcgFail $ ftext "No value assigned when specific change expected."
      (Nothing, Just Nothing) ->
        pvcgFail $ ftext "No value assigned when arbitrary change expected."
      (Nothing, Nothing) -> return ()
pvcgDeepAssertEq name _ _ _ _ =
  fail $ "Expected and actual values for " ++ name ++ " are incomparable."

-- generateVC {{{2

esdRefInstanceFields :: ExpectedStateDef
                     -> Ref
                     -> Map.Map FieldId (Maybe SpecJavaValue)
esdRefInstanceFields esd = refInstanceFields (esdInstanceFields esd)

-- | Compare result with expected state.
generateVC :: JavaMethodSpecIR
           -> ExpectedStateDef -- ^ What is expected
           -> RunResult -- ^ Results of symbolic execution.
           -> PathVC Breakpoint -- ^ Proof oblications
generateVC ir esd (ps, endLoc, res) = do
  let initState  =
        PathVC { pvcStartLoc = esdStartLoc esd
               , pvcEndLoc = endLoc
               , pvcAssumptions = esdAssumptions esd
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  flip execState initState $ do
    case res of
      Left oe -> pvcgFail (vcat (map (ftext . ppOverrideError) oe))
      Right maybeRetVal -> do
        -- Check return value
        let Just cf = currentCallFrame (esdInitialPathState esd)
        let args = Map.elems (cf ^. cfLocals)
        let reachable = reachableRefs ps (maybeToList maybeRetVal ++ args)
        case (maybeRetVal, esdReturnValue esd) of
          (Nothing,Nothing) -> return ()
          (Just rv, Just srv) ->
            pvcgDeepAssertEq "return value" ps rv esd srv
          (Nothing, Just _) ->
            pvcgFail $ ftext $ "Return spec provided for void method."
          (Just _, Nothing) ->
            pvcgFail $ ftext $
            "Missing return spec for method returning a value."
        -- Check initialization
        do let sinits = Set.fromList (specInitializedClasses ir)
           forM_ (Map.keys (ps ^. pathMemory . memInitialization)) $ \cl -> do
             -- NB: when used as an override, we will not initialize this extra
             -- class. Ultimately, we should track which extra classes are
             -- initialized and make sure the override initializes them, too. Or
             -- is it ok to assume that it'll get initialized later if
             -- necessary?
             when (cl `Set.notMember` sinits && not (specAllowAlloc ir)) $ do
               pvcgFail $ ftext $
                 "Initializes extra class " ++ slashesToDots cl ++ "."
        -- Check static fields
        forM_ (Map.toList $ ps ^. pathMemory . memStaticFields) $
          \(f,jval) -> do
            let fieldName = show (fieldIdName f) ++
                            " of class " ++ (fieldIdClass f)
            case esdStaticFieldValue f esd of
              NoExpectedValue ->
                pvcgFail $ ftext $
                "Modifies the undefined static field " ++ fieldName ++ "."
              AnyExpectedValue -> return ()
              AssignedExpectedValue sv ->
                pvcgDeepAssertEq fieldName ps jval esd sv
        -- Check instance fields
        forM_ (Map.toList (ps ^. pathMemory . memInstanceFields)) $
          \((ref,f), jval) -> do
            let fieldName = show (fieldIdName f) ++
                            " of " ++ esdRefName ref esd
            case esdInstanceFieldValue ref f esd of
              _ | not (Set.member ref reachable) ->
                    trace ("Skipping " ++ show ref) $ return ()
              NoExpectedValue ->
                pvcgFail $ ftext $
                "Modifies the undefined field " ++ fieldName ++ "."
              AnyExpectedValue -> return ()
              AssignedExpectedValue sv ->
                pvcgDeepAssertEq fieldName ps jval esd sv
        -- Check value arrays
        forM_ (Map.toList (ps ^. pathMemory . memScalarArrays)) $
          \(ref,(jlen,jval)) -> do
            case esdArrayValue ref esd of
              _ | not (Set.member ref reachable) ->
                    trace ("Skipping " ++ show ref) $ return ()
              NoExpectedValue
                | specAllowAlloc ir -> return ()
                | otherwise -> pvcgFail $ ftext $ "Allocates an array."
              AnyExpectedValue -> return ()
              AssignedExpectedValue (slen, sval)
                | jlen /= slen -> pvcgFail $ ftext $ "Array changes size."
                | otherwise -> pvcgAssertEq (esdRefName ref esd) jval sval
        -- Check ref arrays
        when (not (Map.null (ps ^. pathMemory . memRefArrays))) $ do
          pvcgFail $ ftext "Modifies references arrays."
        -- Check assertions
        pvcgAssert "final assertions" (ps ^. pathAssertions)
        -- Check class objects
        forM_ (Map.keys (ps ^. pathMemory . memClassObjects)) $
          \clNm -> pvcgFail $ ftext $
                   "Allocated class object for " ++
                   slashesToDots clNm ++ "."

-- verifyMethodSpec and friends {{{2

mkSpecVC :: MonadSim (SharedContext SAWCtx) m =>
            SharedContext SAWCtx
         -> VerifyParams
         -> ExpectedStateDef
         -> SAWJavaSim m [PathVC Breakpoint]
mkSpecVC sc params esd = do
  let ir = vpSpec params
      vrb = simVerbose (vpOpts params)
      ovds = vpOver params
  -- Log execution.
  setVerbosity vrb
  -- Add method spec overrides.
  when (vrb >= 2) $ liftIO $
       putStrLn $ "Overriding: " ++ show (map specName ovds)
  mapM_ (overrideFromSpec sc (specPos ir)) ovds
  -- Execute code.
  run
  returnVal <- getProgramReturnValue
  ps <- getPath (PP.text "mkSpecVC")
  -- TODO: handle exceptional or breakpoint terminations
  return $ map (generateVC ir esd) [(ps, Nothing, Right returnVal)]

data VerifyParams = VerifyParams
  { vpCode    :: Codebase
  , vpContext :: SharedContext SAWCtx
  , vpOpts    :: Options
  , vpSpec    :: JavaMethodSpecIR
  , vpOver    :: [JavaMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext SAWCtx -> [PathVC Breakpoint] -> TopLevel ()
type Prover =
  VerifyState -> SharedTerm SAWCtx -> TopLevel ()

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc results = do
  let ir = vpSpec params
      verb = verbLevel (vpOpts params)
      -- ps = esdInitialPathState esd
      -- rv = esdReturnValue esd
  forM_ results $ \pvc -> do
    let mkVState nm cfn =
          VState { vsVCName = nm
                 , vsMethodSpec = ir
                 , vsVerbosity = verb
                 -- , vsFromBlock = esdStartLoc esd
                 -- , vsEvalContext = evalContextFromPathState sc rv ps
                 , vsCounterexampleFn = cfn
                 , vsStaticErrors = pvcStaticErrors pvc
                 }
    if null (pvcStaticErrors pvc) then
     forM_ (pvcChecks pvc) $ \vc -> do
       let vs = mkVState (vcName vc) (vcCounterexample sc vc)
       g <- io $ scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc
       when (verb >= 2) $ io $ do
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
      false <- io $ scBool sc False
      g <- io $ scImplies sc (pvcAssumptions pvc) false
      when (verb >= 2) $ io $ do
        putStrLn $ "Checking " ++ vsName
        print $ pvcStaticErrors pvc
      when (verb >= 5) $ io $ do
        putStrLn $ "Calling prover to disprove " ++
                 scPrettyTerm (pvcAssumptions pvc)
      prover vs g

data VerifyState = VState {
         vsVCName :: String
       , vsMethodSpec :: JavaMethodSpecIR
       , vsVerbosity :: Verbosity
         -- | Starting Block is used for checking VerifyAt commands.
       -- , vsFromBlock :: BlockId
         -- | Evaluation context used for parsing expressions during
         -- verification.
       -- , vsEvalContext :: EvalContext
       , vsCounterexampleFn :: CounterexampleFn SAWCtx
       , vsStaticErrors :: [Doc]
       }

{- Alternative implementation of JavaMethodSpec -}

initializeVerification' :: MonadSim (SharedContext SAWCtx) m
                        => SharedContext SAWCtx
                           -- ^ The SharedContext for creating new symbolic
                           -- expressions.
                        -> JavaMethodSpecIR
                           -- ^ The specification of the overall method.
                        -> BehaviorSpec
                           -- ^ The particular behavioral specification that
                           -- we are checking.
                        -> RefEquivConfiguration
                           -- ^ The particular relationship between which references
                           -- alias each other for verification purposes.
                        -> SAWJavaSim m SpecPathState
initializeVerification' sc ir bs refConfig = do
  -- Generate a reference for each reference equivalence class that
  -- isn't entirely involved in a return expression.
  let refConfig' = filter (not . all containsReturn . fst) refConfig
  exprRefs <- mapM (genRef . jssTypeOfActual . snd) refConfig'
  let refAssignments = (exprRefs `zip` map fst refConfig')
      pushFrame cs = case mcs' of
                       Nothing -> error "internal: failed to push call frame"
                       Just cs' -> cs'
        where
          mcs' = pushCallFrame
                 (className (specMethodClass ir))
                 (specMethod ir)
                 entryBlock -- FIXME: not the right block
                 Map.empty
                 cs
  modifyCSM_ (return . pushFrame)
  let updateInitializedClasses mem =
        foldr (flip setInitializationStatus Initialized)
              mem
              (specInitializedClasses ir)
  modifyPathM_ (PP.text "initializeVerification") $
    return . (pathMemory %~ updateInitializedClasses)
  forM_ refAssignments $ \(r, cl) ->
    forM_ cl $ \e -> writeJavaValue e (RValue r)
  lcs <- liftIO $ bsLogicClasses sc bs refConfig'
  case lcs of
    Nothing ->
      let msg = "Unresolvable cyclic dependencies between assumptions."
      in throwIOExecException (specPos ir) (ftext msg) ""
    Just assignments -> mapM_ (\(l, t, r) -> setClassValues sc l t r) assignments
  getPath (PP.text "initializeVerification")

evalLogicExpr' :: MonadSim (SharedContext SAWCtx) m =>
                  SharedContext SAWCtx -> LogicExpr
               -> SAWJavaSim m (SharedTerm SAWCtx)
evalLogicExpr' sc initExpr = do
  let exprs = logicExprJavaExprs initExpr
  args <- forM exprs $ \expr -> do
    t <- readJavaTermSim expr
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) $
                 logicExprJavaExprs initExpr
  liftIO $ useLogicExpr sc initExpr argTerms

resolveClassRHS :: MonadSim (SharedContext SAWCtx) m =>
                   SharedContext SAWCtx
                -> JavaExpr
                -> SharedTerm SAWCtx
                -> [LogicExpr]
                -> SAWJavaSim m (TypedTerm SAWCtx)
resolveClassRHS sc e tp [] =
  liftIO (scFreshGlobal sc (jeVarName e) tp >>= mkTypedTerm sc)
resolveClassRHS sc _ _ [r] = do
  t <- evalLogicExpr' sc r
  liftIO $ mkTypedTerm sc t
resolveClassRHS _ _ _ _ =
  fail "Not yet implemented."

setClassValues :: (MonadSim (SharedContext SAWCtx) m) =>
                  SharedContext SAWCtx
               -> [JavaExpr] -> SharedTerm SAWCtx
               -> [LogicExpr]
               -> SAWJavaSim m ()
setClassValues sc l tp rs =
  forM_ l $ \e ->
    unless (containsReturn e) $ do
      t <- resolveClassRHS sc e tp rs
      writeJavaTerm sc e t

valueEqTerm :: (Functor m, Monad m, MonadIO m) =>
               SharedContext SAWCtx
            -> String
            -> SpecPathState
            -> SpecJavaValue
            -> SharedTerm SAWCtx
            -> StateT (PathVC Breakpoint) m ()
valueEqTerm sc name _ (IValue t) t' = do
  t'' <- liftIO $ extendToIValue sc t'
  pvcgAssertEq name t t''
valueEqTerm _ name _ (LValue t) t' = pvcgAssertEq name t t'
valueEqTerm _ name ps (RValue r) t' = do
  case Map.lookup r (ps ^. pathMemory . memScalarArrays) of
    Just (_, t) -> pvcgAssertEq name t t'
    Nothing -> fail $ "valueEqTerm: " ++ name ++ ": ref does not point to array"
valueEqTerm _ name _ _ _ = fail $ "valueEqTerm: " ++ name ++ ": unspported value type"

valueEqValue :: (Functor m, Monad m, MonadIO m) =>
               SharedContext SAWCtx
            -> String
            -> SpecPathState
            -> SpecJavaValue
            -> SpecPathState
            -> SpecJavaValue
            -> StateT (PathVC Breakpoint) m ()
valueEqValue sc name _ (IValue t) _ (IValue t') = do
  it <- liftIO $ extendToIValue sc t
  it' <- liftIO $ extendToIValue sc t'
  pvcgAssertEq name it it'
valueEqValue _ name _ (LValue t) _ (LValue t') = pvcgAssertEq name t t'
valueEqValue _ _ _ (RValue r) _ (RValue r') | r == r' = return ()
valueEqValue _ name ps (RValue r) ps' (RValue r') = do
  let ma = Map.lookup r (ps ^. pathMemory . memScalarArrays)
      ma' = Map.lookup r' (ps' ^. pathMemory . memScalarArrays)
  case (ma, ma') of
    (Just (len, t), Just (len', t'))
      | len == len' -> pvcgAssertEq name t t'
      | otherwise -> fail $ "valueEqTerm: array sizes don't match: " ++ show (len, len')
    _ -> fail $ "valueEqTerm: " ++ name ++ ": ref does not point to array"
valueEqValue _ name _ _ _ _ = fail $ "valueEqValue: " ++ name ++ ": unspported value type"

readJavaValueVerif :: (Functor m, Monad m) =>
                      VerificationState
                   -> Path' (SharedTerm SAWCtx)
                   -> JavaExpr
                   -> m SpecJavaValue
readJavaValueVerif vs ps refExpr = do
  let initPS = vsInitialState vs
  readJavaValue (currentCallFrame initPS) ps refExpr

checkStep :: (Functor m, Monad m, MonadIO m) =>
             VerificationState
          -> SpecPathState
          -> BehaviorCommand
          -> StateT (PathVC Breakpoint) m ()
checkStep vs ps (ReturnValue expr) = do
  t <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) expr
  case ps ^. pathRetVal of
    Just rv -> valueEqTerm (vsContext vs) "return" ps rv t
    Nothing -> fail "Return specification, but method did not return a value."
checkStep vs ps (EnsureInstanceField _pos refExpr f rhsExpr) = do
  rv <- readJavaValueVerif vs ps refExpr
  case rv of
    RValue ref -> do
      let mfv = getInstanceFieldValuePS ps ref f
      case mfv of
        Just fv -> do
          ft <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
          valueEqTerm (vsContext vs) (ppJavaExpr refExpr ++ "." ++ fieldIdName f) ps fv ft
        Nothing  -> fail "Invalid instance field in java_ensure_eq."
    _ -> fail "Left-hand side of . did not evaluate to a reference."
checkStep vs ps (EnsureStaticField _pos f rhsExpr) = do
  let mfv = getStaticFieldValuePS ps f
  ft <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
  case mfv of
    Just fv -> valueEqTerm (vsContext vs) (ppFldId f) ps fv ft
    Nothing -> fail "Invalid static field in java_ensure_eq."
checkStep _vs _ps (ModifyInstanceField _refExpr _f) = return ()
checkStep _vs _ps (ModifyStaticField _f) = return ()
checkStep vs ps (EnsureArray _pos refExpr rhsExpr) = do
  rv <- readJavaValueVerif vs ps refExpr
  t <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
  valueEqTerm (vsContext vs) (ppJavaExpr refExpr) ps rv t
checkStep _vs _ps (ModifyArray _refExpr _aty) = return ()

data VerificationState = VerificationState
                         { vsContext :: SharedContext SAWCtx
                         , vsSpec :: JavaMethodSpecIR
                         , vsInitialState :: SpecPathState
                         }

checkFinalState :: MonadSim (SharedContext SAWCtx) m =>
                   SharedContext SAWCtx
                -> JavaMethodSpecIR
                -> BehaviorSpec
                -> RefEquivConfiguration
                -> SpecPathState
                -> SAWJavaSim m (PathVC Breakpoint)
checkFinalState sc ms bs cl initPS = do
  let st = VerificationState { vsContext = sc
                             , vsSpec = ms
                             , vsInitialState = initPS
                             }
      cmds = bsCommands bs
  finalPS <- getPath "checkFinalState"
  let maybeRetVal = finalPS ^. pathRetVal
  refList <- forM (concatMap fst cl) $ \e -> do
      rv <- readJavaValue (currentCallFrame initPS) finalPS e
      case rv of
        RValue r -> return (r, e)
        _ -> fail "internal: refMap"
  let refMap = Map.fromList refList
  assumptions <- liftIO $ evalAssumptions sc initPS (specAssumptions ms)
  let initState  =
        PathVC { pvcStartLoc = bsLoc bs
               , pvcEndLoc = Nothing
               , pvcAssumptions = assumptions
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  let mentionedSFields =
        Set.fromList $
        [ fid | EnsureStaticField _ fid _ <- cmds] ++
        [ fid | ModifyStaticField fid <- cmds ]
      mentionedIFieldExprs =
        [ (e, fid) | EnsureInstanceField _ e fid _ <- cmds] ++
        [ (e, fid) | ModifyInstanceField e fid <- cmds ]
      mentionedArrayExprs =
        [ e | EnsureArray _ e _ <- cmds] ++
        [ e | ModifyArray e _ <- cmds ]
  mentionedIFields <- forM mentionedIFieldExprs $ \(e, fid) -> do
      -- TODO: best combination of initPS and finalPS unclear here.
      rv <- readJavaValue (currentCallFrame initPS) finalPS e
      case rv of
        RValue r -> return (r, fid)
        _ -> fail "internal: mentionedIFields"
  mentionedArrays <- forM mentionedArrayExprs $ \e -> do
      -- TODO: best combination of initPS and finalPS unclear here.
      rv <- readJavaValue (currentCallFrame initPS) finalPS e
      case rv of
        RValue r -> return r
        _ -> fail "internal: mentionedArrays"
  let mentionedIFieldSet = Set.fromList mentionedIFields
  let mentionedArraySet = Set.fromList mentionedArrays
  let mcf = currentCallFrame initPS
  args <- case mcf of
            Just cf -> return (Map.elems (cf ^. cfLocals))
            Nothing -> fail "internal: no call frame in initial path state"
  let reachable = reachableRefs finalPS (maybeToList maybeRetVal ++ args)
  flip execStateT initState $ do
    mapM_ (checkStep st finalPS) cmds
    let initMem = initPS ^. pathMemory
        finalMem = finalPS ^. pathMemory
    when (initMem ^. memInitialization /= finalMem ^. memInitialization) $
      unless (specAllowAlloc ms) $
        pvcgFail "Initializes extra class."
    when (initMem ^. memClassObjects /= finalMem ^. memClassObjects) $
      pvcgFail "Allocates class object."
    when (initMem ^. memRefArrays /= finalMem ^. memRefArrays) $
      pvcgFail "Allocates or modifies reference array."
    forM_ (Map.toList (finalMem ^. memStaticFields)) $ \(f, fval) ->
      unless (Set.member f mentionedSFields) $
        unless(isArrayType (fieldIdType f)) $
          let fieldDesc = fieldIdClass f ++ "." ++ fieldIdName f in
          case Map.lookup f (initMem ^. memStaticFields) of
            Nothing -> pvcgFail $ ftext $
                       "Modifies unspecified static field " ++ fieldDesc
            Just ival -> valueEqValue sc fieldDesc initPS ival finalPS fval
    forM_ (Map.toList (finalMem ^. memInstanceFields)) $ \((ref, f), fval) -> do
      unless (Set.member (ref, f) mentionedIFieldSet) $
        when (ref `Set.member` reachable && not (isArrayType (fieldIdType f))) $
        let fname =
              case Map.lookup ref refMap of
                Just e -> ppJavaExpr e ++ "." ++ fieldIdName f
                Nothing -> "field " ++ fieldIdName f ++  " of a new object"
        in
        case Map.lookup (ref, f) (initMem ^. memInstanceFields) of
          Nothing -> pvcgFail $ ftext $
                     "Modifies unspecified instance field: " ++ fname
          Just ival -> do
            valueEqValue sc fname initPS ival finalPS fval
    forM_ (Map.toList (finalMem ^. memScalarArrays)) $ \(ref, (flen, fval)) ->
      unless (Set.member ref mentionedArraySet) $
      when (ref `Set.member` reachable) $
      case Map.lookup ref (initMem ^. memScalarArrays) of
        Nothing -> unless (specAllowAlloc ms) $
                   pvcgFail "Allocates scalar array."
        Just (ilen, ival)
          | ilen == flen ->
              let aname =
                    case Map.lookup ref refMap of
                      Just e -> ppJavaExpr e
                      Nothing -> "a new array"
              in
              pvcgAssertEq aname ival fval -- TODO: name
          | otherwise -> pvcgFail "Array changed size."
    -- TODO: check that return value has been specified if method returns a value
    pvcgAssert "final assertions" (finalPS ^. pathAssertions)

