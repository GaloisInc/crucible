{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
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
  , runValidation
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
import Control.Monad.State.Strict
import Data.List (intercalate) -- foldl', intersperse)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP

import Debug.Trace

import Language.JVM.Common (ppFldId)
import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.JavaExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.JavaMethodSpecIR
import SAWScript.JavaMethodSpec.Evaluator
import SAWScript.JavaMethodSpec.ExpectedStateDef
import SAWScript.JavaUtils
import SAWScript.Value (TopLevel, io)
import SAWScript.VerificationCheck

import Verifier.Java.Simulator hiding (asBool, State)
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
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
       , ocsReturnValue :: !(Maybe SpecJavaValue)
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
   | FalseAssumption
   | FailedRun (Path (SharedContext SAWCtx)) (Maybe Breakpoint) [OverrideError]
   -- deriving (Show)

type RunResult = ( Path (SharedContext SAWCtx)
                 , Maybe Breakpoint
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
    Left e  -> ocError $ UndefinedExpr (evalErrExpr e)
    Right v -> m v

-- Modify result state
ocModifyResultState :: (SpecPathState -> SpecPathState)
                    -> OverrideComputation ()
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
ocAssert :: Pos -> String -> SharedTerm SAWCtx -> OverrideComputation ()
ocAssert p _nm x = do
  sc <- (ecContext . ocsEvalContext) <$> get
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultStateIO (addAssertionPS sc x)

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
      _ -> ocModifyResultStateIO $ addAssumptionPS sc v
ocStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef ->
    ocEval (evalMixedExpr rhsExpr) $ \value ->
      ocModifyResultState $ setInstanceFieldValuePS lhsRef f value
ocStep (EnsureStaticField _pos f rhsExpr) = do
  ocEval (evalMixedExpr rhsExpr) $ \value ->
    ocModifyResultState $ setStaticFieldValuePS f value
ocStep (EnsureArray _pos lhsExpr rhsExpr) = do
  ocEval (evalJavaRefExpr lhsExpr) $ \lhsRef ->
    ocEval (evalMixedExprAsLogic rhsExpr) $ \rhsVal -> do
      sc <- gets (ecContext . ocsEvalContext)
      ss <- liftIO $ basic_ss sc
      ty <- liftIO $ scTypeOf sc rhsVal >>= rewriteSharedTerm sc ss
      case ty of
        (isVecType (const (return ())) -> Just (n :*: _)) ->
          ocModifyResultState $ setArrayValuePS lhsRef (fromIntegral n) rhsVal
        _ -> ocError (InvalidType (show ty))
ocStep (ModifyInstanceField refExpr f) =
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef -> do
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
            ocModifyResultState $ setArrayValuePS ref (fromIntegral n) rhsVal
          _ -> ocError (InvalidType (show ty))
ocStep (ReturnValue expr) = do
  ocEval (evalMixedExpr expr) $ \val ->
    modify $ \ocs -> ocs { ocsReturnValue = Just val }

-- Executing overrides {{{2

execBehavior :: [BehaviorSpec]
             -> SharedContext SAWCtx
             -> Maybe Ref
             -> [(LocalVariableIndex, Value (SharedTerm SAWCtx))]
             -> SpecPathState
             -> IO [RunResult]
execBehavior bsl sc mbThis argLocals ps = do
  -- Get state of current execution path in simulator.
  fmap orParseResults $ forM bsl $ \bs -> do
    let ec = EvalContext { ecContext = sc
                         , ecLocals =  Map.fromList $
                                       case mbThis of
                                       Just th -> (0, RValue th) : argLocals
                                       Nothing -> argLocals
                         -- TODO: does this need to be initialized for reference returns?
                         , ecReturnValue = Nothing
                         , ecPathState = ps
                         }
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
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

checkClassesInitialized :: MonadSim (SharedContext SAWCtx) m =>
                           Pos -> String -> [String]
                        -> Simulator (SharedContext SAWCtx) m ()
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
             -> Simulator (SharedContext SAWCtx) m ()
execOverride sc pos ir mbThis args = do
  -- Execute behaviors.
  initPS <- getPath (PP.text "MethodSpec override")
  let bsl = specBehaviors ir -- Map.lookup (BreakPC 0) (specBehaviors ir) -- TODO
  let method = specMethod ir
      argLocals = map (localIndexOfParameter method) [0..] `zip` args
  -- Check class initialization.
  checkClassesInitialized pos (specName ir) (specInitializedClasses ir)

  -- TODO: allocate any declared variables that don't currently evaluate to
  -- references. Treat return variable specially.

  -- Execute behavior.
  res <- liftIO $ execBehavior [bsl] sc mbThis argLocals initPS
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
          (Just val, [])     -> ps & set pathRetVal (Just val)
          (Just val, (f:fr)) -> ps & set pathStack  (f' : fr)
            where f' = f & cfOpds %~ (val :)
          (Nothing,  [])     -> ps & set pathRetVal Nothing
          (Nothing,  _:_)    -> ps
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: MonadSim (SharedContext SAWCtx) m =>
                    SharedContext SAWCtx
                 -> Pos
                 -> JavaMethodSpecIR
                 -> Simulator (SharedContext SAWCtx) m ()
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

-- PathVC {{{2

-- | Describes the verification result arising from one symbolic execution path.
data PathVC = PathVC {
          pvcStartLoc :: Breakpoint
        , pvcEndLoc :: Maybe Breakpoint
          -- | Assumptions on inputs.
        , pvcAssumptions :: SharedTerm SAWCtx
          -- | Static errors found in path.
        , pvcStaticErrors :: [Doc]
          -- | What to verify for this result.
        , pvcChecks :: [VerificationCheck SAWCtx]
        }

ppPathVC :: PathVC -> Doc
ppPathVC pvc =
  nest 2 $
  vcat [ text "Path VC:"
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
  {-
  where ppAssignment (expr, tm) = hsep [ text (TC.ppJavaExpr expr)
                                       , text ":="
                                       , scPrettyTermDoc tm
                                       ] -}

type PathVCGenerator = StateT PathVC

-- | Add verification condition to list.
pvcgAssertEq :: (Monad m) =>
                String -> SharedTerm SAWCtx -> SharedTerm SAWCtx
             -> PathVCGenerator m ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: (Monad m) => String -> SharedTerm SAWCtx -> PathVCGenerator m ()
pvcgAssert nm v =
  modify $ \pvc -> pvc { pvcChecks = AssertionCheck nm v : pvcChecks pvc }

pvcgFail :: (Monad m) => Doc -> PathVCGenerator m ()
pvcgFail msg =
  modify $ \pvc -> pvc { pvcStaticErrors = msg : pvcStaticErrors pvc }

pvcgDeepAssertEq :: (Monad m) =>
                    String
                 -> Path (SharedContext SAWCtx)
                 -> SpecJavaValue
                 -> ExpectedStateDef
                 -> SpecJavaValue
                 -> PathVCGenerator m ()
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
           -> PathVC -- ^ Proof oblications
generateVC ir esd (ps, endLoc, res) = do
  let initState  =
        PathVC { pvcStartLoc = esdStartLoc esd
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
         -> Simulator (SharedContext SAWCtx) m [PathVC]
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
  SharedContext SAWCtx -> [PathVC] -> TopLevel ()
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
