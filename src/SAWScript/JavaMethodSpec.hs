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
  , mkSpecVC
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

import Language.JVM.Common (ppFldId)
import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.JavaExpr as TC
import SAWScript.Options
import SAWScript.Utils
import SAWScript.JavaMethodSpecIR
import SAWScript.JavaMethodSpec.Evaluator
import SAWScript.JavaMethodSpec.ExpectedStateDef
import SAWScript.VerificationCheck

import qualified Verifier.Java.Simulator as JSS
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm

-- JSS Utilities {{{1

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

-- | Returns value constructor from node.
mkJSSValue :: JSS.Type -> n -> JSS.Value n
mkJSSValue JSS.BooleanType n = JSS.IValue n
mkJSSValue JSS.ByteType    n = JSS.IValue n
mkJSSValue JSS.CharType    n = JSS.IValue n
mkJSSValue JSS.IntType     n = JSS.IValue n
mkJSSValue JSS.LongType    n = JSS.LValue n
mkJSSValue JSS.ShortType   n = JSS.IValue n
mkJSSValue _ _ = error "internal: illegal type"

-- EvalContext {{{1

evalErrExpr :: ExprEvalError -> TC.JavaExpr
evalErrExpr (EvalExprUndefined e) = e
evalErrExpr (EvalExprUnknownArray e) = e
evalErrExpr (EvalExprUnknownLocal _ e) = e
evalErrExpr (EvalExprUnknownField _ e) = e
evalErrExpr (EvalExprBadJavaType _ _) = error "evalErrExpr: EvalExprBadJavaType"
evalErrExpr (EvalExprBadLogicType _ _) = error "evalErrExpr: EvalExprBadLogicType"
evalErrExpr (EvalExprOther _) = error "evalErrExpr: EvalExprOther"

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
   = SuccessfulRun (JSS.Path (SharedContext SAWCtx)) (Maybe JSS.Breakpoint) (Maybe SpecJavaValue)
   | FalseAssumption
   | FailedRun (JSS.Path (SharedContext SAWCtx)) (Maybe JSS.Breakpoint) [OverrideError]
   -- deriving (Show)

type RunResult = ( JSS.Path (SharedContext SAWCtx)
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
ocAssert :: Pos -> String -> SharedTerm SAWCtx -> OverrideComputation ()
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
ocStep (ReturnValue expr) = do
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

checkClassesInitialized :: JSS.MonadSim (SharedContext SAWCtx) m =>
                           Pos -> String -> [String] -> JSS.Simulator (SharedContext SAWCtx) m ()
checkClassesInitialized pos nm requiredClasses = do
  forM_ requiredClasses $ \c -> do
    mem <- JSS.getMem (PP.text "checkClassesInitialized")
    let status = Map.lookup c (mem ^. JSS.memInitialization)
    when (status /= Just JSS.Initialized) $
      let msg = "The method spec \'" ++ nm ++ "\' requires that the class "
                  ++ JSS.slashesToDots c ++ " is initialized.  SAWScript does not "
                  ++ "currently support methods that initialize new classes."
       in throwIOExecException pos (ftext msg) ""

execOverride :: JSS.MonadSim (SharedContext SAWCtx) m
             => SharedContext SAWCtx
             -> Pos
             -> JavaMethodSpecIR
             -> Maybe JSS.Ref
             -> [JSS.Value (SharedTerm SAWCtx)]
             -> JSS.Simulator (SharedContext SAWCtx) m ()
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
overrideFromSpec :: JSS.MonadSim (SharedContext SAWCtx) m =>
                    SharedContext SAWCtx
                 -> Pos
                 -> JavaMethodSpecIR
                 -> JSS.Simulator (SharedContext SAWCtx) m ()
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

-- MethodSpec verification {{{1

-- PathVC {{{2

-- | Describes the verification result arising from one symbolic execution path.
data PathVC = PathVC {
          pvcStartLoc :: JSS.Breakpoint
        , pvcEndLoc :: Maybe JSS.Breakpoint
        , pvcInitialAssignments :: [(TC.JavaExpr, SharedTerm SAWCtx)]
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
pvcgAssertEq :: String -> SharedTerm SAWCtx -> SharedTerm SAWCtx -> PathVCGenerator ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: String -> SharedTerm SAWCtx -> PathVCGenerator ()
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
          case esdStaticFieldValue f esd of
            NoExpectedValue ->
              pvcgFail $ ftext $ "Modifies the undefined static field " ++ fieldName ++ "."
            AnyExpectedValue -> return ()
            AssignedExpectedValue sv -> do
              case (jval,sv) of
                (jv, _) | jv == sv -> return ()
                (JSS.RValue jref, JSS.RValue _) ->
                  pvcgFail $ ftext $
                    "Assigns an unexpected value " ++ esdRefName jref esd
                       ++ " to " ++ fieldName ++ "."
                (JSS.IValue jvmNode, JSS.IValue specNode) ->
                  pvcgAssertEq fieldName jvmNode specNode
                (JSS.LValue jvmNode, JSS.LValue specNode) ->
                  pvcgAssertEq fieldName jvmNode specNode
                _ ->
                  pvcgFail $
                  ftext "internal: comparePathStates encountered illegal field type."
        -- Check instance fields
        forM_ (Map.toList (ps ^. JSS.pathMemory . JSS.memInstanceFields)) $ \((ref,f), jval) -> do
          let fieldName = show (JSS.fieldIdName f)
                            ++ " of " ++ esdRefName ref esd
          case esdInstanceFieldValue ref f esd of
            NoExpectedValue ->
              pvcgFail $ ftext $ "Modifies the undefined field " ++ fieldName ++ "."
            AnyExpectedValue -> return ()
            AssignedExpectedValue sv -> do
              case (jval,sv) of
                (jv, _) | jv == sv -> return ()
                (JSS.RValue jref, JSS.RValue _) ->
                  pvcgFail $ ftext $
                    "Assigns an unexpected value " ++ esdRefName jref esd
                       ++ " to " ++ fieldName ++ "."
                (JSS.IValue jvmNode, JSS.IValue specNode) ->
                  pvcgAssertEq fieldName jvmNode specNode
                (JSS.LValue jvmNode, JSS.LValue specNode) ->
                  pvcgAssertEq fieldName jvmNode specNode
                _ -> pvcgFail $
                  ftext "internal: comparePathStates encountered illegal field type."
        -- Check value arrays
        forM_ (Map.toList (ps ^. JSS.pathMemory . JSS.memScalarArrays)) $ \(ref,(jlen,jval)) -> do
          case esdArrayValue ref esd of
            NoExpectedValue -> pvcgFail $ ftext $ "Allocates an array."
            AnyExpectedValue -> return ()
            AssignedExpectedValue (slen, sval)
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

mkSpecVC :: JSS.MonadSim (SharedContext SAWCtx) m =>
            SharedContext SAWCtx
         -> VerifyParams
         -> ExpectedStateDef
         -> JSS.Simulator (SharedContext SAWCtx) m [PathVC]
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
  , vpContext :: SharedContext SAWCtx
  , vpOpts    :: Options
  , vpSpec    :: JavaMethodSpecIR
  , vpOver    :: [JavaMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext SAWCtx -> ExpectedStateDef -> [PathVC] -> IO ()
type Prover =
  VerifyState -> SharedTerm SAWCtx -> IO ()

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
                 , vsEvalContext = evalContextFromPathState sc (esdJavaExprs esd) ps
                 , vsInitialAssignments = pvcInitialAssignments pvc
                 , vsCounterexampleFn = cfn
                 , vsStaticErrors = pvcStaticErrors pvc
                 }
--        m = esdJavaExprs esd
    if null (pvcStaticErrors pvc) then
     forM_ (pvcChecks pvc) $ \vc -> do
       let vs = mkVState (vcName vc) (vcCounterexample sc vc)
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
       , vsInitialAssignments :: [(TC.JavaExpr, SharedTerm SAWCtx)]
       , vsCounterexampleFn :: CounterexampleFn SAWCtx
       , vsStaticErrors :: [Doc]
       }
