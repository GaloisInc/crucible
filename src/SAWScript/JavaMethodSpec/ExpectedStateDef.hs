{- |
Module           : $Header$
Description      : Creates initial configuration for simulator and information needed for verification.
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.JavaMethodSpec.ExpectedStateDef
  ( ExpectedStateDef
  , esdStartLoc
  , esdInitialAssignments
  , esdInitialPathState
  , esdReturnValue
  , ExpectedValue(..)
  , esdStaticFieldValue
  , esdInstanceFieldValue
  , esdArrayValue
  , esdRefName
  , initializeVerification
  ) where

import Control.Lens
import Control.Monad
import Control.Monad.State.Strict
import Data.Int
import Data.JVM.Symbolic.AST as JSS
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Text.PrettyPrint.HughesPJ as PP

import Language.JVM.Common (ppFldId)

import Verifier.Java.Codebase as JSS
import Verifier.Java.Common as JSS
import Verifier.Java.Simulator as JSS

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.JavaExpr as TC
import SAWScript.JavaMethodSpec.Evaluator

import SAWScript.JavaMethodSpecIR
import SAWScript.Utils
  ( SAWCtx
  , basic_ss
  , ftext
  , throwIOExecException
  )

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm

import Verifier.SAW.Cryptol (scCryptolEq)

-- ExpectedStateDef {{{1

-- | Describes expected result computation.
data ExpectedStateDef = ESD {
         -- | Location that we started from.
         esdStartLoc :: !Breakpoint
         -- | Map from references back to Java expressions denoting them. Purely
         -- for diagnostics.
       , esdRefExprMap :: !(Map Ref [TC.JavaExpr])
         -- | Initial path state (used for evaluating expressions in
         -- verification).
       , esdInitialPathState :: !SpecPathState
         -- | Stores initial assignments.
       , esdInitialAssignments :: !([(TC.JavaExpr, SharedTerm SAWCtx)])
         -- | Expected return value or Nothing if method returns void.
       , esdReturnValue :: !(Maybe SpecJavaValue)
         -- | Maps instance fields to expected value, or Nothing if value may
         -- be arbitrary.
       , esdInstanceFields :: !(Map (Ref, FieldId) (Maybe SpecJavaValue))
         -- | Maps static fields to expected value, or Nothing if value may
         -- be arbitrary.
         -- Verification will check that all fields assigned a value at the
         -- are defined in this map.
       , esdStaticFields :: !(Map FieldId (Maybe SpecJavaValue))
         -- | Maps reference to expected node, or Nothing if value may be arbitrary.
       , esdArrays :: !(Map Ref (Maybe (Int32, SharedTerm SAWCtx)))
       }


-- | Return the name of a reference from the expected state def.
esdRefName :: Ref -> ExpectedStateDef -> String
esdRefName NullRef _ = "null"
esdRefName ref esd =
  case Map.lookup ref (esdRefExprMap esd) of
    Just cl -> ppJavaExprEquivClass cl
    Nothing -> "fresh allocation"

-- | Describes the expected value of a state variable.
data ExpectedValue a
  = NoExpectedValue
  -- ^ The state variable did not have any expected value.
  | AnyExpectedValue
  -- ^ The state variable may have any value.
  | AssignedExpectedValue a
  -- ^ The state variable has a specific assigned value.

esdStaticFieldValue :: FieldId
                    -> ExpectedStateDef
                    -> ExpectedValue SpecJavaValue
esdStaticFieldValue f esd =
  case Map.lookup f (esdStaticFields esd) of
    Nothing ->
      -- Check if field was in initial state.
      case Map.lookup f init_map of
        Nothing -> NoExpectedValue
        Just r -> AssignedExpectedValue r
      where init_map = esdInitialPathState esd^.pathMemory^.memStaticFields

    Just Nothing -> AnyExpectedValue
    Just (Just r) -> AssignedExpectedValue r

esdInstanceFieldValue :: Ref
                      -> FieldId
                      -> ExpectedStateDef
                      -> ExpectedValue SpecJavaValue
esdInstanceFieldValue ref f esd =
  case Map.lookup (ref,f) (esdInstanceFields esd) of
   Nothing ->
     -- Check if field was in initial state.
     case Map.lookup (ref,f) init_map of
      Nothing -> NoExpectedValue
      Just r -> AssignedExpectedValue r
     where init_map = esdInitialPathState esd^.pathMemory^.memInstanceFields
   Just Nothing -> AnyExpectedValue
   Just (Just r) -> AssignedExpectedValue r

-- | Get the value we expect a reference to have at the beginning.
esdArrayValue :: Ref
              -> ExpectedStateDef
              -> ExpectedValue (Int32, SharedTerm SAWCtx)
esdArrayValue ref esd =
  -- Check if ref was explicitly assigned a value.
  case Map.lookup ref (esdArrays esd) of
   Nothing ->
     -- Check if array was in initial state.
     case Map.lookup ref init_map of
       Nothing -> NoExpectedValue
       Just r -> AssignedExpectedValue r
    where init_map = esdInitialPathState esd^.pathMemory^.memScalarArrays
   Just Nothing -> AnyExpectedValue
   Just (Just r) -> AssignedExpectedValue r


-- Initial state generation {{{1

-- | State for running the behavior specifications in a method override.
data ESGState = ESGState {
         esContext :: !(SharedContext SAWCtx)
       , esMethod :: !Method
       , esExprRefMap :: !(Map TC.JavaExpr Ref)
       , esErrors :: ![String]

       , _esInitialPathState :: !SpecPathState
       , _esInitialAssignments :: ![(TC.JavaExpr, SharedTerm SAWCtx)]
       , _esReturnValue :: !(Maybe SpecJavaValue)
       , _esInstanceFields :: !(Map (Ref, FieldId) (Maybe SpecJavaValue))
       , _esStaticFields :: !(Map FieldId (Maybe SpecJavaValue))
       , _esArrays :: !(Map Ref (Maybe (Int32, SharedTerm SAWCtx)))
       }

esInitialPathState :: Simple Lens ESGState SpecPathState
esInitialPathState = lens _esInitialPathState (\s v -> s { _esInitialPathState = v })

esInitialAssignments :: Simple Lens ESGState [(TC.JavaExpr, SharedTerm SAWCtx)]
esInitialAssignments = lens _esInitialAssignments (\s v -> s { _esInitialAssignments = v })

esReturnValue :: Simple Lens ESGState (Maybe SpecJavaValue)
esReturnValue = lens _esReturnValue (\s v -> s { _esReturnValue = v })

esInstanceFields :: Simple Lens ESGState (Map (Ref, FieldId) (Maybe SpecJavaValue))
esInstanceFields = lens _esInstanceFields (\s v -> s { _esInstanceFields = v })

esStaticFields :: Simple Lens ESGState (Map FieldId (Maybe SpecJavaValue))
esStaticFields = lens _esStaticFields (\s v -> s { _esStaticFields = v })

esArrays :: Simple Lens ESGState (Map Ref (Maybe (Int32, SharedTerm SAWCtx)))
esArrays = lens _esArrays (\s v -> s { _esArrays = v })

-- | Monad used to execute statements in a behavior specification for a method
-- override.
type ExpectedStateGenerator = StateT ESGState IO

esEval :: (EvalContext -> ExprEvaluator b) -> ExpectedStateGenerator b
esEval fn = do
  sc <- gets esContext
  initPS <- use esInitialPathState
  let ec = evalContextFromPathState sc initPS
  res <- runEval (fn ec)
  case res of
    Left expr -> error $ "internal: esEval failed to evaluate expression: " ++ show expr
    Right v   -> return v

esError :: String -> ExpectedStateGenerator ()
esError e = modify $ \es -> es { esErrors = e : esErrors es }

esAddAssertion :: SharedContext SAWCtx
               -> SharedTerm SAWCtx
               -> ExpectedStateGenerator ()
esAddAssertion sc prop = do
  ps <- use esInitialPathState
  ps' <- liftIO $ addAssertionPS sc prop ps
  esInitialPathState .= ps'

esAddAssumption :: SharedContext SAWCtx
               -> SharedTerm SAWCtx
               -> ExpectedStateGenerator ()
esAddAssumption sc prop = do
  ps <- use esInitialPathState
  ps' <- liftIO $ addAssumptionPS sc prop ps
  esInitialPathState .= ps'

esAddEqAssertion :: SharedContext SAWCtx -> String -> SharedTerm SAWCtx -> SharedTerm SAWCtx
                 -> ExpectedStateGenerator ()
esAddEqAssertion sc _nm x y = do
  prop <- liftIO $ scEq sc x y
  esAddAssertion sc prop

-- | Assert that two terms are equal.
esAssertEq :: String -> SpecJavaValue -> SpecJavaValue
           -> ExpectedStateGenerator ()
esAssertEq nm (RValue x) (RValue y) = do
  when (x /= y) $
    esError $ "internal: Asserted different references for " ++ nm ++ " are equal."
esAssertEq nm (IValue x) (IValue y) = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq nm (LValue x) (LValue y) = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq _ _ _ = esError "internal: esAssertEq given illegal arguments."

-- | Set value in initial state.
esSetJavaValue :: TC.JavaExpr -> SpecJavaValue -> ExpectedStateGenerator ()
esSetJavaValue e@(CC.Term exprF) v = do
  -- liftIO $ putStrLn $ "Setting Java value for " ++ show e
  case exprF of
    -- TODO: the following is ugly, and doesn't make good use of lenses
    -- TODO: is this the right way to handle return values?
    TC.ReturnVal _ -> error "internal: can't set return value in initial state"
    TC.Local _ idx _ -> do
      ps <- use esInitialPathState
      let ls = case currentCallFrame ps of
                 Just cf -> cf ^. cfLocals
                 Nothing -> Map.empty
          ps' = (pathStack %~ updateLocals) ps
          updateLocals (f:r) = (cfLocals %~ Map.insert idx v) f : r
          updateLocals [] =
            error "internal: esSetJavaValue of local with empty call stack"
      -- liftIO $ putStrLn $ "Local " ++ show idx ++ " with stack " ++ show ls
      case Map.lookup idx ls of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing -> esInitialPathState .= ps'
    -- TODO: the following is ugly, and doesn't make good use of lenses
    TC.InstanceField refExpr f -> do
      -- Lookup refrence associated to refExpr
      Just ref <- Map.lookup refExpr `fmap` gets esExprRefMap
      ps <- use esInitialPathState
      case Map.lookup (ref,f) (ps ^. pathMemory . memInstanceFields) of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing ->
          esInitialPathState . pathMemory . memInstanceFields %= Map.insert (ref,f) v
    TC.StaticField f -> do
      ps <- use esInitialPathState
      case Map.lookup f (ps ^. pathMemory . memStaticFields) of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing ->
          esInitialPathState . pathMemory . memStaticFields %= Map.insert f v

esResolveLogicExprs :: TC.JavaExpr -> SharedTerm SAWCtx -> [TC.LogicExpr]
                    -> ExpectedStateGenerator (SharedTerm SAWCtx)
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
    prop <- liftIO $ scCryptolEq sc t rhs
    esAddAssumption sc prop
  -- Return value.
  return t

esSetLogicValues :: SharedContext SAWCtx -> [TC.JavaExpr] -> SharedTerm SAWCtx
                 -> [TC.LogicExpr]
                 -> ExpectedStateGenerator ()
esSetLogicValues _ [] _ _ = esError "empty class passed to esSetLogicValues"
esSetLogicValues sc cl@(rep:_) tp lrhs = do
  -- liftIO $ putStrLn $ "Setting logic values for: " ++ show cl
  -- Get value of rhs.
  value <- esResolveLogicExprs rep tp lrhs
  -- Update Initial assignments.
  esInitialAssignments %= (map (\e -> (e,value)) cl ++)
  ty <- liftIO $ scTypeOf sc value
  -- Update value.
  case ty of
    (isVecType (const (return ())) -> Just (n :*: _)) -> do
       refs <- forM cl $ \expr -> do
                 RValue ref <- esEval $ evalJavaExpr expr
                 return ref
       forM_ refs $ \r ->
         esInitialPathState %= setArrayValuePS r (fromIntegral n) value
    (asBitvectorType -> Just 32) ->
       mapM_ (flip esSetJavaValue (IValue value)) cl
    (asBitvectorType -> Just 64) ->
       mapM_ (flip esSetJavaValue (LValue value)) cl
    _ -> esError "internal: initializing Java values given bad rhs."

esStep :: BehaviorCommand -> ExpectedStateGenerator ()
-- TODO: Figure out difference between assertPred and assumePred
esStep (AssertPred _ expr) = do
  sc <- gets esContext
  v <- esEval $ evalLogicExpr expr
  esAddAssumption sc v
esStep (AssumePred expr) = do
  sc <- gets esContext
  v <- esEval $ evalLogicExpr expr
  esAddAssumption sc v
esStep (ReturnValue expr) = do
  v <- esEval $ evalMixedExpr expr
  esReturnValue .= Just v
esStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  value <- esEval $ evalMixedExpr rhsExpr
  -- Get dag engine
  sc <- gets esContext
  -- Check that instance field is already defined, if so add an equality check for that.
  ifMap <- use esInstanceFields
  case (Map.lookup (ref, f) ifMap, value) of
    (Nothing, _) -> return ()
    (Just Nothing, _) -> return ()
    (Just (Just (RValue prev)), RValue new)
      | prev == new -> return ()
    (Just (Just (IValue prev)), IValue new) ->
       esAddEqAssertion sc (show refExpr) prev new
    (Just (Just (LValue prev)), LValue new) ->
       esAddEqAssertion sc (show refExpr) prev new
    -- TODO: See if we can give better error message here.
    -- Perhaps this just ends up meaning that we need to verify the assumptions in this
    -- behavior are inconsistent.
    _ -> esError "internal: Incompatible values assigned to instance field."
  -- Define instance field post condition.
  esInstanceFields %= Map.insert (ref,f) (Just value)
esStep (EnsureStaticField _pos f rhsExpr) = do
  value <- esEval $ evalMixedExpr rhsExpr
  -- Get dag engine
  sc <- gets esContext
  -- Check that instance field is already defined, if so add an equality check for that.
  sfMap <- use esStaticFields
  case (Map.lookup f sfMap, value) of
    (Nothing, _) -> return ()
    (Just Nothing, _) -> return ()
    (Just (Just (RValue prev)), RValue new)
      | prev == new -> return ()
    (Just (Just (IValue prev)), IValue new) ->
       esAddEqAssertion sc (ppFldId f) prev new
    (Just (Just (LValue prev)), LValue new) ->
       esAddEqAssertion sc (ppFldId f) prev new
    -- TODO: See if we can give better error message here.
    -- Perhaps this just ends up meaning that we need to verify the assumptions in this
    -- behavior are inconsistent.
    _ -> esError "internal: Incompatible values assigned to static field."
  esStaticFields %= Map.insert f (Just value)
esStep (ModifyInstanceField refExpr f) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  fMap <- use esInstanceFields
  -- Add postcondition if value has not been assigned.
  when (Map.notMember (ref, f) fMap) $ do
    esInstanceFields %= Map.insert (ref,f) Nothing
esStep (ModifyStaticField f) = do
  fMap <- use esStaticFields
  -- Add postcondition if value has not been assigned.
  when (Map.notMember f fMap) $ do
    esStaticFields %= Map.insert f Nothing
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
      arrayMap <- use esArrays
      case Map.lookup ref arrayMap of
        Just (Just (oldLen, prev))
          | l /= fromIntegral oldLen -> esError "internal: array changed size."
          | otherwise -> esAddEqAssertion sc (show lhsExpr) prev value
        _ -> return ()
      -- Define instance field post condition.
      esArrays %= Map.insert ref (Just (l, value))
    _ -> esError "internal: right hand side of array ensure clause has non-array type."
esStep (ModifyArray refExpr _) = do
  ref <- esEval $ evalJavaRefExpr refExpr
  arrayMap <- use esArrays
  -- Add postcondition if value has not been assigned.
  when (Map.notMember ref arrayMap) $ do
    esArrays %= Map.insert ref Nothing

-----------------------------------------------------------------------------
-- initializeVerification

-- | @initializeVerification@ is responsible for configuring the simulator
-- initial state so that it captures the information in a particular behavioral
-- specification relative to a particular aliasing relationship between
-- references.
--
-- This method returns an @ExpectedStateDef@ which will be used to verify the
-- state(s) after simulation are compatible with the specification.
initializeVerification :: MonadSim (SharedContext SAWCtx) m
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
                       -> Simulator (SharedContext SAWCtx) m ExpectedStateDef
initializeVerification sc ir bs refConfig = do
  exprRefs <- mapM (genRef . TC.jssTypeOfActual . snd) refConfig
  let refAssignments = (exprRefs `zip` map fst refConfig)
      --key = methodKey (specMethod ir)
      pushFrame cs = fromMaybe (error "internal: failed to push call frame") mcs'
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
  -- TODO: add breakpoints once local specs exist
  --forM_ (Map.keys (specBehaviors ir)) $ addBreakpoint clName key
  -- TODO: set starting PC
  initPS <- getPath (PP.text "initializeVerification")
  let initESG = ESGState { esContext = sc
                         , esMethod = specMethod ir
                         , esExprRefMap = Map.fromList
                             [ (e, r) | (r,cl) <- refAssignments, e <- cl ]
                         , esErrors = []

                         , _esInitialPathState = initPS
                         , _esInitialAssignments = []
                         , _esReturnValue = Nothing
                         , _esInstanceFields = Map.empty
                         , _esStaticFields = Map.empty
                         , _esArrays = Map.empty
                         }
  -- liftIO $ putStrLn "Starting to initialize state."
  es <- liftIO $ flip execStateT initESG $ do
          -- Set references
          -- liftIO $ putStrLn "Setting references."
          forM_ refAssignments $ \(r,cl) ->
            forM_ cl $ \e -> esSetJavaValue e (RValue r)
          -- Set initial logic values.
          -- liftIO $ putStrLn "Setting logic values."
          lcs <- liftIO $ bsLogicClasses sc bs refConfig
          case lcs of
            Nothing ->
              let msg = "Unresolvable cyclic dependencies between assumptions."
               in throwIOExecException (specPos ir) (ftext msg) ""
            Just assignments -> mapM_ (\(l,t,r) -> esSetLogicValues sc l t r) assignments
          -- Process commands
          -- liftIO $ putStrLn "Running commands."
          mapM esStep (bsCommands bs)
  let errs = esErrors es
      indent2 = (' ' :) . (' ' :)
  unless (null errs) $ fail . unlines $
    "Errors while initializing verification:" : map indent2 errs
  modifyPathM_ (PP.text "initializeVerification") (\_ -> return (es^.esInitialPathState))
  return ESD { esdStartLoc = bsLoc bs
             , esdRefExprMap = Map.fromList refAssignments
             , esdInitialPathState = es^.esInitialPathState
             , esdInitialAssignments = reverse (es^.esInitialAssignments)
             , esdReturnValue    = es^.esReturnValue
             , esdInstanceFields = es^.esInstanceFields
             , esdStaticFields   = es^.esStaticFields
             , esdArrays         = es^.esArrays
             }
