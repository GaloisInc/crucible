{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMMethodSpec
  ( LLVMMethodSpecIR
  , specFunction
  , specName
  , SymbolicRunHandler
  , initializeVerification'
  , runValidation
  , checkFinalState
  , overrideFromSpec
  , ppPathVC
  , scLLVMValue
  , VerifyParams(..)
  , VerifyState(..)
  , EvalContext(..)
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.LLVMExpr as TC
import SAWScript.Options
import SAWScript.Utils
import Verifier.SAW.Prelude
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMUtils
import SAWScript.PathVC
import SAWScript.Value (TopLevel, io)
import SAWScript.VerificationCheck

import Verifier.LLVM.Simulator hiding (State)
import Verifier.LLVM.Simulator.Internals hiding (State)
import Verifier.LLVM.Codebase
import Verifier.LLVM.Backend hiding (asBool)
import Verifier.LLVM.Backend.SAW

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm hiding (Ident)

-- | Contextual information needed to evaluate expressions.
data EvalContext
  = EvalContext {
      ecContext :: SharedContext SAWCtx
    , ecDataLayout :: DataLayout
    , ecBackend :: SBE SpecBackend
    , ecGlobalMap :: GlobalMap SpecBackend
    , ecArgs :: [(Ident, SharedTerm SAWCtx)]
    , ecPathState :: SpecPathState
    , ecLLVMExprs :: Map String (TC.LLVMActualType, TC.LLVMExpr)
    }

type ExprEvaluator a = ExceptT TC.LLVMExpr IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either TC.LLVMExpr b)
runEval v = liftIO (runExceptT v)

-- | Evaluate an LLVM expression, and return its value (r-value) as an
-- internal term.
evalLLVMExpr :: (Functor m, MonadIO m) =>
                TC.LLVMExpr -> EvalContext
             -> m SpecLLVMValue
evalLLVMExpr expr ec = eval expr
  where eval e@(CC.Term app) =
          case app of
            TC.Arg _ n _ ->
              case lookup n (ecArgs ec) of
                Just v -> return v
                Nothing -> fail $ "evalLLVMExpr: argument not found: " ++ show e
            TC.Global n tp -> do
              -- TODO: don't discard fst
              snd <$> (liftIO $ loadGlobal sbe (ecGlobalMap ec) n tp ps)
            TC.Deref ae tp -> do
              addr <- evalLLVMExpr ae ec
              -- TODO: don't discard fst
              snd <$> (liftIO $ loadPathState sbe addr tp ps)
            TC.StructField ae si idx tp ->
              case siFieldOffset si idx of
                Just off -> do
                  saddr <- evalLLVMExpr ae ec
                  addr <- liftIO $ addrPlusOffset (ecDataLayout ec) sc saddr off
                  -- TODO: don't discard fst
                  snd <$> (liftIO $ loadPathState sbe addr tp ps)
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.StructDirectField ve si idx tp -> do
              case siFieldOffset si idx of
                Just off -> do
                  saddr <- evalLLVMRefExpr ve ec
                  addr <- liftIO $ addrPlusOffset (ecDataLayout ec) sc saddr off
                  -- TODO: don't discard fst
                  snd <$> (liftIO $ loadPathState sbe addr tp ps)
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.ReturnValue _ -> fail "return values not yet supported" -- TODO
        sbe = ecBackend ec
        ps = ecPathState ec
        sc = ecContext ec

-- | Evaluate an LLVM expression, and return the location it describes
-- (l-value) as an internal term.
evalLLVMRefExpr :: (Functor m, MonadIO m) =>
                   TC.LLVMExpr -> EvalContext
                -> m SpecLLVMValue
evalLLVMRefExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.Arg _ _ _ -> fail "evalLLVMRefExpr: applied to argument"
            TC.Global n _ -> do
              case Map.lookup n gm of
                Just addr -> return addr
                Nothing ->
                  fail $ "evalLLVMRefExpr: global " ++ show n ++ " not found"
            TC.Deref ae _ -> evalLLVMExpr ae ec
            TC.StructField ae si idx _ ->
              case siFieldOffset si idx of
                Just off -> do
                  addr <- evalLLVMExpr ae ec
                  liftIO $ addrPlusOffset (ecDataLayout ec) sc addr off
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.StructDirectField ve si idx _ -> do
              case siFieldOffset si idx of
                Just off -> do
                  addr <- evalLLVMRefExpr ve ec
                  liftIO $ addrPlusOffset (ecDataLayout ec) sc addr off
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.ReturnValue _ -> fail "evalLLVMRefExpr: applied to return value"
        gm = ecGlobalMap ec
        sc = ecContext ec

evalDerefLLVMExpr :: (Functor m, MonadIO m) =>
                     TC.LLVMExpr -> EvalContext
                  -> m (SharedTerm SAWCtx)
evalDerefLLVMExpr expr ec = do
  val <- evalLLVMExpr expr ec
  case TC.lssTypeOfLLVMExpr expr of
    PtrType (MemType tp) -> liftIO $
      -- TODO: don't discard fst
      (snd <$> loadPathState (ecBackend ec) val tp (ecPathState ec))
    PtrType _ -> fail "Pointer to weird type."
    _ -> return val

-- | Evaluate a typed expression in the context of a particular state.
evalLogicExpr :: (Functor m, MonadIO m) =>
                 TC.LogicExpr -> EvalContext
              -> m SpecLLVMValue
evalLogicExpr initExpr ec = do
  let sc = ecContext ec
  t <- liftIO $ TC.useLogicExpr sc initExpr
  extMap <- forM (getAllExts t) $ \ext -> do
              let n = ecName ext
              case Map.lookup n (ecLLVMExprs ec) of
                Just (_, expr) -> do
                  lt <- evalLLVMExpr expr ec
                  return (ecVarIndex ext, lt)
                Nothing -> fail $ "Name " ++ n ++ " not found."
  liftIO $ scInstantiateExt sc (Map.fromList extMap) t

-- | Return Java value associated with mixed expression.
evalMixedExpr :: (Functor m, MonadIO m) =>
                 TC.MixedExpr -> EvalContext
              -> m SpecLLVMValue
evalMixedExpr (TC.LogicE expr) ec = evalLogicExpr expr ec
evalMixedExpr (TC.LLVME expr) ec = evalLLVMExpr expr ec

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         ocsLoc :: SymBlockID
       , ocsEvalContext :: !EvalContext
       , ocsResultState :: !SpecPathState
       , ocsReturnValue :: !(Maybe (SharedTerm SAWCtx))
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

ocModifyResultStateIO :: (SpecPathState -> IO SpecPathState)
                      -> OverrideComputation ()
ocModifyResultStateIO fn = do
  bcs <- get
  new <- liftIO $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

-- | Add assumption for predicate.
ocAssert :: Pos -> String -> SharedTerm SAWCtx -> OverrideComputation ()
ocAssert p _nm x = do
  sbe <- (ecBackend . ocsEvalContext) <$> get
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultStateIO (addAssertion sbe x)

ocStep :: BehaviorCommand -> OverrideComputation ()
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
    value <- liftIO $ scFreshGlobal sc (show (TC.ppLLVMExpr lhsExpr)) lty
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
       -- Verify assumptions
       forM_ (bsAssumptions bs) $ \le -> do
         ocEval (evalLogicExpr le) $ \assumptions ->
           ocAssert (PosInternal "assumption") "Override assumption check" assumptions
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

execOverride :: (MonadIO m, Functor m) =>
                SharedContext SAWCtx
             -> Pos
             -> LLVMMethodSpecIR
             -> [(MemType, SpecLLVMValue)]
             -> Simulator SpecBackend m (Maybe (SharedTerm SAWCtx))
execOverride sc _pos ir args = do
  initPS <- fromMaybe (error "no path during override") <$> getPath
  let bsl = specBehavior ir
  let func = specFunction ir
      cb = specCodebase ir
      Just funcDef = lookupDefine func cb
  sbe <- gets symBE
  gm <- use globalTerms
  let ec = EvalContext { ecContext = sc
                       , ecDataLayout = cbDataLayout cb
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
    [(ps, _, Right mval)] -> do
      currentPathOfState .= ps
      return mval
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: (MonadIO m, Functor m) =>
                    SharedContext SAWCtx
                 -> Pos
                 -> LLVMMethodSpecIR
                 -> Simulator SpecBackend m ()
overrideFromSpec sc pos ir = do
  let ovd = Override (\_ _ -> execOverride sc pos ir)
  -- TODO: check argument types?
  tryRegisterOverride (specFunction ir) (const (Just ovd))

createLogicValue :: Codebase SpecBackend
                 -> SBE SpecBackend
                 -> SharedContext SAWCtx
                 -> TC.LLVMExpr
                 -> SpecPathState
                 -> MemType
                 -> Maybe TC.LogicExpr
                 -> IO (SpecLLVMValue, SpecPathState)
createLogicValue _ _ _ _ _ (PtrType _) (Just _) =
  fail "Pointer variables cannot be given initial values."
createLogicValue _ _ _ _ _ (StructType _) (Just _) =
  fail "Struct variables cannot be given initial values as a whole."
createLogicValue cb sbe sc _expr ps (PtrType (MemType mtp)) Nothing = do
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
      return (addr, ps')
createLogicValue _ _ _ _ _ (PtrType ty) Nothing =
  fail $ "Pointer to weird type: " ++ show (ppSymType ty)
createLogicValue _ _ _ _ _ (StructType _) Nothing =
  fail "Non-pointer struct variables not supported."
createLogicValue _ _ sc expr ps mtp mrhs = do
  mbltp <- TC.logicTypeOfActual sc mtp
  -- Get value of rhs.
  tm <- case (mrhs, mbltp) of
          (Just v, _) -> TC.useLogicExpr sc v
          (Nothing, Just tp) -> scFreshGlobal sc (show (TC.ppLLVMExpr expr)) tp
          (Nothing, Nothing) -> fail "Can't calculate type for fresh input."
  return (tm, ps)

initializeVerification' :: (MonadIO m, Monad m, Functor m) =>
                           SharedContext SAWCtx
                        -> LLVMMethodSpecIR
                        -> Simulator SpecBackend m (SpecPathState, [SpecLLVMValue])
initializeVerification' sc ir = do
  let bs = specBehavior ir
      fn = specFunction ir
      cb = specCodebase ir
      Just fnDef = lookupDefine fn (specCodebase ir)
      isArgAssgn (CC.Term (TC.Arg _ _ _), _) = True
      isArgAssgn _ = False
      isPtrAssgn (e, _) = TC.isPtrLLVMExpr e
      assignments = map getAssign $ Map.toList (bsExprDecls bs)
      getAssign (e, (_, v)) = (e, v)
      argAssignments = filter isArgAssgn assignments
      ptrAssignments = filter (\a -> isPtrAssgn a && not (isArgAssgn a)) assignments
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
      (CC.Term (TC.Arg _ _ _), Just _) ->
        fail "argument assignments not allowed"
      (CC.Term (TC.Arg _ _ ty), Nothing) -> do
        ps <- fromMaybe (error "initializeVerification") <$> getPath
        (tm, ps') <- liftIO $ createLogicValue cb sbe sc expr ps ty mle
        setPS ps'
        return (Just (expr, tm))
      _ -> return Nothing

  let argAssignments'' = catMaybes argAssignments'

  let args = flip map argAssignments'' $ \(expr, mle) ->
               case (expr, mle) of
                 (CC.Term (TC.Arg i _ ty), tm) ->
                   Just (i, (ty, tm))
                 _ -> Nothing

  --gm <- use globalTerms
  let rreg =  (,Ident "__sawscript_result") <$> sdRetType fnDef
      cmpFst (i, _) (i', _) =
        case i `compare` i' of
          EQ -> error $ "Argument " ++ show i ++ " declared multiple times."
          r -> r
  let argVals = (map snd (sortBy cmpFst (catMaybes args)))
  callDefine' False fn rreg argVals

  let doAssign (expr, mle) = do
        let Just (ty, _) = Map.lookup expr (bsExprDecls bs)
        ps <- fromMaybe (error "initializeVerification") <$> getPath
        (v, ps') <- liftIO $ createLogicValue cb sbe sc expr ps ty mle
        setPS ps'
        writeLLVMTerm (map snd argVals) (expr, v, 1)

  -- Allocate space for all pointers that aren't directly parameters.
  forM_ ptrAssignments doAssign

  -- Set initial logic values for everything except arguments and
  -- pointers, including values pointed to by pointers from directly
  -- above, and fields of structures from anywhere.
  forM_ otherAssignments doAssign

  ps <- fromMaybe (error "initializeVerification") <$> getPath

  return (ps, map snd argVals)

checkFinalState :: (MonadIO m, Functor m, MonadException m) =>
                   SharedContext SAWCtx
                -> LLVMMethodSpecIR
                -> SpecPathState
                -> [SpecLLVMValue]
                -> Simulator SpecBackend m (PathVC SymBlockID)
checkFinalState sc ms initPS args = do
  let cmds = bsCommands (specBehavior ms)
      cb = specCodebase ms
      dl = cbDataLayout cb
  mrv <- getProgramReturnValue
  assumptions <- evalAssumptions ms sc initPS args (specAssumptions ms)
  msrv <- case [ e | Return e <- cmds ] of
            [e] -> Just <$> readLLVMMixedExprPS ms sc initPS args e
            [] -> return Nothing
            _  -> fail "More than one return value specified."
  expectedValues <- forM [ (le, me) | Ensure _ le me <- cmds ] $ \(le, me) -> do
    lhs <- readLLVMTermAddrPS initPS args le
    rhs <- readLLVMMixedExprPS ms sc initPS args me
    let Just (tp, _) = Map.lookup le (bsExprDecls (specBehavior ms))
    return (le, lhs, tp, rhs)
  let initState  =
        PathVC { pvcStartLoc = bsLoc (specBehavior ms)
               , pvcEndLoc = Nothing
               , pvcAssumptions = assumptions
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  flip execStateT initState $ do
    case (mrv, msrv) of
      (Nothing,Nothing) -> return ()
      (Just rv, Just srv) -> pvcgAssertEq "return value" rv srv
      (Just _, Nothing) -> fail "simulator returned value when not expected"
      (Nothing, Just _) -> fail "simulator did not return value when expected"

    -- Check that expected state modifications have occurred.
    -- TODO: extend this to check that nothing else has changed.
    forM_ expectedValues $ \(e, lhs, tp, rhs) -> do
      finalValue <- lift $ load tp lhs (memTypeAlign dl tp)
      pvcgAssertEq (show e) finalValue rhs
    -- Check assertions
    ps <- fromMaybe (error "no path in checkFinalState") <$> (lift $ getPath)
    pvcgAssert "final assertions" (ps ^. pathAssertions)


data VerifyParams = VerifyParams
  { vpCode    :: Codebase (SAWBackend SAWCtx)
  , vpContext :: SharedContext SAWCtx
  , vpOpts    :: Options
  , vpSpec    :: LLVMMethodSpecIR
  , vpOver    :: [LLVMMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext SAWCtx -> [PathVC SymBlockID] -> TopLevel ()
type Prover = VerifyState -> SharedTerm SAWCtx -> TopLevel ()

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc results = do
  let ir = vpSpec params
      verb = verbLevel (vpOpts params)
  forM_ results $ \pvc -> do
    let mkVState nm cfn =
          VState { vsVCName = nm
                 , vsMethodSpec = ir
                 , vsVerbosity = verb
                 , vsCounterexampleFn = cfn
                 , vsStaticErrors = pvcStaticErrors pvc
                 }
    if null (pvcStaticErrors pvc) then
      forM_ (pvcChecks pvc) $ \vc -> do
        let vs = mkVState (vcName vc) (vcCounterexample sc vc)
        g <- io (scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc)
        when (verb >= 3) $ io $ do
          putStr $ "Checking " ++ vcName vc
          when (verb >= 4) $ putStr $ " (" ++ show g ++ ")"
          putStrLn ""
        prover vs g
    else do
      let vsName = "an invalid path"
      let vs = mkVState vsName (\_ -> return $ vcat (pvcStaticErrors pvc))
      false <- io $ scBool sc False
      g <- io $ scImplies sc (pvcAssumptions pvc) false
      when (verb >= 4) $ io $ do
        putStrLn $ "Checking " ++ vsName
        print $ pvcStaticErrors pvc
        putStrLn $ "Calling prover to disprove " ++
                 scPrettyTerm defaultPPOpts (pvcAssumptions pvc)
      prover vs g

data VerifyState = VState {
         vsVCName :: String
       , vsMethodSpec :: LLVMMethodSpecIR
       , vsVerbosity :: Verbosity
       , vsCounterexampleFn :: CounterexampleFn SAWCtx
       , vsStaticErrors :: [Doc]
       }

type Verbosity = Int

readLLVMMixedExprPS :: (Functor m, Monad m, MonadIO m) =>
                       LLVMMethodSpecIR
                    -> SharedContext SAWCtx
                    -> SpecPathState -> [SpecLLVMValue] -> TC.MixedExpr
                    -> Simulator SpecBackend m SpecLLVMValue
readLLVMMixedExprPS ir sc ps args (TC.LogicE le) = do
  useLogicExprPS ir sc ps args le
readLLVMMixedExprPS _ir _sc ps args (TC.LLVME le) =
  readLLVMTermPS ps args le 1

useLogicExprPS :: (Monad m, MonadIO m) =>
                  LLVMMethodSpecIR
               -> SharedContext SAWCtx
               -> SpecPathState
               -> [SpecLLVMValue]
               -> TC.LogicExpr
               -> Simulator SpecBackend m SpecLLVMValue
useLogicExprPS ir sc ps args initExpr = do
  t <- liftIO $ TC.useLogicExpr sc initExpr
  extMap <- forM (getAllExts t) $ \ext -> do
              let n = ecName ext
              case Map.lookup n (specLLVMExprNames ir) of
                Just (_, expr) -> do
                  lt <- readLLVMTermPS ps args expr 1
                  return (ecVarIndex ext, lt)
                Nothing -> fail $ "Name " ++ n ++ " not found."
  liftIO $ scInstantiateExt sc (Map.fromList extMap) t

evalAssumptions :: (Monad m, MonadIO m) =>
                   LLVMMethodSpecIR
                -> SharedContext SAWCtx
                -> SpecPathState
                -> [SpecLLVMValue]
                -> [TC.LogicExpr]
                -> Simulator SpecBackend m (SharedTerm SAWCtx)
evalAssumptions ir sc ps args as = do
  assumptionList <- mapM (useLogicExprPS ir sc ps args) as
  liftIO $ do
    true <- scBool sc True
    foldM (scAnd sc) true assumptionList
