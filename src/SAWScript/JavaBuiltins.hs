{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.JavaBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif
import Control.Lens
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.List (partition)
import Data.IORef
import qualified Data.Map as Map
import Data.Time.Clock
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.JVM.Common

import Verifier.Java.Codebase hiding (lookupClass)
import Verifier.Java.Simulator as JSS hiding (lookupClass)
import Verifier.Java.SAWBackend

import Verifier.SAW.Recognizer
import Verifier.SAW.FiniteValue
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC

import SAWScript.JavaExpr
import SAWScript.JavaMethodSpec
import SAWScript.JavaMethodSpecIR
import SAWScript.JavaUtils

import SAWScript.Builtins
import SAWScript.CryptolEnv (schemaNoUser)
import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SS

import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.PP as Cryptol (pretty)

loadJavaClass :: BuiltinContext -> String -> IO Class
loadJavaClass bic =
  lookupClass (biJavaCodebase bic) fixPos . dotsToSlashes

getActualArgTypes :: JavaSetupState -> Either String [JavaActualType]
getActualArgTypes s = mapM getActualType declaredTypes
  where
    declaredTypes = zip [0..] (methodParameterTypes meth)
    ir = jsSpec s
    meth = specMethod ir
    getActualType (n, ty) = do
      let i = localIndexOfParameter meth n
          atys = [ aty | (CC.Term (Local _ i' _), aty) <-
                         Map.toList (specActualTypeMap ir), i == i' ]
      case atys of
        [] | isPrimitiveType ty -> Right (PrimitiveType ty)
           | otherwise ->
             Left $ "No declared type for non-scalar parameter " ++ show n
        [aty] -> Right aty
        _ -> Left $ "More than one actual type given for parameter " ++ show n

type Assign = (JavaExpr, TypedTerm SAWCtx)

symexecJava :: BuiltinContext
            -> Options
            -> Class
            -> String
            -> [(String, TypedTerm SAWCtx)]
            -> [String]
            -> Bool
            -> TopLevel (TypedTerm SAWCtx)
symexecJava bic opts cls mname inputs outputs satBranches = do
  let cb = biJavaCodebase bic
      pos = fixPos
      jsc = biSharedContext bic
      fl = defaultSimFlags { alwaysBitBlastBranchTerms = True
                           , satAtBranches = satBranches
                           }
  (_mcls, meth) <- io $ findMethod cb pos mname cls
  -- TODO: should we use mcls anywhere below?
  let mkAssign (s, tm) = do
        e <- parseJavaExpr' cb cls meth s
        return (e, tm)
      multDefErr i = error $ "Multiple terms given for " ++ ordinal (i + 1) ++
                             " argument in method " ++ methodName meth
      noDefErr i = fail $ "No binding for " ++ ordinal (i + 1) ++
                          " argument in method " ++ methodName meth
      pidx = fromIntegral . localIndexOfParameter meth
  withSAWBackend jsc Nothing $ \sbe -> io $ do
    runSimulator cb sbe defaultSEH (Just fl) $ do
      setVerbosity (simVerbose opts)
      assigns <- mapM mkAssign inputs
      let (argAssigns, otherAssigns) = partition (isArg meth . fst) assigns
          argMap = Map.fromListWithKey (\i _ _ -> multDefErr i)
                   [ (idx, tm) | (CC.Term (Local _ idx _), tm) <- argAssigns ]
      argTms <- forM [0..maxArg meth] $ \i ->
                  maybe (noDefErr i) return $ Map.lookup (pidx i) argMap
      args <- mapM (valueOfTerm jsc) argTms
      -- TODO: map scTypeOf over argTms and lift to JavaActualType
      actualArgTys <- liftIO $ mapM (typeOfValue jsc) args
      let expectedArgTys = methodParameterTypes meth
      forM_ (zip actualArgTys expectedArgTys) $ \ (aty, ety) ->
        unless (aty == ety) $ fail $
        "Passing value of type " ++ show aty ++
        " to argument expected to be of type " ++ show ety ++ "."
      mapM_ (uncurry (writeJavaTerm jsc)) otherAssigns
      initPS <- getPath "java_symexec initial"
      _ <- case methodIsStatic meth of
             True -> execStaticMethod (className cls) (methodKey meth) args
             False -> do
               RValue this <- freshJavaVal Nothing jsc (ClassInstance cls)
               execInstanceMethod (className cls) (methodKey meth) this args
      ps <- getPath "java_symexec final"
      outtms <- forM outputs $ \ostr -> do
        case ostr of
          "$safety" -> return (ps ^. pathAssertions)
          _-> do
            e <- parseJavaExpr' cb cls meth ostr
            readJavaTerm (currentCallFrame initPS) ps e
      let bundle tms = case tms of
                         [t] -> return t
                         _ -> scTuple jsc tms
      liftIO (mkTypedTerm jsc =<< bundle outtms)

extractJava :: BuiltinContext -> Options -> Class -> String
            -> JavaSetup ()
            -> TopLevel (TypedTerm SAWCtx)
extractJava bic opts cls mname setup = do
  let cb = biJavaCodebase bic
      pos = fixPos
      jsc = biSharedContext bic
  argsRef <- io $ newIORef []
  withSAWBackend jsc (Just argsRef) $ \sbe -> do
    setupRes <- runJavaSetup pos cb cls mname jsc setup
    let fl = defaultSimFlags { alwaysBitBlastBranchTerms =
                                 jsSatBranches setupRes }
        meth = specMethod (jsSpec setupRes)
    io $ runSimulator cb sbe defaultSEH (Just fl) $ do
      setVerbosity (simVerbose opts)
      argTypes <- either fail return (getActualArgTypes setupRes)
      args <- mapM (freshJavaVal (Just argsRef) jsc) argTypes
      -- TODO: support initializing other state elements
      rslt <- case methodIsStatic meth of
                True -> execStaticMethod (className cls) (methodKey meth) args
                False -> do
                  RValue this <- freshJavaVal (Just argsRef) jsc (ClassInstance cls)
                  execInstanceMethod (className cls) (methodKey meth) this args
      dt <- case (rslt, methodReturnType meth) of
              (Nothing, _) -> fail $ "No return value from " ++ methodName meth
              (_, Nothing) -> fail $ "Return value from void method " ++ methodName meth
              (Just v, Just tp) -> termOfValueSim tp v
      liftIO $ do
        let sc = biSharedContext bic
        argBinds <- reverse <$> readIORef argsRef
        exts <- mapM asExtCns argBinds
        -- TODO: group argBinds according to the declared types
        bindExts jsc exts dt >>= mkTypedTerm sc

withSAWBackend :: SharedContext s
               -> Maybe (IORef [SharedTerm s])
               -> (Backend (SharedContext s) -> TopLevel a)
               -> TopLevel a
withSAWBackend jsc argsRef a = io (sawBackend jsc argsRef sawProxy) >>= a

runJavaSetup :: Pos -> Codebase -> Class -> String -> SharedContext SAWCtx
             -> StateT JavaSetupState TopLevel a
             -> TopLevel JavaSetupState
runJavaSetup pos cb cls mname jsc setup = do
  ms <- io $ initMethodSpec pos cb cls mname
  --putStrLn "Created MethodSpec"
  let setupState = JavaSetupState {
                     jsSpec = ms
                   , jsContext = jsc
                   , jsTactic = Skip
                   , jsSimulate = True
                   , jsSatBranches = False
                   }
  snd <$> runStateT setup setupState

verifyJava :: BuiltinContext -> Options -> Class -> String
           -> [JavaMethodSpecIR]
           -> JavaSetup ()
           -> TopLevel JavaMethodSpecIR
verifyJava bic opts cls mname overrides setup = do
  startTime <- io $ getCurrentTime
  let pos = fixPos -- TODO
      cb = biJavaCodebase bic
      bsc = biSharedContext bic
      jsc = bsc
  setupRes <- runJavaSetup pos cb cls mname jsc setup
  --putStrLn "Done running setup"
  let ms = jsSpec setupRes
      vp = VerifyParams {
             vpCode = cb
           , vpContext = jsc
           , vpOpts = opts
           , vpSpec = ms
           , vpOver = overrides
           }
  when (jsSimulate setupRes) $ do
    let verb = simVerbose opts
        overrideText =
          case overrides of
            [] -> ""
            irs -> " (overriding " ++ show (map renderName irs) ++ ")"
        renderName ir = className (specMethodClass ir) ++ "." ++
                        methodName (specMethod ir)
        configs = [ (bs, cl)
                  | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                  , cl <- bsRefEquivClasses bs
                  ]
        fl = defaultSimFlags { alwaysBitBlastBranchTerms = True
                             , satAtBranches = jsSatBranches setupRes
                             }
    when (verb >= 2) $ io $ putStrLn $ "Starting verification of " ++ specName ms
    ro <- getTopLevelRO
    rw <- getTopLevelRW
    -- io $ print (length configs)
    forM_ configs $ \(bs,cl) -> withSAWBackend jsc Nothing $ \sbe -> io $ do
      liftIO $ bsCheckAliasTypes pos bs
      when (verb >= 2) $ do
        putStrLn $ "Executing " ++ specName ms ++
                   " at PC " ++ show (bsLoc bs) ++ "."
      -- runDefSimulator cb sbe $ do
      runSimulator cb sbe defaultSEH (Just fl) $ do
        setVerbosity (simVerbose opts)
        let prover script vs g = do
              let exts = getAllExts g
              glam <- io $ bindExts jsc exts g
              tt <- io $ mkTypedTerm jsc glam
              io $ doExtraChecks opts bsc glam
              r <- evalStateT script (ProofGoal Universal (vsVCName vs) tt)
              case r of
                SS.Unsat -> when (verb >= 3) $ io $ putStrLn "Valid."
                -- TODO: replace x with something
                SS.Sat val -> io $ showCexResults jsc ms vs exts [("x", val)]
                SS.SatMulti vals -> io $ showCexResults jsc ms vs exts vals
        let ovds = vpOver vp
        initPS <- initializeVerification' jsc ms bs cl
        when (verb >= 2) $ liftIO $
          putStrLn $ "Overriding: " ++ show (map specName ovds)
        mapM_ (overrideFromSpec jsc (specPos ms)) ovds
        when (verb >= 2) $ liftIO $
          putStrLn $ "Running method: " ++ specName ms
        -- Execute code.
        run
        when (verb >= 2) $ liftIO $
          putStrLn $ "Checking final state"
        pvc <- checkFinalState jsc ms bs cl initPS
        let pvcs = [pvc] -- Only one for now, but that might change
        when (verb >= 5) $ liftIO $ do
          putStrLn "Verifying the following:"
          mapM_ (print . ppPathVC) pvcs
        let validator script = runValidation (prover script) vp jsc pvcs
        case jsTactic setupRes of
          Skip -> liftIO $ putStrLn $
            "WARNING: skipping verification of " ++ specName ms
          RunVerify script ->
            liftIO $ fmap fst $ runTopLevel (validator script) ro rw
    endTime <- io $ getCurrentTime
    io $ putStrLn $ "Successfully verified " ++ specName ms ++ overrideText ++
                    " (" ++ showDuration (diffUTCTime endTime startTime) ++ ")"
  unless (jsSimulate setupRes) $ io $ putStrLn $
    "WARNING: skipping simulation of " ++ specName ms
  return ms

doExtraChecks :: Options -> SharedContext s -> SharedTerm s -> IO ()
doExtraChecks opts bsc t = do
  let verb = simVerbose opts
  when (extraChecks opts) $ do
    when (verb >= 2) $ putStrLn "Type checking goal..."
    tcr <- scTypeCheck bsc t
    case tcr of
      Left e -> putStr $ unlines $
                "Ill-typed goal constructed." : prettyTCError e
      Right _ -> when (verb >= 2) $ putStrLn "Done."
  when (verb >= 6) $ putStrLn $ "Trying to prove: " ++ show t

showCexResults :: SharedContext SAWCtx
               -> JavaMethodSpecIR
               -> VerifyState
               -> [ExtCns (SharedTerm SAWCtx)]
               -> [(String, FiniteValue)]
               -> IO ()
showCexResults sc ms vs exts vals = do
  putStrLn $ "When verifying " ++ specName ms ++ ":"
  putStrLn $ "Proof of " ++ vsVCName vs ++ " failed."
  putStrLn $ "Counterexample: "
  mapM_ (\(n, v) -> putStrLn ("  " ++ n ++ ": " ++ show v)) vals
  if (length exts == length vals)
    then do let cexEval = cexEvalFn sc (zip exts (map snd vals))
            doc <- vsCounterexampleFn vs cexEval
            putStrLn (displayS (renderPretty 0.8 80 doc) "")
    else putStrLn "ERROR: Can't show result, wrong number of values"
  fail "Proof failed."

mkMixedExpr :: SharedContext SAWCtx
            -> SharedTerm SAWCtx
            -> JavaSetup MixedExpr
mkMixedExpr _ (asJavaExpr -> Just s) =
  (JE . fst) <$> getJavaExpr "mkMixedExpr" s
mkMixedExpr sc t = do
  let exts = getAllExts t
      extNames = map ecName exts
  jes <- mapM (getJavaExpr "mkMixedExpr") extNames
  fn <- liftIO $ scAbstractExts sc exts t
  return $ LE $ LogicExpr fn (map fst jes)

exportJSSType :: JavaType -> JavaSetup Type
exportJSSType jty =
  case jty of
    JavaBoolean     -> return BooleanType
    JavaByte        -> return ByteType
    JavaChar        -> return CharType
    JavaShort       -> return ShortType
    JavaInt         -> return IntType
    JavaLong        -> return LongType
    JavaFloat       -> return FloatType
    JavaDouble      -> return DoubleType
    JavaArray _ ety -> ArrayType <$> exportJSSType ety
    JavaClass name  -> return $ ClassType (dotsToSlashes name)

exportJavaType :: Codebase -> JavaType -> JavaSetup JavaActualType
exportJavaType cb jty =
  case jty of
    JavaBoolean     -> return $ PrimitiveType BooleanType
    JavaByte        -> return $ PrimitiveType ByteType
    JavaChar        -> return $ PrimitiveType CharType
    JavaShort       -> return $ PrimitiveType ShortType
    JavaInt         -> return $ PrimitiveType IntType
    JavaLong        -> return $ PrimitiveType LongType
    JavaFloat       -> return $ PrimitiveType FloatType
    JavaDouble      -> return $ PrimitiveType DoubleType
    JavaArray n t   -> ArrayInstance (fromIntegral n) <$> exportJSSType t
    JavaClass name  ->
      do cls <- liftIO $ lookupClass cb fixPos (dotsToSlashes name)
         return (ClassInstance cls)

checkCompatibleType :: String
                    -> JavaActualType
                    -> Cryptol.Schema
                    -> JavaSetup ()
checkCompatibleType msg aty schema = do
  case cryptolTypeOfActual aty of
    Nothing ->
      fail $ "Type is not translatable: " ++ show aty ++ " (" ++ msg ++ ")"
    Just lt -> do
      unless (Cryptol.Forall [] [] lt == schemaNoUser schema) $ fail $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ Cryptol.pretty lt
                , "  Got: " ++ Cryptol.pretty schema
                , "  In context: " ++ msg
                ]

parseJavaExpr' :: (MonadIO m) =>
                  JSS.Codebase -> JSS.Class -> JSS.Method -> String
               -> m JavaExpr
parseJavaExpr' cb cls meth name =
  liftIO (runExceptT (parseJavaExpr cb cls meth name) >>= either fail return)

getJavaExpr :: String -> String -> JavaSetup (JavaExpr, JavaActualType)
getJavaExpr ctx name = do
  ms <- gets jsSpec
  let cb = specCodebase ms
      cls = specThisClass ms
      meth = specMethod ms
  e <- parseJavaExpr' cb cls meth name
  case Map.lookup e (bsActualTypeMap (specBehaviors ms)) of
    Just ty -> return (e, ty)
    Nothing -> fail $ "Unknown expression " ++ name ++ " in " ++ ctx

typeJavaExpr :: BuiltinContext -> String -> JavaType
             -> JavaSetup (JavaExpr, JavaActualType)
typeJavaExpr bic name ty = do
  ms <- gets jsSpec
  let cb = biJavaCodebase bic
  expr <- parseJavaExpr' cb (specThisClass ms) (specMethod ms) name
  jty' <- exportJSSType ty
  checkEqualTypes (exprType expr) jty' name
  aty <- exportJavaType cb ty
  return (expr, aty)

checkEqualTypes :: Type -> Type -> String -> JavaSetup ()
checkEqualTypes declared actual name =
  when (declared /= actual) $ fail $ show $
    hsep [ text "WARNING: Declared type"
         , text (show (ppType declared)) -- TODO: change pretty-printer
         , text "doesn't match actual type"
         , text (show (ppType actual)) -- TODO: change pretty-printer
         , text "for variable"
         , text name
         ]

modifySpec :: (JavaMethodSpecIR -> JavaMethodSpecIR) -> JavaSetup ()
modifySpec f = modify $ \st -> st { jsSpec = f (jsSpec st) }

javaPure :: JavaSetup ()
javaPure = return ()

javaNoSimulate :: JavaSetup ()
javaNoSimulate = modify (\s -> s { jsSimulate = False })

javaSatBranches :: Bool -> JavaSetup ()
javaSatBranches doSat = modify (\s -> s { jsSatBranches = doSat })

javaRequiresClass :: String -> JavaSetup ()
javaRequiresClass cls = modifySpec $ \ms ->
  let clss' = cls : specInitializedClasses ms in
  ms { specInitializedClasses = clss' }

javaClassVar :: BuiltinContext -> Options -> String -> JavaType
             -> JavaSetup ()
javaClassVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  case aty of
    ClassInstance _ -> return ()
    _ -> fail "Can't use `java_class_var` with variable of non-class type."
  modifySpec (specAddVarDecl expr aty)

javaVar :: BuiltinContext -> Options -> String -> JavaType
        -> JavaSetup (TypedTerm SAWCtx)
javaVar bic _ name t = do
  --liftIO $ putStrLn "javaVar"
  (expr, aty) <- typeJavaExpr bic name t
  case aty of
    ClassInstance _ -> fail "Can't use `java_var` with variable of class type."
    _ -> return ()
  modifySpec (specAddVarDecl expr aty)
  let sc = biSharedContext bic
  liftIO $ do
    Just lty <- logicTypeOfActual sc aty
    scJavaValue sc lty name >>= mkTypedTerm sc

javaMayAlias :: BuiltinContext -> Options -> [String]
             -> JavaSetup ()
javaMayAlias _ _ exprs = do
  exprList <- mapM (getJavaExpr "java_may_alias") exprs
  modifySpec (specAddAliasSet (map fst exprList))

javaAssert :: BuiltinContext -> Options -> TypedTerm SAWCtx
           -> JavaSetup ()
javaAssert bic _ (TypedTerm schema v) = do
  --liftIO $ putStrLn "javaAssert"
  unless (schemaNoUser schema == Cryptol.Forall [] [] Cryptol.tBit) $
    fail $ "java_assert passed expression of non-boolean type: " ++ show schema
  me <- mkMixedExpr (biSharedContext bic) v
  case me of
    LE le -> modifySpec (specAddAssumption le)
    JE je -> fail $ "Used java_assert with Java expression: " ++ show je

javaAssertEq :: BuiltinContext -> Options -> String -> TypedTerm SAWCtx
           -> JavaSetup ()
javaAssertEq bic _ name (TypedTerm schema t) = do
  --liftIO $ putStrLn "javaAssertEq"
  (expr, aty) <- (getJavaExpr "java_assert_eq") name
  checkCompatibleType "java_assert_eq" aty schema
  me <- mkMixedExpr (biSharedContext bic) t
  modifySpec (specAddLogicAssignment fixPos expr me)

javaEnsureEq :: BuiltinContext -> Options -> String -> TypedTerm SAWCtx
             -> JavaSetup ()
javaEnsureEq bic _ name (TypedTerm schema t) = do
  --liftIO $ putStrLn "javaEnsureEq"
  ms <- gets jsSpec
  (expr, aty) <- (getJavaExpr "java_ensure_eq") name
  --liftIO $ putStrLn "Making MixedExpr"
  when (isArg (specMethod ms) expr && isScalarExpr expr) $ fail $
    "The `java_ensure_eq` function cannot be used " ++
    "to set the value of a scalar argument."
  checkCompatibleType "java_ensure_eq" aty schema
  me <- mkMixedExpr (biSharedContext bic) t
  --liftIO $ putStrLn "Done making MixedExpr"
  cmd <- case (CC.unTerm expr, aty) of
    (_, ArrayInstance _ _) -> return (EnsureArray fixPos expr me)
    (InstanceField r f, _) -> return (EnsureInstanceField fixPos r f me)
    (StaticField f, _) -> return (EnsureStaticField fixPos f me)
    _ -> fail $ "invalid java_ensure target: " ++ name
  modifySpec (specAddBehaviorCommand cmd)

javaModify :: BuiltinContext -> Options -> String
           -> JavaSetup ()
javaModify _bic _ name = do
  --liftIO $ putStrLn "javaModify"
  ms <- gets jsSpec
  (expr, aty) <- (getJavaExpr "java_modify") name
  when (isArg (specMethod ms) expr && isScalarExpr expr) $ fail $
    "The `java_modify` function cannot be used " ++
    "to set the value of a scalar argument."
  cmd <- case (CC.unTerm expr, aty) of
    (_, ArrayInstance _ _) -> return (ModifyArray expr aty)
    (InstanceField r f, _) -> return (ModifyInstanceField r f)
    (StaticField f, _) -> return (ModifyStaticField f)
    _ -> fail $ "invalid java_modify target: " ++ name
  modifySpec (specAddBehaviorCommand cmd)

javaReturn :: BuiltinContext -> Options -> TypedTerm SAWCtx
           -> JavaSetup ()
javaReturn bic _ (TypedTerm _ t) = do
  --liftIO $ putStrLn "javaReturn"
  ms <- gets jsSpec
  let meth = specMethod ms
  case methodReturnType meth of
    Just _ty -> do
      -- TODO: check that types are compatible
      me <- mkMixedExpr (biSharedContext bic) t
      modifySpec (specAddBehaviorCommand (ReturnValue me))
    Nothing ->
      fail $ "can't use `java_return` on void method " ++ methodName meth

javaVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SatResult
                 -> JavaSetup ()
javaVerifyTactic _ _ script =
  modify $ \st -> st { jsTactic = RunVerify script }

javaAllowAlloc :: JavaSetup ()
javaAllowAlloc = modifySpec specSetAllowAllocation
