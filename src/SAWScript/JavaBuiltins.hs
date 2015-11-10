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
import Data.List (intercalate, partition)
import Data.List.Split
import Data.IORef
import qualified Data.Map as Map
import Data.Time.Clock
import qualified Data.Vector as V
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP
import Text.Read (readMaybe)

import Data.JVM.Symbolic.AST (entryBlock)
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
import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SS
import SAWScript.VerificationCheck

import qualified Cryptol.TypeCheck.AST as Cryptol

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
        e <- liftIO $ parseJavaExpr cb cls meth s
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
      let actualArgTys = map typeOfValue args
          expectedArgTys = methodParameterTypes meth
      forM_ (zip actualArgTys expectedArgTys) $ \ (aty, ety) ->
        unless (aty == ety) $ fail $
        "Passing value of type " ++ show aty ++
        " to argument expected to be of type " ++ show ety ++ "."
      mapM_ (uncurry (writeJavaTerm jsc)) otherAssigns
      _ <- case methodIsStatic meth of
             True -> execStaticMethod (className cls) (methodKey meth) args
             False -> do
               RValue this <- freshJavaVal Nothing jsc (ClassInstance cls)
               execInstanceMethod (className cls) (methodKey meth) this args
      outexprs <- liftIO $ mapM (parseJavaExpr cb cls meth) outputs
      outtms <- mapM readJavaTermSim outexprs
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
    let fl = defaultSimFlags { alwaysBitBlastBranchTerms = True }
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
      dt <- case rslt of
              Nothing -> fail $ "No return value from " ++ methodName meth
              Just v -> termOfValueSim v
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
                        -> Simulator (SharedContext SAWCtx) m (JSS.Path (SharedContext SAWCtx))
initializeVerification' sc ir bs refConfig = do
  -- Generate a reference for each reference equivalence class
  exprRefs <- mapM (genRef . jssTypeOfActual . snd) refConfig
  let _refAssignments = (exprRefs `zip` map fst refConfig)
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
  mapM_ (initStep sc) (bsCommands bs)
  getPath (PP.text "initializeVerification")

initStep :: (Monad m) =>
            SharedContext SAWCtx -> BehaviorCommand
         -> Simulator (SharedContext SAWCtx) m ()
initStep sc (AssertPred _ expr) = do
  c <- logicExprToTermSim sc expr
  addAssertion c
initStep sc (AssumePred expr) = do
  c <- logicExprToTermSim sc expr -- Create term in initial state
  addAssertion c
initStep _ _ = return ()


valueEqTerm :: (MonadIO m) =>
               String
            -> SpecJavaValue
            -> SharedTerm SAWCtx
            -> Simulator (SharedContext SAWCtx) m [VerificationCheck SAWCtx]
valueEqTerm name (IValue t) t' = return [EqualityCheck name t t']
valueEqTerm name (LValue t) t' = return [EqualityCheck name t t']
valueEqTerm name (RValue r) t' = do
  ps <- getPath (PP.text name)
  case Map.lookup r (ps ^. pathMemory . memScalarArrays) of
    Just (_, t) -> return [EqualityCheck name t t']
    Nothing -> fail $ "valueEqTerm: " ++ name ++ ": ref does not point to array"
valueEqTerm name _ _ = fail $ "valueEqTerm: " ++ name ++ ": unspported value type"

-- TODO: have checkStep record a list of all the things it has checked.
-- After it runs, we can go through the final state and check whether
-- there are any unchecked elements of the state.
checkStep :: (MonadIO m) =>
             VerificationState -> BehaviorCommand
          -> Simulator (SharedContext SAWCtx) m [VerificationCheck SAWCtx]
checkStep _ (AssertPred _ _) = return []
checkStep _ (AssumePred _) = return []
checkStep vs (ReturnValue expr) = do
  t <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) expr
  mrv <- getProgramReturnValue
  case mrv of
    Just rv -> valueEqTerm "ReturnValue" rv t
    Nothing -> fail "Return specification, but method did not return a value."
checkStep vs (EnsureInstanceField _pos refExpr f rhsExpr) = do
  rv <- readJavaValueSim refExpr
  case rv of
    RValue ref -> do
      fv <- getInstanceFieldValue ref f
      ft <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
      valueEqTerm "EnsureInstanceField" fv ft
    _ -> fail "Left-hand side of . did not evaluate to a reference."
checkStep vs (EnsureStaticField _pos f rhsExpr) = do
  fv <- getStaticFieldValue f
  ft <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
  valueEqTerm "EnsureStaticField" fv ft
checkStep vs (ModifyInstanceField refExpr f) = do
  rv <- readJavaValueSim refExpr
  case rv of
    RValue ref -> do
      mty <- liftIO $ logicTypeOfJSSType (vsContext vs) (fieldIdType f)
      case mty of
        Just ty -> do
          fv <- getInstanceFieldValue ref f
          ft <- liftIO $ scFreshGlobal (vsContext vs) "_" ty
          valueEqTerm "ModifyInstanceField" fv ft
        Nothing -> fail "Invalid type in java_modify for instance field."
    _ -> fail "Left-hand side of . did not evaluate to a reference."
checkStep vs (ModifyStaticField f) = do
  fv <- getStaticFieldValue f
  mty <- liftIO $ logicTypeOfJSSType (vsContext vs) (fieldIdType f)
  case mty of
    Just ty -> do
      ft <- liftIO $ scFreshGlobal (vsContext vs) "_" ty
      valueEqTerm "ModifyStaticField" fv ft
    Nothing -> fail "Invalid type in java_modify for static field."
checkStep vs (EnsureArray _pos refExpr rhsExpr) = do
  rv <- readJavaValueSim refExpr
  t <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
  valueEqTerm "EnsureArray" rv t
checkStep vs (ModifyArray refExpr aty) = do
  rv <- readJavaValueSim refExpr
  mty <- liftIO $ logicTypeOfActual (vsContext vs) aty
  case mty of
    Just ty -> do
      t <- liftIO $ scFreshGlobal (vsContext vs) "_" ty
      valueEqTerm "ModifyArray" rv t
    Nothing -> fail "Invalid type in java_modify for array."

data VerificationState = VerificationState
                         { vsContext :: SharedContext SAWCtx
                         , vsSpec :: JavaMethodSpecIR
                         , vsInitialState :: JSS.Path (SharedContext SAWCtx)
                         }

checkFinalState :: MonadSim (SharedContext SAWCtx) m =>
                   SharedContext SAWCtx
                -> JavaMethodSpecIR
                -> BehaviorSpec
                -> JSS.Path (SharedContext SAWCtx)
                -> Simulator (SharedContext SAWCtx) m [VerificationCheck SAWCtx]
checkFinalState sc ms bs initPS = do
  let st = VerificationState { vsContext = sc
                             , vsSpec = ms
                             , vsInitialState = initPS
                             }
  vcs <- mapM (checkStep st) (bsCommands bs)
  -- TODO: also compare states, keep track of what we've looked at
  return (concat vcs)

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
      -- print (bsActualTypeMap bs)
      -- print (bsRefExprs bs)
      -- print cl
      when (verb >= 2) $ do
        putStrLn $ "Executing " ++ specName ms ++
                   " at PC " ++ show (bsLoc bs) ++ "."
      -- runDefSimulator cb sbe $ do
      runSimulator cb sbe defaultSEH (Just fl) $ do
        setVerbosity (simVerbose opts)
        esd <- initializeVerification jsc ms bs cl
        res <- mkSpecVC jsc vp esd
        when (verb >= 5) $ liftIO $ do
          putStrLn "Verifying the following:"
          mapM_ (print . ppPathVC) res
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
        case jsTactic setupRes of
          Skip -> liftIO $ putStrLn $
            "WARNING: skipping verification of " ++ specName ms
          RunVerify script ->
            liftIO $ fmap fst $ runTopLevel (runValidation (prover script) vp jsc esd res) ro rw
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
    then vsCounterexampleFn vs (cexEvalFn sc (zip exts (map snd vals))) >>= print
    else putStrLn "ERROR: Can't show result, wrong number of values"
  fail "Proof failed."

parseJavaExpr :: Codebase -> Class -> Method -> String
              -> IO JavaExpr
parseJavaExpr cb cls meth estr = do
  sr <- parseStaticParts cb eparts
  case sr of
    Just e -> return e
    Nothing -> parseParts eparts
  where parseParts :: [String] -> IO JavaExpr
        parseParts [] = fail "empty Java expression"
        parseParts [s] =
          case s of
            "this" | methodIsStatic meth ->
                     fail $ "Can't use 'this' in static method " ++
                            methodName meth
                   | otherwise -> return (thisJavaExpr cls)
            "return" -> case returnJavaExpr meth of
                          Just e -> return e
                          Nothing ->
                            fail $ "No return value for " ++ methodName meth
            ('a':'r':'g':'s':'[':rest) -> do
              let num = fst (break (==']') rest)
              case readMaybe num of
                Just (n :: Int) -> do
                  let i = localIndexOfParameter meth n
                      mlv = lookupLocalVariableByIdx meth 0 i
                      paramTypes = V.fromList .
                                   methodKeyParameterTypes .
                                   methodKey $
                                   meth
                  case mlv of
                    Nothing
                      | n < V.length paramTypes ->
                        return (CC.Term (Local s i (paramTypes V.! (fromIntegral n))))
                      | otherwise ->
                        fail $ "(Zero-based) local variable index " ++ show i ++
                               " for parameter " ++ show n ++ " doesn't exist"
                    Just lv -> return (CC.Term (Local s i (localType lv)))
                Nothing -> fail $ "bad Java expression syntax: " ++ s
            _ | hasDebugInfo meth -> do
                  let mlv = lookupLocalVariableByName meth 0 s
                  case mlv of
                    Nothing -> fail $ "local " ++ s ++ " doesn't exist, expected one of: " ++
                                 unwords (map localName (localVariableEntries meth 0))
                    Just lv -> return (CC.Term (Local s i ty))
                      where i = localIdx lv
                            ty = localType lv
              | otherwise ->
                  fail $ "variable " ++ s ++
                         " referenced by name, but no debug info available"
        parseParts (f:rest) = do
          e <- parseParts rest
          let jt = exprType e
              pos = fixPos -- TODO
          fid <- findField cb pos jt f
          return (CC.Term (InstanceField e fid))
        eparts = reverse (splitOn "." estr)

parseStaticParts :: Codebase -> [String] -> IO (Maybe JavaExpr)
parseStaticParts cb (fname:rest) = do
  let cname = intercalate "/" (reverse rest)
  mc <- tryLookupClass cb cname
  case mc of
    Just c ->
      case filter ((== fname) . fieldName) (classFields c) of
        [f] -> return (Just (CC.Term fld))
          where fld =  StaticField (FieldId cname fname (fieldType f))
        _ -> return Nothing
    Nothing -> return Nothing
parseStaticParts _ _ = return Nothing

mkMixedExpr :: SharedContext SAWCtx
            -> JavaMethodSpecIR
            -> SharedTerm SAWCtx
            -> IO MixedExpr
mkMixedExpr _ ms (asJavaExpr -> Just s) = JE <$> getJavaExpr ms s
mkMixedExpr sc ms t = do
  let exts = getAllExts t
      extNames = map ecName exts
  javaExprs <- mapM (getJavaExpr ms) extNames
  le <- LogicExpr <$> scAbstractExts sc exts t <*> pure javaExprs
  return (LE le)

exportJSSType :: JavaType -> JavaSetup Type
exportJSSType jty =
  case jty of
    JavaBoolean     -> return BooleanType
    JavaByte        -> return ByteType
    JavaChar        -> return CharType
    JavaShort       -> return ShortType
    JavaInt         -> return IntType
    JavaLong        -> return LongType
    JavaFloat       -> fail "exportJSSType: Can't translate float type"
    JavaDouble      -> fail "exportJSSType: Can't translate double type"
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
    JavaFloat       -> fail "exportJavaType: Can't translate float type"
    JavaDouble      -> fail "exportJavaType: Can't translate double type"
    JavaArray n t   -> ArrayInstance (fromIntegral n) <$> exportJSSType t
    JavaClass name  ->
      do cls <- liftIO $ lookupClass cb fixPos (dotsToSlashes name)
         return (ClassInstance cls)

checkCompatibleExpr :: String -> JavaExpr -> Cryptol.Schema -> JavaSetup ()
checkCompatibleExpr msg expr schema = do
  jsState <- get
  let atm = specActualTypeMap (jsSpec jsState)
  liftIO $ case Map.lookup expr atm of
    Nothing -> fail $ "No type found for Java expression: " ++ show expr ++
                      " (" ++ msg ++ ")"
    Just aty -> liftIO $ checkCompatibleType msg aty schema

checkCompatibleType :: String
                    -> JavaActualType
                    -> Cryptol.Schema
                    -> IO ()
checkCompatibleType msg aty schema = do
  case cryptolTypeOfActual aty of
    Nothing ->
      fail $ "Type is not translatable: " ++ show aty ++ " (" ++ msg ++ ")"
    Just lt -> do
      unless (Cryptol.Forall [] [] lt == schema) $ fail $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ show lt
                , "  Got: " ++ show schema
                , "  In context: " ++ msg
                ]

javaPure :: JavaSetup ()
javaPure = return ()

typeJavaExpr :: BuiltinContext -> String -> JavaType
             -> JavaSetup (JavaExpr, JavaActualType)
typeJavaExpr bic name ty = do
  jsState <- get
  let ms = jsSpec jsState
      cb = biJavaCodebase bic
      cls = specThisClass ms
      meth = specMethod ms
  expr <- liftIO $ parseJavaExpr (biJavaCodebase bic) cls meth name
  let jty = exprType expr
  jty' <- exportJSSType ty
  liftIO $ checkEqualTypes jty jty' name
  aty <- exportJavaType cb ty
  return (expr, aty)

checkEqualTypes :: Type -> Type -> String -> IO ()
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

javaNoSimulate :: JavaSetup ()
javaNoSimulate = modify (\s -> s { jsSimulate = False })

javaSatBranches :: Bool -> JavaSetup ()
javaSatBranches doSat = modify (\s -> s { jsSatBranches = doSat })

javaClassVar :: BuiltinContext -> Options -> String -> JavaType
             -> JavaSetup ()
javaClassVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  case exprType expr of
    ClassType _ -> return ()
    _ -> fail "Can't use `java_class_var` with variable of non-class type."
  modifySpec (specAddVarDecl expr aty)

javaVar :: BuiltinContext -> Options -> String -> JavaType
        -> JavaSetup (TypedTerm SAWCtx)
javaVar bic _ name t = do
  --liftIO $ putStrLn "javaVar"
  (expr, aty) <- typeJavaExpr bic name t
  case exprType expr of
    ClassType _ -> fail "Can't use `java_var` with variable of class type."
    _ -> return ()
  modifySpec (specAddVarDecl expr aty)
  let sc = biSharedContext bic
  liftIO $ do
    Just lty <- logicTypeOfActual sc aty
    scJavaValue sc lty name >>= mkTypedTerm sc

javaMayAlias :: BuiltinContext -> Options -> [String]
             -> JavaSetup ()
javaMayAlias _ _ exprs = do
  ms <- gets jsSpec
  exprList <- liftIO $ mapM (getJavaExpr ms) exprs
  -- TODO: check that all expressions exist and have the same type
  modifySpec (specAddAliasSet exprList)

javaAssert :: BuiltinContext -> Options -> TypedTerm SAWCtx
           -> JavaSetup ()
javaAssert bic _ (TypedTerm schema v) = do
  --liftIO $ putStrLn "javaAssert"
  let sc = biSharedContext bic
  ms <- gets jsSpec
  unless (schema == Cryptol.Forall [] [] Cryptol.tBit) $
    fail $ "java_assert passed expression of non-boolean type: " ++ show schema
  me <- liftIO $ mkMixedExpr sc ms v
  case me of
    LE le -> modifySpec (specAddBehaviorCommand (AssertPred fixPos le))
    JE je -> fail $ "Used java_assert with Java expression: " ++ show je

getJavaExpr :: (MonadIO m) =>
               JavaMethodSpecIR -> String
            -> m JavaExpr
getJavaExpr ms name = do
  let cb = specCodebase ms
      cls = specThisClass ms
      meth = specMethod ms
  liftIO $ parseJavaExpr cb cls meth name

javaAssertEq :: BuiltinContext -> Options -> String -> TypedTerm SAWCtx
           -> JavaSetup ()
javaAssertEq bic _ name (TypedTerm schema t) = do
  --liftIO $ putStrLn "javaAssertEq"
  ms <- gets jsSpec
  let sc = biSharedContext bic
  expr <- getJavaExpr ms name
  checkCompatibleExpr "java_assert_eq" expr schema
  me <- liftIO $ mkMixedExpr sc ms t
  modifySpec (specAddLogicAssignment fixPos expr me)

javaEnsureEq :: BuiltinContext -> Options -> String -> TypedTerm SAWCtx
             -> JavaSetup ()
javaEnsureEq bic _ name (TypedTerm schema t) = do
  --liftIO $ putStrLn "javaEnsureEq"
  ms <- gets jsSpec
  expr <- getJavaExpr ms name
  let sc = biSharedContext bic
      meth = specMethod ms
      ty = exprType expr
  --liftIO $ putStrLn "Making MixedExpr"
  when (isArg meth expr && isScalarExpr expr) $ fail $
    "The `java_ensure_eq` function cannot be used " ++
    "to set the value of a scalar argument."
  checkCompatibleExpr "java_ensure_eq" expr schema
  me <- liftIO $ mkMixedExpr sc ms t
  --liftIO $ putStrLn "Done making MixedExpr"
  cmd <- case (CC.unTerm expr, ty) of
    (_, ArrayType _) -> return (EnsureArray fixPos expr me)
    (InstanceField r f, _) -> return (EnsureInstanceField fixPos r f me)
    (StaticField f, _) -> return (EnsureStaticField fixPos f me)
    _ -> fail $ "invalid java_ensure target: " ++ name
  modifySpec (specAddBehaviorCommand cmd)

javaModify :: BuiltinContext -> Options -> String
           -> JavaSetup ()
javaModify _bic _ name = do
  --liftIO $ putStrLn "javaModify"
  ms <- gets jsSpec
  expr <- getJavaExpr ms name
  let meth = specMethod ms
  when (isArg meth expr && isScalarExpr expr) $ fail $
    "The `java_modify` function cannot be used " ++
    "to set the value of a scalar argument."
  let mty = Map.lookup expr (bsActualTypeMap (specBehaviors ms))
  cmd <- case (CC.unTerm expr, mty) of
    (_, Just ty@(ArrayInstance _ _)) -> return (ModifyArray expr ty)
    (InstanceField r f, _) -> return (ModifyInstanceField r f)
    (StaticField f, _) -> return (ModifyStaticField f)
    _ -> fail $ "invalid java_modify target: " ++ name
  modifySpec (specAddBehaviorCommand cmd)

javaReturn :: BuiltinContext -> Options -> TypedTerm SAWCtx
           -> JavaSetup ()
javaReturn bic _ (TypedTerm _ t) = do
  --liftIO $ putStrLn "javaReturn"
  -- TODO: check that types are compatible
  ms <- gets jsSpec
  me <- liftIO $ mkMixedExpr (biSharedContext bic) ms t
  modifySpec (specAddBehaviorCommand (ReturnValue me))

javaVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SatResult
                 -> JavaSetup ()
javaVerifyTactic _ _ script =
  modify $ \st -> st { jsTactic = RunVerify script }

javaAllowAlloc :: JavaSetup ()
javaAllowAlloc = modifySpec specSetAllowAllocation
