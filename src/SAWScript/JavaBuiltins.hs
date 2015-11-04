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
import Text.Read (readMaybe)

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

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SS

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

typeOfValue :: JSS.Value a -> JSS.Type
typeOfValue (IValue _) = JSS.IntType
typeOfValue (LValue _) = JSS.LongType
typeOfValue (RValue (Ref _ ty)) = ty
typeOfValue (RValue NullRef) = error "Can't get type of null reference."
typeOfValue (FValue _) = JSS.FloatType
typeOfValue (DValue _) = JSS.DoubleType
typeOfValue (AValue _) = error "Can't get type of address value."

writeJavaTerm :: (MonadSim SAWBackend m) =>
                 SharedContext SAWCtx
              -> JavaExpr
              -> TypedTerm SAWCtx
              -> Simulator SAWBackend m ()
writeJavaTerm sc expr@(CC.Term e) tm = do
  liftIO $ putStrLn "write"
  v <- valueOfTerm sc tm
  let vty = typeOfValue v
      ety = exprType expr
  unless (vty == ety) $ fail $
    "Writing value of type " ++ show vty ++
    " to location of type " ++ show ety ++ "."
  case e of
    ReturnVal _ -> fail "Can't set return value"
    Local _ idx _ -> setLocal idx v
    InstanceField rexp f -> do
      rv <- readJavaValue rexp
      case rv of
        RValue r -> setInstanceFieldValue r f v
        _ -> fail "Instance argument of instance field evaluates to non-reference"
    StaticField f -> setStaticFieldValue f v

readJavaTerm :: (MonadSim sbe m) =>
                JavaExpr -> Simulator sbe m (SBETerm sbe)
readJavaTerm et = termOfValue =<< readJavaValue et

termOfValue :: (MonadSim sbe m) =>
               JSS.Value (SBETerm sbe) -> Simulator sbe m (SBETerm sbe)
termOfValue (IValue t) = return t
termOfValue (LValue t) = return t
termOfValue (RValue r@(Ref _ (ArrayType _))) = do
  -- TODO: handle arrays of references
  ma <- getSymbolicArray r
  case ma of
    Just (_, t) -> return t
    Nothing -> fail "Reference not found in arrays map"
termOfValue (RValue (Ref _ (ClassType _))) =
  fail "Translating objects to terms not yet implemented" -- TODO
termOfValue _ = fail "Can't convert term to value"

byteExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
byteExtend sc x = do
  n24 <- scNat sc 24
  n8 <- scNat sc 8
  scBvUExt sc n24 n8 x

shortExtend :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
shortExtend sc x = do
  n16 <- scNat sc 16
  scBvUExt sc n16 n16 x

type SAWBackend = SharedContext SAWCtx

valueOfTerm :: (MonadSim SAWBackend m) =>
               SharedContext SAWCtx
            -> TypedTerm SAWCtx
            -> Simulator SAWBackend m (JSS.Value (SharedTerm SAWCtx))
valueOfTerm sc (TypedTerm _schema t) = do
  -- TODO: the following is silly since we have @schema@ in scope
  ty <- liftIO $ (scTypeOf sc t >>= scWhnf sc)
  case ty of
    (asBitvectorType -> Just 8) -> IValue <$> (liftIO $ byteExtend sc t)
    (asBitvectorType -> Just 16) -> IValue <$> (liftIO $ shortExtend sc t)
    (asBitvectorType -> Just 32) -> return (IValue t)
    (asBitvectorType -> Just 64) -> return (LValue t)
    (asVecType -> Just (n :*: ety)) -> do
      jty <- case ety of
               (asBitvectorType -> Just 8) -> return ByteType
               (asBitvectorType -> Just 16) -> return ShortType
               (asBitvectorType -> Just 32) -> return IntType
               (asBitvectorType -> Just 64) -> return LongType
               _ -> fail $ "Unsupported array element type: " ++ show ety
      RValue <$> newSymbolicArray (ArrayType jty) (fromIntegral n) t
    _ -> fail $ "Can't translate term of type: " ++ show ty
-- If vector of other things, allocate array, translate those things, and store
-- If record, allocate appropriate object, translate fields, assign fields
-- For the last case, we need information about the desired Java type

readJavaValue :: (MonadSim sbe m) =>
                 JavaExpr
              -> Simulator sbe m (JSS.Value (SBETerm sbe))
readJavaValue (CC.Term e) = do
  case e of
    ReturnVal _ -> do
      mrv <- getProgramReturnValue
      case mrv of
        Just rv -> return rv
        Nothing -> fail "Return value not found"
    Local _ idx _ -> do
      p <- getPath "readJavaValue"
      case currentCallFrame p of
        Just cf ->
          case Map.lookup idx (cf ^. cfLocals) of
            Just v -> return v
            Nothing -> fail $ "Local variable " ++ show idx ++ " not found"
        Nothing -> fail "No current call frame"
    InstanceField rexp f -> do
      v <- readJavaValue rexp
      case v of
        RValue r -> getInstanceFieldValue r f
        _ -> fail "Object in instance field expr evaluated to non-reference"
    StaticField f -> getStaticFieldValue f

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
      outtms <- mapM readJavaTerm outexprs
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
              Just v -> termOfValue v
      liftIO $ do
        let sc = biSharedContext bic
        argBinds <- reverse <$> readIORef argsRef
        exts <- mapM asExtCns argBinds
        -- TODO: group argBinds according to the declared types
        bindExts jsc exts dt >>= mkTypedTerm sc

freshJavaVal :: (MonadIO m, Functor m) =>
                Maybe (IORef [SharedTerm SAWCtx])
             -> SharedContext SAWCtx
             -> JavaActualType
             -> Simulator SAWBackend m (JSS.Value (SharedTerm SAWCtx))
freshJavaVal _ _ (PrimitiveType ty) = do
  case ty of
    BooleanType -> withSBE $ \sbe -> IValue <$> freshBool sbe
    ByteType    -> withSBE $ \sbe -> IValue <$> freshByte sbe
    CharType    -> withSBE $ \sbe -> IValue <$> freshChar sbe
    ShortType   -> withSBE $ \sbe -> IValue <$> freshShort sbe
    IntType     -> withSBE $ \sbe -> IValue <$> freshInt sbe
    LongType    -> withSBE $ \sbe -> LValue <$> freshLong sbe
    _ -> fail $ "Can't create fresh primitive value of type " ++ show ty
freshJavaVal argsRef sc (ArrayInstance n ty) | isPrimitiveType ty = do
  -- TODO: should this use bvAt?
  elts <- liftIO $ do
    ety <- scBitvector sc (fromIntegral (JSS.stackWidth ty))
    ntm <- scNat sc (fromIntegral n)
    aty <- scVecType sc ntm ety
    atm <- scFreshGlobal sc "_" aty
    maybe (return ()) (\r -> modifyIORef r (atm :)) argsRef
    mapM (scAt sc ntm ety atm) =<< mapM (scNat sc) [0..(fromIntegral n) - 1]
  case ty of
    LongType -> RValue <$> newLongArray elts
    _ | isIValue ty -> RValue <$> newIntArray (ArrayType ty) elts
    _ -> fail $ "Can't create array with element type " ++ show ty
-- TODO: allow input declarations to specialize types of fields
freshJavaVal _ _ (ArrayInstance _ _) =
  fail $ "Can't create fresh array of non-scalar elements"
freshJavaVal argsRef sc (ClassInstance c) = do
  r <- createInstance (className c) Nothing
  forM_ (classFields c) $ \f -> do
    let ty = fieldType f
    v <- freshJavaVal argsRef sc (PrimitiveType ty)
    setInstanceFieldValue r (FieldId (className c) (fieldName f) ty) v
  return (RValue r)

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
    forM_ configs $ \(bs,cl) -> withSAWBackend jsc Nothing $ \sbe -> io $ do
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
