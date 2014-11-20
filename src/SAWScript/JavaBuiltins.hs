{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module SAWScript.JavaBuiltins where

import Control.Applicative hiding (empty)
import Control.Monad.State
import qualified Data.ABC as ABC
import Data.List (intercalate)
import Data.List.Split
import Data.IORef
import Data.Maybe
import qualified Data.Map as Map
import Data.Time.Clock
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read (readMaybe)

import Language.JVM.Common

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

import Verifier.Java.Codebase hiding (lookupClass)
import Verifier.Java.Simulator as JSS hiding (lookupClass)
import Verifier.Java.SAWBackend

import Verifier.SAW.Recognizer
import Verifier.SAW.FiniteValue
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

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


loadJavaClass :: BuiltinContext -> String -> IO Class
loadJavaClass bic =
  lookupClass (biJavaCodebase bic) fixPos . dotsToSlashes

browseJavaClass :: Class -> IO ()
browseJavaClass = print . prettyClass

prettyClass :: Class -> Doc
prettyClass cls = vcat $
  [ empty
  , text "Class name:" <+> text (className cls) <+>
    parens (commas attrs)
  , text "Superclass:" <+> text (fromMaybe "none" (superClass cls))
  , empty
  ] ++
  (if null (classInterfaces cls)
      then []
      else [ text "Interfaces:"
           , indent 2 (vcat (map text (classInterfaces cls)))
           , empty
           ]) ++
  [ text "Fields:"
  , indent 2 (vcat (map prettyField (classFields cls)))
  , empty
  , text "Methods:"
  , indent 2 (vcat (map prettyMethod (classMethods cls)))
  , empty
  ]
  where attrs = concat
          [ if classIsPublic cls then [text "public"] else []
          , if classIsFinal cls then [text "final"] else []
          , if classHasSuperAttribute cls then [text "super"] else []
          , if classIsInterface cls then [text "interface"] else []
          , if classIsAbstract cls then [text "abstract"] else []
          ]

prettyField :: Field -> Doc
prettyField f = hsep $
  [ text (show (fieldVisibility f)) ] ++
  attrs ++
  [ text (show (ppType (fieldType f))) -- TODO: Ick. Different PPs.
  , text (fieldName f)
  ]
  where attrs = concat
          [ if fieldIsStatic f then [text "static"] else []
          , if fieldIsFinal f then [text "final"] else []
          , if fieldIsVolatile f then [text "volatile"] else []
          , if fieldIsTransient f then [text "transient"] else []
          ]

prettyMethod :: Method -> Doc
prettyMethod m =
  hsep [ maybe (text "void") prettyType ret
       , text name
       , (parens . commas . map prettyType) params
       ]
  where (MethodKey name params ret) = methodKey m
        prettyType = text . show . ppType -- TODO: Ick.

commas :: [Doc] -> Doc
commas = sep . punctuate comma

extractJava :: BuiltinContext -> Options -> Class -> String
            -> JavaSetup ()
            -> IO (TypedTerm SAWCtx)
extractJava bic opts cls mname setup = do
  let cb = biJavaCodebase bic
      pos = fixPos
  argsRef <- newIORef []
  (jsc, sbe) <- createSAWBackend (Just argsRef)
  setupRes <- runJavaSetup pos cb cls mname jsc setup
  let fl = defaultSimFlags { alwaysBitBlastBranchTerms = True }
      meth = specMethod (jsSpec setupRes)
  runSimulator cb sbe defaultSEH (Just fl) $ do
    setVerbosity (simVerbose opts)
    args <- mapM (freshJavaArg sbe) (methodParameterTypes meth)
    rslt <- execStaticMethod (className cls) (methodKey meth) args
    dt <- case rslt of
            Nothing -> fail "No return value from "
            Just (IValue t) -> return t
            Just (LValue t) -> return t
            _ -> fail "Unimplemented result type from "
    liftIO $ do
      let sc = biSharedContext bic
      argBinds <- reverse <$> readIORef argsRef
      bindExts jsc argBinds dt >>= scImport sc >>= mkTypedTerm sc

freshJavaArg :: MonadIO m =>
                Backend sbe
             -> Type
             -> m (AtomicValue d f (SBETerm sbe) (SBETerm sbe) r)
freshJavaArg sbe BooleanType = liftIO (IValue <$> freshBool sbe)
freshJavaArg sbe ByteType    = liftIO (IValue <$> freshByte sbe)
freshJavaArg sbe CharType    = liftIO (IValue <$> freshChar sbe)
freshJavaArg sbe ShortType   = liftIO (IValue <$> freshShort sbe)
freshJavaArg sbe IntType     = liftIO (IValue <$> freshInt sbe)
freshJavaArg sbe LongType    = liftIO (LValue <$> freshLong sbe)
freshJavaArg _ ty = fail $ "Unsupported argument type: " ++ show ty

freshJavaVal :: MonadSim sbe m =>
                JavaActualType -> Simulator sbe m (JSS.Value (SBETerm sbe))
freshJavaVal (PrimitiveType ty) = do
  case ty of
    BooleanType -> withSBE $ \sbe -> IValue <$> freshBool sbe
    ByteType    -> withSBE $ \sbe -> IValue <$> freshByte sbe
    CharType    -> withSBE $ \sbe -> IValue <$> freshChar sbe
    ShortType   -> withSBE $ \sbe -> IValue <$> freshShort sbe
    IntType     -> withSBE $ \sbe -> IValue <$> freshInt sbe
    LongType    -> withSBE $ \sbe -> LValue <$> freshLong sbe
    _ -> fail $ "Can't create fresh primitive value of type " ++ show ty
freshJavaVal (ArrayInstance n ty) = do
  elts <- replicateM n (freshJavaVal (PrimitiveType ty))
  let getLVal (LValue t) = Just t
      getLVal _ = Nothing
      getIVal (IValue t) = Just t
      getIVal _ = Nothing
  case ty of
    LongType -> RValue <$> newLongArray (mapMaybe getLVal elts)
    _ | isIValue ty ->
        RValue <$> newIntArray (ArrayType ty) (mapMaybe getIVal elts)
    _ -> fail $ "Can't create array with element type " ++ show ty
freshJavaVal (ClassInstance c) =
  fail $ "Can't create fresh instance of class " ++ className c

createSAWBackend :: Maybe (IORef [SharedTerm JSSCtx])
                 -> IO (SharedContext JSSCtx, Backend (SharedContext JSSCtx))
createSAWBackend argsRef = do
  let imps = [CryptolSAW.cryptolModule]
      vjavaModule = foldr insImport javaModule imps
  sc0 <- mkSharedContext vjavaModule
  -- ss <- basic_ss sc0
  let (jsc :: SharedContext JSSCtx) = sc0 -- rewritingSharedContext sc0 ss
  -- TODO: should we refactor to use withNewGraph?
  ABC.SomeGraph be <- ABC.newGraph ABC.giaNetwork
  sbe <- sawBackend jsc argsRef be
  return (jsc, sbe)

runJavaSetup :: Pos -> Codebase -> Class -> String -> SharedContext JSSCtx
             -> StateT JavaSetupState IO a
             -> IO JavaSetupState
runJavaSetup pos cb cls mname jsc setup = do
  ms <- initMethodSpec pos cb cls mname
  let setupState = JavaSetupState {
                     jsSpec = ms
                   , jsContext = jsc
                   , jsTactic = Skip
                   }
  snd <$> runStateT setup setupState

verifyJava :: BuiltinContext -> Options -> Class -> String
           -> [JavaMethodSpecIR]
           -> JavaSetup ()
           -> IO JavaMethodSpecIR
verifyJava bic opts cls mname overrides setup = do
  startTime <- getCurrentTime
  let pos = fixPos -- TODO
      cb = biJavaCodebase bic
  (jsc, sbe) <- createSAWBackend Nothing
  setupRes <- runJavaSetup pos cb cls mname jsc setup
  let ms = jsSpec setupRes
  let vp = VerifyParams {
             vpCode = cb
           , vpContext = jsc
           , vpOpts = opts
           , vpSpec = ms
           , vpOver = overrides
           }
  let verb = simVerbose opts
      overrideText =
        case overrides of
          [] -> ""
          irs -> " (overriding " ++ show (map renderName irs) ++ ")"
      renderName ir = className (specMethodClass ir) ++ "." ++
                      methodName (specMethod ir)
  when (verb >= 2) $ putStrLn $ "Starting verification of " ++ specName ms
  let configs = [ (bs, cl)
                | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                , cl <- bsRefEquivClasses bs
                ]
  forM_ configs $ \(bs,cl) -> do
    when (verb >= 2) $ do
      putStrLn $ "Executing " ++ specName ms ++
                 " at PC " ++ show (bsLoc bs) ++ "."
    runDefSimulator cb sbe $ do
      esd <- initializeVerification jsc ms bs cl
      res <- mkSpecVC jsc vp esd
      when (verb >= 5) $ liftIO $ do
        putStrLn "Verifying the following:"
        mapM_ (print . ppPathVC) res
      let prover script vs g = do
            glam <- bindAllExts jsc g
            let bsc = biSharedContext bic
            glam' <- scNegate bsc =<< scImport bsc glam
            when (extraChecks opts) $ do
              when (verb >= 2) $ putStrLn "Type checking goal..."
              tcr <- scTypeCheck bsc glam'
              case tcr of
                Left err -> do
                  putStr $ unlines $
                    "Ill-typed goal constructed." : prettyTCError err
                Right _ -> when (verb >= 2) $ putStrLn "Done."
            when (verb >= 6) $ putStrLn $ "Trying to prove: " ++ show glam'
            (r, _) <- runStateT script (ProofGoal (vsVCName vs) glam')
            case r of
              SS.Unsat -> when (verb >= 3) $ putStrLn "Valid."
              SS.Sat val -> showCexResults jsc ms vs [("x", val)] -- TODO: replace x with something
              SS.SatMulti vals -> showCexResults jsc ms vs vals
      case jsTactic setupRes of
        Skip -> liftIO $ putStrLn $
          "WARNING: skipping verification of " ++ show (specName ms)
        RunVerify script ->
          liftIO $ runValidation (prover script) vp jsc esd res
  endTime <- getCurrentTime
  putStrLn $ "Successfully verified " ++ specName ms ++ overrideText ++
             " (" ++ showDuration (diffUTCTime endTime startTime) ++ ")"
  return ms

showCexResults :: SharedContext JSSCtx
               -> JavaMethodSpecIR
               -> VerifyState
               -> [(String, FiniteValue)]
               -> IO ()
showCexResults sc ms vs vals = do
  putStrLn $ "When verifying " ++ specName ms ++ ":"
  putStrLn $ "Proof of " ++ vsVCName vs ++ " failed."
  putStrLn $ "Counterexample: "
  mapM_ (\(n, v) -> putStrLn ("  " ++ n ++ ": " ++ show v)) vals
  vsCounterexampleFn vs (cexEvalFn sc (map snd vals)) >>= print
  fail "Proof failed."

parseJavaExpr :: Codebase -> Class -> Method -> String
              -> IO JavaExpr
parseJavaExpr cb cls meth estr = do
  sr <- parseStaticParts parts
  case sr of
    Just e -> return e
    Nothing -> parseParts parts
  where parseParts :: [String] -> IO JavaExpr
        parseParts [] = fail "empty Java expression"
        parseParts [s] =
          case s of
            "this" | methodIsStatic meth ->
                     fail $ "Can't use 'this' in static method " ++
                            methodName meth
                   | otherwise -> return (thisJavaExpr cls)
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
                      | otherwise -> fail $
                                     "local variable index " ++ show i ++
                                     " for parameter " ++ show n ++ " doesn't exist"
                    Just lv -> return (CC.Term (Local s i (localType lv)))
                Nothing -> fail $ "bad Java expression syntax: " ++ s
            _ | hasDebugInfo meth -> do
                  let mlv = lookupLocalVariableByName meth 0 s
                  case mlv of
                    Nothing -> fail $ "local doesn't exist: " ++ s
                    Just lv -> return (CC.Term (Local s i ty))
                      where i = localIdx lv
                            ty = localType lv
              | otherwise ->
                  fail $ "variable " ++ s ++
                         " referenced by name, but no debug info available"
        parseParts (f:rest) = do
          e <- parseParts rest
          let jt = jssTypeOfJavaExpr e
              pos = fixPos -- TODO
          fid <- findField cb pos jt f
          return (CC.Term (InstanceField e fid))
        parseStaticParts (fname:rest) = do
          let cname = intercalate "/" (reverse rest)
          mc <- tryLookupClass cb cname
          case mc of
            Just c ->
              case filter ((== fname) . fieldName) (classFields c) of
                [f] -> return (Just
                               (CC.Term
                                (StaticField
                                 (FieldId cname fname (fieldType f)))))
                _ -> return Nothing
            Nothing -> return Nothing
        parseStaticParts _ = return Nothing
        parts = reverse (splitOn "." estr)

javaBool :: JavaType
javaBool = JavaBoolean

javaByte :: JavaType
javaByte = JavaByte

javaChar :: JavaType
javaChar = JavaChar

javaShort :: JavaType
javaShort = JavaShort

javaInt :: JavaType
javaInt = JavaInt

javaLong :: JavaType
javaLong = JavaLong

javaFloat :: JavaType
javaFloat = JavaFloat

javaDouble :: JavaType
javaDouble = JavaDouble

javaArray :: Int -> JavaType -> JavaType
javaArray n t = JavaArray n t

javaClass :: String -> JavaType
javaClass name = JavaClass name

exportJSSType :: JavaType -> Type
exportJSSType jty =
  case jty of
    JavaBoolean     -> BooleanType
    JavaByte        -> ByteType
    JavaChar        -> CharType
    JavaShort       -> ShortType
    JavaInt         -> IntType
    JavaLong        -> LongType
    JavaFloat       -> error "exportJSSType: Can't translate float type"
    JavaDouble      -> error "exportJSSType: Can't translate double type"
    JavaArray _ ety -> ArrayType (exportJSSType ety)
    JavaClass name  -> ClassType (dotsToSlashes name)

exportJavaType :: Codebase -> JavaType -> IO JavaActualType
exportJavaType cb jty =
  case jty of
    JavaBoolean     -> return $ PrimitiveType BooleanType
    JavaByte        -> return $ PrimitiveType ByteType
    JavaChar        -> return $ PrimitiveType CharType
    JavaShort       -> return $ PrimitiveType ShortType
    JavaInt         -> return $ PrimitiveType IntType
    JavaLong        -> return $ PrimitiveType LongType
    JavaFloat       -> error "exportJavaType: Can't translate float type"
    JavaDouble      -> error "exportJavaType: Can't translate double type"
    JavaArray n t   -> return $ ArrayInstance (fromIntegral n) (exportJSSType t)
    JavaClass name  -> do cls <- lookupClass cb fixPos name
                          return (ClassInstance cls)

checkCompatibleExpr :: SharedContext s -> String -> JavaExpr -> SharedTerm s
                    -> JavaSetup ()
checkCompatibleExpr sc msg expr t = do
  jsState <- get
  let atm = specActualTypeMap (jsSpec jsState)
  liftIO $ case Map.lookup expr atm of
    Nothing -> fail $ "No type found for Java expression: " ++ show expr ++
                      " (" ++ msg ++ ")"
    Just at -> liftIO $ checkCompatibleType sc msg at t

checkCompatibleType :: SharedContext s
                    -> String
                    -> JavaActualType
                    -> SharedTerm s
                    -> IO ()
checkCompatibleType sc msg at t = do
  mlt <- logicTypeOfActual sc at
  case mlt of
    Nothing ->
      fail $ "Type is not translatable: " ++ show at ++ " (" ++ msg ++ ")"
    Just lt -> do
      ty <- scTypeCheckError sc t
      lt' <- scWhnf sc lt
      ty' <- scWhnf sc ty
      unless (lt' == ty') $ fail $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ show lt'
                , "  Got: " ++ show ty'
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
  let jty = jssTypeOfJavaExpr expr
      jty' = exportJSSType ty
  liftIO $ checkEqualTypes jty jty' name
  aty <- liftIO $ exportJavaType cb ty
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

javaClassVar :: BuiltinContext -> Options -> String -> JavaType
             -> JavaSetup ()
javaClassVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  modify $ \st -> st { jsSpec = specAddVarDecl name expr aty (jsSpec st) }

javaVar :: BuiltinContext -> Options -> String -> JavaType
        -> JavaSetup (TypedTerm SAWCtx)
javaVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  modify $ \st -> st { jsSpec = specAddVarDecl name expr aty (jsSpec st) }
  let sc = biSharedContext bic
  Just lty <- liftIO $ logicTypeOfActual sc aty
  liftIO $ scJavaValue sc lty name >>= mkTypedTerm sc

javaMayAlias :: BuiltinContext -> Options -> [String]
             -> JavaSetup ()
javaMayAlias bic _ exprs = do
  jsState <- get
  let cb = biJavaCodebase bic
      ms = jsSpec jsState
      cls = specThisClass ms
      meth = specMethod ms
  exprList <- liftIO $ mapM (parseJavaExpr cb cls meth) exprs
  -- TODO: check that all expressions exist and have the same type
  modify $ \st -> st { jsSpec = specAddAliasSet exprList (jsSpec st) }

javaAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> JavaSetup ()
javaAssert bic _ v = do
  --liftIO $ print "javaAssert"
  ms <- gets jsSpec
  let m = specJavaExprNames ms
      atm = specActualTypeMap ms
  let sc = biSharedContext bic
  ty <- liftIO $ scTypeCheckError sc v
  ty' <- liftIO $ scWhnf sc ty
  unless (asBoolType ty' == Just ()) $
    fail $ "java_assert passed expression of non-boolean type: " ++ show ty'
  me <- liftIO $ mkMixedExpr m atm sc v
  case me of
    LE le ->
      modify $ \st ->
        st { jsSpec =
               specAddBehaviorCommand (AssertPred fixPos le) (jsSpec st) }
    JE je -> fail $ "Used java_assert with Java expression: " ++ show je

getJavaExpr :: Monad m =>
               JavaMethodSpecIR -> String
            -> m (JavaExpr, Type)
getJavaExpr ms name = do
  case Map.lookup name (specJavaExprNames ms) of
    Just expr -> return (expr, jssTypeOfJavaExpr expr)
    Nothing -> fail $ "Java name " ++ name ++ " has not been declared."

javaAssertEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
           -> JavaSetup ()
javaAssertEq bic _ name t = do
  --liftIO $ print "javaAssertEq"
  ms <- gets jsSpec
  let m = specJavaExprNames ms
      atm = specActualTypeMap ms
  let sc = biSharedContext bic
  (expr, _) <- liftIO $ getJavaExpr ms name
  checkCompatibleExpr sc "java_assert_eq" expr t
  me <- liftIO $ mkMixedExpr m atm sc t
  modify $ \st ->
    st { jsSpec = specAddLogicAssignment fixPos expr me ms }

javaEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> JavaSetup ()
javaEnsureEq bic _ name t = do
  --liftIO $ print "javaEnsureEq"
  ms <- gets jsSpec
  (expr, ty) <- liftIO $ getJavaExpr ms name
  let m = specJavaExprNames ms
      atm = specActualTypeMap ms
  let sc = biSharedContext bic
  --liftIO $ putStrLn "Making MixedExpr"
  checkCompatibleExpr sc "java_ensure_eq" expr t
  me <- liftIO $ mkMixedExpr m atm sc t
  --liftIO $ putStrLn "Done making MixedExpr"
  let cmd = case (CC.unTerm expr, ty) of
              (_, ArrayType _) -> EnsureArray fixPos expr me
              (InstanceField r f, _) -> EnsureInstanceField fixPos r f me
              (StaticField f, _) -> EnsureStaticField fixPos f me
              _ -> error "invalid java_ensure command"
  modify $ \st -> st { jsSpec = specAddBehaviorCommand cmd ms }

javaModify :: BuiltinContext -> Options -> String
           -> JavaSetup ()
javaModify _bic _ name = do
  --liftIO $ print "javaModify"
  ms <- gets jsSpec
  (expr, _) <- liftIO $ getJavaExpr ms name
  let mty = Map.lookup expr (bsActualTypeMap (specBehaviors ms))
  let cmd = case (CC.unTerm expr, mty) of
              (_, Just ty@(ArrayInstance _ _)) -> ModifyArray expr ty
              (InstanceField r f, _) -> ModifyInstanceField r f
              (StaticField f, _) -> ModifyStaticField f
              _ -> error "invalid java_modify command"
  modify $ \st -> st { jsSpec = specAddBehaviorCommand cmd ms }

javaReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> JavaSetup ()
javaReturn bic _ t = do
  --liftIO $ print "javaReturn"
  ms <- gets jsSpec
  let m = specJavaExprNames ms
      atm = specActualTypeMap ms
      -- TODO: check that given expression is compatible with return type
      {-
      rtype = methodKeyReturnType . methodKey . specMethod $ ms
      rt = toActualType rtype
      -}
  me <- liftIO $ mkMixedExpr m atm (biSharedContext bic) t
  modify $ \st ->
    st { jsSpec = specAddBehaviorCommand (ReturnValue me) (jsSpec st) }

javaVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SatResult
                 -> JavaSetup ()
javaVerifyTactic _ _ script =
  modify $ \st -> st { jsTactic = RunVerify script }
