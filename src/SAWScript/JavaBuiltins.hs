{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.JavaBuiltins where

import Control.Applicative hiding (empty)
import Control.Monad.Error
import Control.Monad.State
import qualified Data.ABC as ABC
import Data.List (sort, intercalate)
import Data.List.Split
import Data.IORef
import Data.Maybe
import qualified Data.Map as Map
import Data.Time.Clock
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read (readMaybe)

import qualified Language.JVM.Common as JP

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Simulator as JSS
import qualified Verifier.Java.SAWBackend as JSS

import Verifier.SAW.Evaluator
import Verifier.SAW.Recognizer
import Verifier.SAW.FiniteValue
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import qualified SAWScript.CongruenceClosure as CC

import SAWScript.JavaExpr
import SAWScript.JavaMethodSpec
import SAWScript.JavaMethodSpecIR

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value as SS


loadJavaClass :: BuiltinContext -> String -> IO JSS.Class
loadJavaClass bic cname = do
  let cname' = JP.dotsToSlashes cname
      cb = biJavaCodebase bic
  lookupClass cb fixPos cname'

browseJavaClass :: JSS.Class -> IO ()
browseJavaClass = print . prettyClass

prettyClass :: JSS.Class -> Doc
prettyClass cls = vcat $
  [ empty
  , text "Class name:" <+> text (JSS.className cls) <+>
    parens (commas attrs)
  , text "Superclass:" <+> text (fromMaybe "none" (JSS.superClass cls))
  , empty
  ] ++
  (if null (JSS.classInterfaces cls)
      then []
      else [ text "Interfaces:"
           , indent 2 (vcat (map text (JSS.classInterfaces cls)))
           , empty
           ]) ++
  [ text "Fields:"
  , indent 2 (vcat (map ppField (JSS.classFields cls)))
  , empty
  , text "Methods:"
  , indent 2 (vcat (map ppMethod (JSS.classMethods cls)))
  , empty
  ]
  where attrs = concat
          [ if JSS.classIsPublic cls then [text "public"] else []
          , if JSS.classIsFinal cls then [text "final"] else []
          , if JSS.classHasSuperAttribute cls then [text "super"] else []
          , if JSS.classIsInterface cls then [text "interface"] else []
          , if JSS.classIsAbstract cls then [text "abstract"] else []
          ]

ppField :: JSS.Field -> Doc
ppField f = hsep $
  [ text (show (JSS.fieldVisibility f)) ] ++
  attrs ++
  [ text (show (JP.ppType (JSS.fieldType f))) -- TODO: Ick. Different PPs.
  , text (JSS.fieldName f)
  ]
  where attrs = concat
          [ if JSS.fieldIsStatic f then [text "static"] else []
          , if JSS.fieldIsFinal f then [text "final"] else []
          , if JSS.fieldIsVolatile f then [text "volatile"] else []
          , if JSS.fieldIsTransient f then [text "transient"] else []
          ]

ppMethod :: JSS.Method -> Doc
ppMethod m =
  hsep [ maybe (text "void") ppType ret
       , text name
       , (parens . commas . map ppType) params
       ]
  where (JSS.MethodKey name params ret) = JSS.methodKey m
        ppType = text . show . JP.ppType -- TODO: Ick.

commas :: [Doc] -> Doc
commas = sep . punctuate comma

extractJava :: BuiltinContext -> Options -> JSS.Class -> String
            -> JavaSetup ()
            -> IO (SharedTerm SAWCtx)
extractJava bic _opts cls mname _setup = do
  let sc = biSharedContext bic
      cb = biJavaCodebase bic
  (_, meth) <- findMethod cb fixPos mname cls
  argsRef <- newIORef []
  ABC.withNewGraph ABC.giaNetwork $ \be -> do
    let fl = JSS.defaultSimFlags { JSS.alwaysBitBlastBranchTerms = True }
    sbe <- JSS.sawBackend sc (Just argsRef) be
    JSS.runSimulator cb sbe JSS.defaultSEH (Just fl) $ do
      JSS.setVerbosity 0
      args <- mapM (freshJavaArg sbe) (JSS.methodParameterTypes meth)
      rslt <- JSS.execStaticMethod (JSS.className cls) (JSS.methodKey meth) args
      dt <- case rslt of
              Nothing -> fail "No return value from JSS."
              Just (JSS.IValue t) -> return t
              Just (JSS.LValue t) -> return t
              _ -> fail "Unimplemented result type from JSS."
      liftIO $ do
        argsRev <- readIORef argsRef
        bindExts sc (reverse argsRev) dt

freshJavaArg :: MonadIO m =>
                JSS.Backend sbe
             -> JSS.Type
             -> m (JSS.AtomicValue d f (JSS.SBETerm sbe) (JSS.SBETerm sbe) r)
--freshJavaArg sbe JSS.BooleanType =
freshJavaArg sbe JSS.ByteType = liftIO (JSS.IValue <$> JSS.freshByte sbe)
--freshJavaArg sbe JSS.CharType =
--freshJavaArg sbe JSS.ShortType =
freshJavaArg sbe JSS.IntType = liftIO (JSS.IValue <$> JSS.freshInt sbe)
freshJavaArg sbe JSS.LongType = liftIO (JSS.LValue <$> JSS.freshLong sbe)
freshJavaArg _ _ = fail "Only byte, int, and long arguments are supported for now."

verifyJava :: BuiltinContext -> Options -> JSS.Class -> String
           -> [JavaMethodSpecIR]
           -> JavaSetup ()
           -> IO (JavaMethodSpecIR)
verifyJava bic opts cls mname overrides setup = do
  startTime <- getCurrentTime
  let pos = fixPos -- TODO
      cb = biJavaCodebase bic
      imps = [CryptolSAW.cryptolModule]
      vjavaModule = foldr insImport JSS.javaModule imps
  sc0 <- mkSharedContext vjavaModule
  -- ss <- basic_ss sc0
  let (jsc :: SharedContext JSSCtx) = sc0 -- rewritingSharedContext sc0 ss
  ABC.SomeGraph be <- ABC.newGraph ABC.giaNetwork
  backend <- JSS.sawBackend jsc Nothing be
  ms0 <- initMethodSpec pos cb cls mname
  let jsctx0 = JavaSetupState {
                 jsSpec = ms0
               , jsContext = jsc
               , jsTactic = Skip
               }
  (_, jsctx) <- runStateT setup jsctx0
  let ms = jsSpec jsctx
  let vp = VerifyParams {
             vpCode = cb
           , vpContext = jsc
           , vpOpts = opts
           , vpSpec = ms
           , vpOver = overrides
           }
  let verb = simVerbose (vpOpts vp)
      overrideText =
        case overrides of
          [] -> ""
          irs -> " (overriding " ++ show (map renderName irs) ++ ")"
      renderName ir = JSS.className (specMethodClass ir) ++ "." ++
                      JSS.methodName (specMethod ir)
  when (verb >= 2) $ putStrLn $ "Starting verification of " ++ specName ms
  let configs = [ (bs, cl)
                | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                , cl <- bsRefEquivClasses bs
                ]
  forM_ configs $ \(bs,cl) -> do
    when (verb >= 2) $ do
      putStrLn $ "Executing " ++ specName ms ++
                 " at PC " ++ show (bsLoc bs) ++ "."
    JSS.runDefSimulator cb backend $ do
      esd <- initializeVerification jsc ms bs cl
      res <- mkSpecVC jsc vp esd
      when (verb >= 5) $ liftIO $ do
        putStrLn "Verifying the following:"
        mapM_ (print . ppPathVC) res
      let prover script vs g = do
            glam <- bindAllExts jsc g
            let bsc = biSharedContext bic
            glam' <- scNegate bsc =<< scImport bsc glam
            when (verb >= 6) $ putStrLn $ "Trying to prove: " ++ show glam'
            (r, _) <- runStateT script (ProofGoal (vsVCName vs) glam')
            case r of
              SS.Unsat -> when (verb >= 3) $ putStrLn "Valid."
              SS.Sat val -> showCexResults jsc ms vs [("x", val)] -- TODO: replace x with something
              SS.SatMulti vals -> showCexResults jsc ms vs vals
      case jsTactic jsctx of
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

parseJavaExpr :: JSS.Codebase -> JSS.Class -> JSS.Method -> String
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
            "this" | JSS.methodIsStatic meth ->
                     fail $ "Can't use 'this' in static method " ++
                            JSS.methodName meth
                   | otherwise -> return (thisJavaExpr cls)
            ('a':'r':'g':'s':'[':rest) -> do
              let num = fst (break (==']') rest)
              case readMaybe num of
                Just (n :: Int) -> do
                  let i = JSS.localIndexOfParameter meth n
                      mlv = JSS.lookupLocalVariableByIdx meth 0 i
                      paramTypes = V.fromList .
                                   JSS.methodKeyParameterTypes .
                                   JSS.methodKey $
                                   meth
                  case mlv of
                    Nothing
                      | n < V.length paramTypes ->
                        return (CC.Term (Local s i (paramTypes V.! (fromIntegral n))))
                      | otherwise -> fail $
                                     "local variable index " ++ show i ++
                                     " for parameter " ++ show n ++ " doesn't exist"
                    Just lv -> return (CC.Term (Local s i (JSS.localType lv)))
                Nothing -> fail $ "bad Java expression syntax: " ++ s
            _ | JSS.hasDebugInfo meth -> do
                  let mlv = JSS.lookupLocalVariableByName meth 0 s
                  case mlv of
                    Nothing -> fail $ "local doesn't exist: " ++ s
                    Just lv -> return (CC.Term (Local s i ty))
                      where i = JSS.localIdx lv
                            ty = JSS.localType lv
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
          mc <- JSS.tryLookupClass cb cname
          case mc of
            Just c ->
              case filter ((== fname) . JSS.fieldName) (JSS.classFields c) of
                [f] -> return (Just
                               (CC.Term
                                (StaticField
                                 (JSS.FieldId cname fname (JSS.fieldType f)))))
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

exportJSSType :: JavaType -> JSS.Type
exportJSSType jty =
  case jty of
    JavaBoolean     -> JSS.BooleanType
    JavaByte        -> JSS.ByteType
    JavaChar        -> JSS.CharType
    JavaShort       -> JSS.ShortType
    JavaInt         -> JSS.IntType
    JavaLong        -> JSS.LongType
    JavaFloat       -> error "exportJSSType: Can't translate float type"
    JavaDouble      -> error "exportJSSType: Can't translate double type"
    JavaArray _ ety -> JSS.ArrayType (exportJSSType ety)
    JavaClass name  -> JSS.ClassType (JP.dotsToSlashes name)

exportJavaType :: JSS.Codebase -> JavaType -> IO JavaActualType
exportJavaType cb jty =
  case jty of
    JavaBoolean     -> return $ PrimitiveType JSS.BooleanType
    JavaByte        -> return $ PrimitiveType JSS.ByteType
    JavaChar        -> return $ PrimitiveType JSS.CharType
    JavaShort       -> return $ PrimitiveType JSS.ShortType
    JavaInt         -> return $ PrimitiveType JSS.IntType
    JavaLong        -> return $ PrimitiveType JSS.LongType
    JavaFloat       -> error "exportJavaType: Can't translate float type"
    JavaDouble      -> error "exportJavaType: Can't translate double type"
    JavaArray n t   -> return $ ArrayInstance (fromIntegral n) (exportJSSType t)
    JavaClass name  -> do cls <- lookupClass cb fixPos name
                          return (ClassInstance cls)

checkCompatibleExpr :: SharedContext s -> JavaExpr -> SharedTerm s
                    -> JavaSetup ()
checkCompatibleExpr sc expr t = do
  jsState <- get
  let atm = specActualTypeMap (jsSpec jsState)
  liftIO $ case Map.lookup expr atm of
    Nothing -> fail $ "No type found for Java expression: " ++ show expr
    Just at -> liftIO $ checkCompatibleType sc at t

checkCompatibleType :: SharedContext s -> JavaActualType -> SharedTerm s
                     -> IO ()
checkCompatibleType sc at t = do
  mlt <- logicTypeOfActual sc at
  case mlt of
    Nothing ->
      fail $ "Type is not translatable: " ++ show at
    Just lt -> do
      ty <- scTypeCheck sc t
      lt' <- scWhnf sc lt
      ty' <- scWhnf sc ty
      -- TODO: we can't really compare types until we have a more
      -- flexible evaluator
      unless (lt' == ty') $ return () {- fail $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ show lt'
                , "  Got:" ++ show ty'
                ] -}

javaPure :: JavaSetup ()
javaPure = return ()

typeJavaExpr :: BuiltinContext -> String -> JavaType
             -> JavaSetup (JavaExpr, JavaActualType)
typeJavaExpr bic name ty = do
  jsState <- get
  let ms = jsSpec jsState
      cb = biJavaCodebase bic
      cls = specMethodClass ms
      meth = specMethod ms
  expr <- liftIO $ parseJavaExpr (biJavaCodebase bic) cls meth name
  let jty = jssTypeOfJavaExpr expr
      jty' = exportJSSType ty
  liftIO $ checkEqualTypes jty jty' name
  aty <- liftIO $ exportJavaType cb ty
  return (expr, aty)

checkEqualTypes :: JSS.Type -> JSS.Type -> String -> IO ()
checkEqualTypes declared actual name =
  when (declared /= actual) $ fail $ show $
    hsep [ text "WARNING: Declared type"
         , text (show (JP.ppType declared)) -- TODO: change pretty-printer
         , text "doesn't match actual type"
         , text (show (JP.ppType actual)) -- TODO: change pretty-printer
         , text "for variable"
         , text name
         ]

javaClassVar :: BuiltinContext -> Options -> String -> JavaType
             -> JavaSetup ()
javaClassVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  modify $ \st -> st { jsSpec = specAddVarDecl name expr aty (jsSpec st) }
javaClassVar _ _ _ _ = fail "java_class_var called with invalid type argument"

javaVar :: BuiltinContext -> Options -> String -> JavaType
        -> JavaSetup (SS.TypedTerm SAWCtx)
javaVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  modify $ \st -> st { jsSpec = specAddVarDecl name expr aty (jsSpec st) }
  let sc = biSharedContext bic
  Just lty <- liftIO $ logicTypeOfActual sc aty
  liftIO $ scJavaValue sc lty name >>= SS.mkTypedTerm sc
javaVar _ _ _ _ = fail "java_var called with invalid type argument"

javaMayAlias :: BuiltinContext -> Options -> [String]
             -> JavaSetup ()
javaMayAlias bic _ exprs = do
  jsState <- get
  let cb = biJavaCodebase bic
      ms = jsSpec jsState
      cls = specMethodClass ms
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
  ty <- liftIO $ scTypeCheck sc v
  ty' <- liftIO $ scWhnf sc ty
  unless (asBoolType ty' == Just ()) $
    fail $ "java_assert passed expression of non-boolean type: " ++ show ty'
  me <- liftIO $ mkMixedExpr m atm sc v
  case me of
    LE le ->
      modify $ \st ->
        st { jsSpec =
               specAddBehaviorCommand (AssertPred fixPos le) (jsSpec st) }
    JE je -> fail "Used java_assert with Java expression"

getJavaExpr :: Monad m =>
               JavaMethodSpecIR -> String
            -> m (JavaExpr, JSS.Type)
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
  checkCompatibleExpr sc expr t
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
  checkCompatibleExpr sc expr t
  me <- liftIO $ mkMixedExpr m atm sc t
  --liftIO $ putStrLn "Done making MixedExpr"
  let cmd = case (CC.unTerm expr, ty) of
              (_, JSS.ArrayType _) -> EnsureArray fixPos expr me
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
  let sc = biSharedContext bic
  me <- liftIO $ mkMixedExpr m atm sc t
  modify $ \st ->
    st { jsSpec = specAddBehaviorCommand (Return me) (jsSpec st) }

javaVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SatResult
                 -> JavaSetup ()
javaVerifyTactic _ _ script =
  modify $ \st -> st { jsTactic = RunVerify script }
