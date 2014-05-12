{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.JavaBuiltins where

import Control.Applicative
import Control.Exception (bracket)
import Control.Monad.Error
import Control.Monad.State
import Data.List (sort)
import Data.List.Split
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))
import Text.Read (readMaybe)

import qualified Language.JVM.Common as JP

import Verinf.Symbolic.Lit.ABC

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Simulator as JSS
import qualified Verifier.Java.SAWBackend as JSS

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding (instantiateVarList)

import qualified SAWScript.CongruenceClosure as CC

import SAWScript.JavaExpr
import SAWScript.JavaMethodSpec
import SAWScript.JavaMethodSpecIR

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import qualified SAWScript.Value as SS

import qualified Verinf.Symbolic as BE
import Verinf.Utils.LogMonad

extractJava :: BuiltinContext -> Options -> String -> String
            -> JavaSetup ()
            -> IO (SharedTerm SAWCtx)
extractJava bic opts cname mname _setup = do
  let cname' = JP.dotsToSlashes cname
      sc = biSharedContext bic
      cb = biJavaCodebase bic
  cls <- lookupClass cb fixPos cname'
  (_, meth) <- findMethod cb fixPos mname cls
  argsRef <- newIORef []
  bracket BE.createBitEngine BE.beFree $ \be -> do
    let fl = JSS.defaultSimFlags { JSS.alwaysBitBlastBranchTerms = True }
    sbe <- JSS.sawBackend sc (Just argsRef) be
    JSS.runSimulator cb sbe JSS.defaultSEH (Just fl) $ do
      setVerbosity 0
      args <- mapM (freshJavaArg sbe) (JSS.methodParameterTypes meth)
      rslt <- JSS.execStaticMethod cname' (JSS.methodKey meth) args
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

verifyJava :: BuiltinContext -> Options -> String -> String
           -> [JavaMethodSpecIR]
           -> JavaSetup ()
           -> IO (JavaMethodSpecIR)
verifyJava bic opts cname mname overrides setup = do
  let pos = fixPos -- TODO
      cb = biJavaCodebase bic
  sc0 <- mkSharedContext JSS.javaModule
  ss <- basic_ss sc0
  let (jsc :: SharedContext JSSCtx) = sc0 -- rewritingSharedContext sc0 ss
  be <- createBitEngine
  backend <- JSS.sawBackend jsc Nothing be
  ms0 <- initMethodSpec pos cb cname mname
  let jsctx0 = JavaSetupState {
                 jsSpec = ms0
               , jsContext = jsc
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
      let isExtCns (STApp _ (FTermF (ExtCns e))) = True
          isExtCns _ = False
          initialExts =
            sort . filter isExtCns . map snd . esdInitialAssignments $ esd
      res <- mkSpecVC jsc vp esd
      when (verb >= 5) $ liftIO $ do
        putStrLn "Verifying the following:"
        mapM_ (print . ppPathVC) res
      let prover vs script g = do
            glam <- bindExts jsc initialExts g
            glam' <- scImport (biSharedContext bic) glam
            when (verb >= 6) $ putStrLn $ "Trying to prove: " ++ show glam'
            Theorem thm <- provePrim (biSharedContext bic) script glam'
            when (verb >= 5) $ putStrLn $ "Proved: " ++ show thm
      liftIO $ runValidation prover vp jsc esd res
  BE.beFree be
  let overrideText = case overrides of
                       [] -> ""
                       irs -> " (overriding " ++ show (map specName irs) ++ ")"
      specName ir = JSS.className (specMethodClass ir) ++ "." ++ JSS.methodName (specMethod ir)
  putStrLn $ "Successfully verified " ++ specName ms ++ overrideText
  return ms

parseJavaExpr :: JSS.Codebase -> JSS.Class -> JSS.Method -> String
              -> IO JavaExpr
parseJavaExpr cb cls meth = parseParts . reverse . splitOn "."
  where parseParts [] = fail "empty Java expression"
        parseParts [s] =
          case s of
            "this" -> return (thisJavaExpr cls)
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
                      | otherwise -> error $
                                     "local variable index " ++ show i ++
                                     " for parameter " ++ show n ++ " doesn't exist"
                    Just lv -> return (CC.Term (Local s i (JSS.localType lv)))
                Nothing -> fail $ "bad Java expression syntax: " ++ s
            _ -> do
              let mlv = JSS.lookupLocalVariableByName meth 0 s
              case mlv of
                Nothing -> error $ "local doesn't exist: " ++ s
                Just lv -> return (CC.Term (Local s i ty))
                  where i = JSS.localIdx lv
                        ty = JSS.localType lv
        parseParts (f:rest) = do
          e <- parseParts rest
          let jt = jssTypeOfJavaExpr e
              pos = fixPos -- TODO
          fid <- findField cb pos jt f
          return (CC.Term (InstanceField e fid))

exportJSSType :: SS.Value s -> JSS.Type
exportJSSType (SS.VCtorApp "Java.IntType" []) = JSS.IntType
exportJSSType (SS.VCtorApp "Java.LongType" []) = JSS.LongType
exportJSSType (SS.VCtorApp "Java.ArrayType" [_, ety]) =
  JSS.ArrayType (exportJSSType ety)
exportJSSType (SS.VCtorApp "Java.ClassType" [SS.VString name]) =
  JSS.ClassType (JP.dotsToSlashes name)
exportJSSType v = error $ "exportJSSType: Can't translate to Java type: " ++ show v

exportJavaType :: JSS.Codebase -> SS.Value s -> IO JavaActualType
exportJavaType _ (SS.VCtorApp "Java.IntType" []) = return $ PrimitiveType JSS.IntType
exportJavaType _ (SS.VCtorApp "Java.LongType" []) = return $ PrimitiveType JSS.LongType
exportJavaType _ (SS.VCtorApp "Java.ArrayType" [SS.VInteger n, ety]) =
  return $ ArrayInstance (fromIntegral n) (exportJSSType ety)
exportJavaType cb (SS.VCtorApp "Java.ClassType" [SS.VString name]) = do
  cls <- lookupClass cb fixPos (JP.dotsToSlashes name)
  return (ClassInstance  cls)
exportJavaType _ v = error $ "exportJavaType: Can't translate to Java type: " ++ show v

javaPure :: JavaSetup ()
javaPure = return ()

javaVar :: BuiltinContext -> Options -> String -> SS.Value SAWCtx
        -> JavaSetup (SharedTerm SAWCtx)
javaVar bic _ name t@(SS.VCtorApp _ _) = do
  jsState <- get
  let ms = jsSpec jsState
      cb = biJavaCodebase bic
      cls = specMethodClass ms
      meth = specMethod ms
  exp <- liftIO $ parseJavaExpr (biJavaCodebase bic) cls meth name
  let jty = jssTypeOfJavaExpr exp
      jty' = exportJSSType t
  aty <- liftIO $ exportJavaType cb t
  when (jty /= jty') $ fail $ show $
    hsep [ text "WARNING: Declared type"
         , text (show (JP.ppType jty')) -- TODO: change pretty-printer
         , text "doesn't match actual type"
         , text (show (JP.ppType jty)) -- TODO: change pretty-printer
         , text "for variable"
         , text name
         ]
  modify $ \st -> st { jsSpec = specAddVarDecl name exp aty (jsSpec st) }
  let sc = biSharedContext bic
  Just lty <- liftIO $ logicTypeOfActual sc aty
  liftIO $ scJavaValue sc lty name
javaVar _ _ _ _ = fail "java_var called with invalid type argument"

javaMayAlias :: BuiltinContext -> Options -> [String]
             -> JavaSetup ()
javaMayAlias bic _ exprs = do
  jsState <- get
  let cb = biJavaCodebase bic
      ms = jsSpec jsState
      cls = specMethodClass ms
      meth = specMethod ms
  exprs <- liftIO $ mapM (parseJavaExpr cb cls meth) exprs
  modify $ \st -> st { jsSpec = specAddAliasSet exprs (jsSpec st) }

javaAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> JavaSetup ()
javaAssert _ _ v =
  modify $ \st ->
    st { jsSpec = specAddBehaviorCommand (AssertPred fixPos (mkLogicExpr v)) (jsSpec st) }

getJavaExpr :: Monad m =>
               JavaMethodSpecIR -> String
            -> m (JavaExpr, JSS.Type)
getJavaExpr ms name = do
  case Map.lookup name (specJavaExprNames ms) of
    Just exp -> return (exp, jssTypeOfJavaExpr exp)
    Nothing -> fail $ "Java name " ++ name ++ " has not been declared."

javaAssertEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
           -> JavaSetup ()
javaAssertEq bic _ name t = do
  ms <- gets jsSpec
  (exp, ty) <- liftIO $ getJavaExpr ms name
  modify $ \st ->
    st { jsSpec = specAddLogicAssignment fixPos exp (mkLogicExpr t) ms }

javaEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> JavaSetup ()
javaEnsureEq bic _ name t = do
  ms <- gets jsSpec
  (exp, ty) <- liftIO $ getJavaExpr ms name
  let cmd = case (CC.unTerm exp, ty) of
              (_, JSS.ArrayType _) -> EnsureArray fixPos exp le
              (InstanceField r f, _) -> EnsureInstanceField fixPos r f (LE le)
              _ -> error "invalid java_ensure command"
      le = mkLogicExpr t
  modify $ \st -> st { jsSpec = specAddBehaviorCommand cmd ms }

javaModify :: BuiltinContext -> Options -> String
           -> JavaSetup ()
javaModify bic _ name = do
  ms <- gets jsSpec
  (exp, _) <- liftIO $ getJavaExpr ms name
  let mty = Map.lookup exp (bsActualTypeMap (specBehaviors ms))
  let cmd = case (CC.unTerm exp, mty) of
              (_, Just ty@(ArrayInstance _ _)) -> ModifyArray exp ty
              (InstanceField r f, _) -> ModifyInstanceField r f
              _ -> error "invalid java_modify command"
  modify $ \st -> st { jsSpec = specAddBehaviorCommand cmd ms }

javaReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> JavaSetup ()
javaReturn _ _ t =
  modify $ \st ->
    st { jsSpec = specAddBehaviorCommand (Return (LE (mkLogicExpr t))) (jsSpec st) }

javaVerifyTactic :: BuiltinContext -> Options -> ProofScript SAWCtx ProofResult
                 -> JavaSetup ()
javaVerifyTactic _ _ script =
  modify $ \st -> st { jsSpec = specSetVerifyTactic script (jsSpec st) }
