{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
module SAWScript.Builtins where

import Control.Applicative
import qualified Control.Exception as CE
import Control.Monad.State
import Data.Bits
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Typeable
import Data.Vector ( Vector )
import qualified Data.Vector as V
import qualified Data.Vector.Storable as SV
import Text.PrettyPrint.HughesPJ

import Data.ABC.Internal.GIA

import qualified Text.LLVM as LLVM
import qualified Verifier.LLVM.AST as L
import qualified Verifier.LLVM.Backend as L
import qualified Verifier.LLVM.Codebase as L
import qualified Verifier.LLVM.SAWBackend as L
--import qualified Verifier.LLVM.BitBlastBackend as BB
import qualified Verifier.LLVM.Simulator as L

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Simulator as JSS
import qualified Verifier.Java.WordBackend as JSS

import Verifier.SAW.BitBlast
import Verifier.SAW.Evaluator
import Verifier.SAW.ParserUtils ( readModuleFromFile )
import Verifier.SAW.Prelude
import qualified Verifier.SAW.SBVParser as SBV
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import qualified Verifier.SAW.Export.SMT.Version1 as SMT1
import qualified Verifier.SAW.Export.SMT.Version2 as SMT2

import qualified Verinf.Symbolic as BE
import Verinf.Utils.LogMonad

runTest :: IO ()
runTest =
    do sawScriptModule <- readModuleFromFile [preludeModule] "examples/prelude.sawcore"
       (sc :: SharedContext s) <- mkSharedContext sawScriptModule
       let global = evalGlobal sawScriptModule (allPrims global)
       let t = Term (FTermF (GlobalDef "SAWScriptPrelude.test"))
       runSC (fromValue (evalTerm global [] t :: Value s)) sc

sawScriptPrims :: forall s. (Ident -> Value s) -> Map Ident (Value s)
sawScriptPrims global = Map.fromList
  -- Key SAWScript functions
  [ ("SAWScriptPrelude.topBind", toValue
      (topBind :: () -> () -> SC s (Value s) -> (Value s -> SC s (Value s)) -> SC s (Value s)))
  , ("SAWScriptPrelude.topReturn", toValue
      (topReturn :: () -> Value s -> SC s (Value s)))
  , ("SAWScriptPrelude.readSBV", toValue
      (readSBV :: FilePath -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.readAIG", toValue
      (readAIG :: FilePath -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.writeAIG", toValue
      (writeAIG :: FilePath -> SharedTerm s -> SC s ()))
  , ("SAWScriptPrelude.writeSMTLib1", toValue
      (writeSMTLib1 :: FilePath -> SharedTerm s -> SC s ()))
  , ("SAWScriptPrelude.writeSMTLib2", toValue
      (writeSMTLib2 :: FilePath -> SharedTerm s -> SC s ()))
  -- Term building
  , ("SAWScriptPrelude.termGlobal", toValue
      (termGlobal :: String -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termTrue", toValue (termTrue :: SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termFalse", toValue (termFalse :: SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termNat", toValue
      (termNat :: Integer -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termVec", toValue
      (termVec :: Integer -> SharedTerm s -> Vector (SharedTerm s) -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termTuple", toValue
      (termTuple :: Integer -> Vector (SharedTerm s) -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termRecord", toValue
      (termRecord :: Integer -> Vector (String, SharedTerm s) -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termSelect", toValue
      (termSelect :: SharedTerm s -> String -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termLocalVar", toValue
      (termLocalVar :: Integer -> SharedTerm s -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termGlobal", toValue
      (termGlobal :: String -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termLambda", toValue
      (termLambda :: String -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)))
  , ("SAWScriptPrelude.termApp", toValue
      (termApp :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)))
  -- Misc stuff
  , ("SAWScriptPrelude.print", toValue
      (myPrint :: () -> Value s -> SC s ()))
  , ("SAWScriptPrelude.bvNatIdent", toValue ("Prelude.bvNat" :: String))
  , ("SAWScript.predNat", toValue (pred :: Integer -> Integer))
  , ("SAWScript.isZeroNat", toValue ((== 0) :: Integer -> Bool))
  , ("SAWScriptPrelude.p384_safe_product_path", toValue p384_safe_product_path)
  , ("SAWScriptPrelude.evaluate", toValue (evaluate global :: () -> SharedTerm s -> Value s))
  , ("Prelude.append", toValue
      (myAppend :: Int -> Int -> () -> Value s -> Value s -> Value s))
  ]

allPrims :: (Ident -> Value s) -> Map Ident (Value s)
allPrims global = Map.union preludePrims (sawScriptPrims global)

--topReturn :: (a :: sort 0) -> a -> TopLevel a;
topReturn :: () -> Value s -> SC s (Value s)
topReturn _ = return

--topBind :: (a b :: sort 0) -> TopLevel a -> (a -> TopLevel b) -> TopLevel b;
topBind :: () -> () -> SC s (Value s) -> (Value s -> SC s (Value s)) -> SC s (Value s)
topBind _ _ = (>>=)

-- TODO: Add argument for uninterpreted-function map
readSBV :: FilePath -> SC s (SharedTerm s)
readSBV path =
    mkSC $ \sc -> do
      pgm <- SBV.loadSBV path
      SBV.parseSBVPgm sc (\_ _ -> Nothing) pgm

withBE :: (BE.BitEngine BE.Lit -> IO a) -> IO a
withBE act = do
  be <- BE.createBitEngine
  r <- act be
  BE.beFree be
  return r

-- TODO: needs AIG -> SharedTerm function
readAIG :: FilePath -> SC s (SharedTerm s)
readAIG f =
    mkSC $ \sc -> do
      n <- giaAigerRead f False False
      fail "readAIG not yet implemented"

writeAIG :: FilePath -> SharedTerm s -> SC s ()
writeAIG f t = mkSC $ \sc -> withBE $ \be -> do
  mbterm <- bitBlast be t
  case mbterm of
    Nothing -> fail "Can't bitblast."
    Just bterm -> do
      outs <- case bterm of
              BBool l -> return $ SV.singleton l
              BVector ls -> return ls
      ins <- BE.beInputLits be
      BE.beWriteAigerV be f ins outs

writeSMTLib1 :: FilePath -> SharedTerm s -> SC s ()
writeSMTLib1 f t = mkSC $ \sc -> do
  -- TODO: better benchmark name than "sawscript"?
  let ws = SMT1.qf_aufbv_WriterState sc "sawscript"
  cmd <- execStateT (SMT1.writeFormula t) ws
  writeFile f (SMT1.render cmd)

writeSMTLib2 :: FilePath -> SharedTerm s -> SC s ()
writeSMTLib2 f t = mkSC $ \sc -> do
  let ws = SMT2.qf_aufbv_WriterState sc
  cmd <- execStateT (SMT2.assert t) ws
  writeFile f (SMT2.render cmd)

proveABC :: SharedTerm s -> SC s ()
proveABC t = mkSC $ \sc -> withBE $ \be -> do
  mbterm <- bitBlast be t
  case (mbterm, BE.beCheckSat be) of
    (Just bterm, Just chk) -> do
      case bterm of
        BBool l -> do
          satRes <- chk l
          return () -- TODO: do something with satRes!
        BVector _ -> fail "Can't prove non-boolean term."
    (_, _) -> fail "Can't bitblast."

-- Implementations of SharedTerm primitives

termTrue :: SC s (SharedTerm s)
termTrue = mkSC $ \sc -> scCtorApp sc "Prelude.True" []

termFalse :: SC s (SharedTerm s)
termFalse = mkSC $ \sc -> scCtorApp sc "Prelude.False" []

termNat :: Integer -> SC s (SharedTerm s)
termNat n = mkSC $ \sc -> scNat sc n

termVec :: Integer -> SharedTerm s -> Vector (SharedTerm s) -> SC s (SharedTerm s)
termVec _ t v = mkSC $ \sc -> scVector sc t (V.toList v)

-- TODO: termGet

termTuple :: Integer -> Vector (SharedTerm s) -> SC s (SharedTerm s)
termTuple _ tv = mkSC $ \sc -> scTuple sc (V.toList tv)

termRecord :: Integer -> Vector (String, SharedTerm s) -> SC s (SharedTerm s)
termRecord _ v = mkSC $ \sc -> scMkRecord sc (Map.fromList (V.toList v))

termSelect :: SharedTerm s -> String -> SC s (SharedTerm s)
termSelect t s = mkSC $ \sc -> scRecordSelect sc t s

termLocalVar :: Integer -> SharedTerm s -> SC s (SharedTerm s)
termLocalVar n t = mkSC $ \sc -> scLocalVar sc (fromInteger n) t

termGlobal :: String -> SC s (SharedTerm s)
termGlobal name = mkSC $ \sc -> scGlobalDef sc (parseIdent name)

termLambda :: String -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
termLambda s t1 t2 = mkSC $ \sc -> scLambda sc s t1 t2

termApp :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
termApp t1 t2 = mkSC $ \sc -> scApply sc t1 t2

-- evaluate :: (a :: sort 0) -> Term -> a;
evaluate :: (Ident -> Value s) -> () -> SharedTerm s -> Value s
evaluate global _ = evalSharedTerm global

p384_safe_product_path :: String
p384_safe_product_path = "examples/p384_safe_product.sbv"
-- (x, y) -> uext(x) * uext(y)
-- ([384], [384]) -> [768]

myPrint :: () -> Value s -> SC s ()
myPrint _ v = mkSC $ const (print v)

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
myAppend :: Int -> Int -> () -> Value s -> Value s -> Value s
myAppend _ _ _ (VWord a x) (VWord b y) = VWord (a + b) (x .|. shiftL y b)
myAppend _ _ _ (VVector xv) (VVector yv) = VVector ((V.++) xv yv)
myAppend _ _ _ _ _ = error "Prelude.append: malformed arguments"

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
--
-- Note! The s and s' type variables in this signature are different.
extractLLVM :: FilePath -> String -> SC s (SharedTerm s')
extractLLVM file func = mkSC $ \sc -> do
  mdl <- L.loadModule file
  let dl = L.parseDataLayout $ LLVM.modDataLayout mdl
      mg = L.defaultMemGeom dl
      sym = L.Symbol func
  withBE $ \be -> do
    (sbe, mem) <- L.createSAWBackend be dl mg
    cb <- L.mkCodebase sbe dl mdl
    case L.lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> L.runSimulator cb sbe mem L.defaultSEH Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (L.sdArgs md)
        L.callDefine_ sym (L.sdRetType md) args
        mrv <- L.getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just rv -> return rv

freshLLVMArg :: Monad m =>
            (t, L.MemType) -> L.Simulator sbe m (L.MemType, L.SBETerm sbe)
freshLLVMArg (_, ty@(L.IntType bw)) = do
  sbe <- gets L.symBE
  tm <- L.liftSBE $ L.freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."

-- TODO: need configuration arguments for jars, classpath
extractJava :: String -> String -> SC s (SharedTerm s)
extractJava cname mname =  mkSC $ \sc -> do
  let jpaths' = undefined
      cpaths = undefined
  cb <- JSS.loadCodebase jpaths' cpaths
  cls <- lookupClass cb cname
  (_, meth) <- findMethod cb mname cls
  JSS.withFreshBackend $ \sbe -> do
    let fl  = JSS.defaultSimFlags { JSS.alwaysBitBlastBranchTerms = True }
    JSS.runSimulator cb sbe JSS.defaultSEH (Just fl) $ do
      args <- mapM (freshJavaArg sbe) (JSS.methodParameterTypes meth)
      rslt <- JSS.execStaticMethod cname (JSS.methodKey meth) args
      undefined -- TODO: need to convert to SAWCore term

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

-- ExecException {{{1

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException -- Pos          -- ^ Position
                                   Doc          -- ^ Error message
                                   String       -- ^ Resolution tip
  deriving (Show, Typeable)

instance CE.Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => {- Pos -> -} Doc -> String -> m a
throwIOExecException {- pos -} errorMsg resolution =
  liftIO $ CE.throwIO (ExecException {- pos -} errorMsg resolution)

-- | Throw exec exception in a MonadIO.
throwExecException :: {- Pos -> -} Doc -> String -> m a
throwExecException {- pos -} errorMsg resolution =
  CE.throw (ExecException {- pos -} errorMsg resolution)

ftext :: String -> Doc
ftext msg = fsep (map text $ words msg)

-- Java lookup functions {{{1

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists.
lookupClass :: JSS.Codebase -> {- Pos -> -} String -> IO JSS.Class
lookupClass cb {- pos -} nm = do
  maybeCl <- JSS.tryLookupClass cb nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ JSS.slashesToDots nm ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException {- pos -} msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: JSS.Codebase -> {- Pos -> -} String -> JSS.Class -> IO (JSS.Class, JSS.Method)
findMethod cb {- pos -} nm initClass = impl initClass
  where javaClassName = JSS.slashesToDots (JSS.className initClass)
        methodMatches m = JSS.methodName m == nm && not (JSS.methodIsAbstract m)
        impl cl =
          case filter methodMatches (JSS.classMethods cl) of
            [] -> do
              case JSS.superClass cl of
                Nothing ->
                  let msg = ftext $ "Could not find method " ++ nm
                              ++ " in class " ++ javaClassName ++ "."
                      res = "Please check that the class and method are correct."
                   in throwIOExecException {- pos -} msg res
                Just superName ->
                  impl =<< lookupClass cb {- pos -} superName
            [method] -> return (cl,method)
            _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                             ++ " is ambiguous.  SAWScript currently requires that "
                             ++ "method names are unique."
                     res = "Please rename the Java method so that it is unique."
                  in throwIOExecException {- pos -} (ftext msg) res
