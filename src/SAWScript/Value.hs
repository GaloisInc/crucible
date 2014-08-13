{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.Value where

import Control.Applicative
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.State ( StateT(..) )
import Data.Bits
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Traversable ( traverse )
import qualified Data.Vector as V
import qualified Text.LLVM as L

import qualified SAWScript.AST as SS
import qualified SAWScript.JavaMethodSpecIR as JIR
import qualified SAWScript.LLVMMethodSpecIR as LIR
import qualified Verifier.Java.Codebase as JSS
import SAWScript.Proof
import SAWScript.Utils
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.Rewriter ( Simpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.SAW.Evaluator as SC
import qualified Cryptol.ModuleSystem as Cry
import qualified Cryptol.TypeCheck.AST as C

-- Values ----------------------------------------------------------------------

data Value s
  = VBool Bool
  | VString String
  | VInteger Integer
  | VWord Int Integer
  | VArray [Value s]
  | VTuple [Value s]
  | VRecord (Map SS.Name (Value s))
  | VFun (Value s -> Value s)
  | VFunTerm (SharedTerm s -> Value s)
  | VFunType (SS.Type -> Value s)
  | VLambda (Value s -> Maybe (SharedTerm s) -> IO (Value s))
  | VTLambda (SS.Type -> IO (Value s))
  | VTerm (Maybe C.Schema) (SharedTerm s)
  | VCtorApp String [Value s]
  | VIO (IO (Value s))
  | VProofScript (ProofScript s (Value s))
  | VSimpset (Simpset (SharedTerm s))
  | VTheorem (Theorem s)
  | VJavaSetup (JavaSetup (Value s))
  | VLLVMSetup (LLVMSetup (Value s))
  | VJavaMethodSpec JIR.JavaMethodSpecIR
  | VLLVMMethodSpec LIR.LLVMMethodSpecIR
  | VCryptolModuleEnv Cry.ModuleEnv
  | VJavaClass JSS.Class
  | VLLVMModule LLVMModule
  | VSatResult (SatResult s)
  | VProofResult (ProofResult s)
  -- | VAIG (BitEngine Lit) (V.Vector Lit) (V.Vector Lit)

data LLVMModule =
  LLVMModule
  { modName :: String
  , modMod :: L.Module
  }

data ProofResult s
  = Valid
  | Invalid (Value s)
  | InvalidMulti [(String, Value s)]
    deriving (Show)

data SatResult s
  = Unsat
  | Sat (Value s)
  | SatMulti [(String, Value s)]
    deriving (Show)

flipSatResult :: SatResult s -> ProofResult s
flipSatResult Unsat = Valid
flipSatResult (Sat t) = Invalid t
flipSatResult (SatMulti t) = InvalidMulti t

isVUnit :: Value s -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

bitsToWord :: [Bool] -> Value s
bitsToWord bs = VWord (length bs) (SC.bvToInteger (V.fromList bs))

arrayToWord :: [Value s] -> Value s
arrayToWord = bitsToWord . map fromValue

isBool :: Value s -> Bool
isBool (VBool _) = True
isBool _ = False

data PPOpts = PPOpts
  { ppOptsAnnotate :: Bool
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts False

commaSep :: [ShowS] -> ShowS
commaSep ss = foldr (.) id (intersperse (showString ",") ss)

showBrackets :: ShowS -> ShowS
showBrackets s = showString "[" . s . showString "]"

showBraces :: ShowS -> ShowS
showBraces s = showString "{" . s . showString "}"

showsPrecValue :: PPOpts -> Int -> Maybe SS.Type -> Value s -> ShowS
showsPrecValue opts p mty v =
  case v of
    VBool True -> showString "True"
    VBool False -> showString "False"
    VString s -> shows s
    VInteger n -> shows n
    VWord w x
      | ppOptsAnnotate opts -> showParen (p > 9) (shows x . showString ":[" . shows w . showString "]")
      | otherwise           -> shows x
    VArray vs
      | all isBool vs -> shows (arrayToWord vs)
      | otherwise -> showBrackets $ commaSep $ map (showsPrecValue opts 0 mty') vs
                       where mty' = case mty of
                                      Just (SS.TyCon SS.ArrayCon [_, ty']) -> Just ty'
                                      _ -> Nothing
    VTuple vs -> case mty of
                   Just (SS.TyRecord tm) | M.size tm == length vs
                     -> showsPrecValue opts p mty (VRecord (M.fromList (zip (M.keys tm) vs)))
                   Just (SS.TyCon (SS.TupleCon _) ts) | length ts == length vs
                     -> showParen True $ commaSep $ zipWith (showsPrecValue opts 0) (map Just ts) vs
                   _ -> showParen True $ commaSep $ map (showsPrecValue opts 0 Nothing) vs
    VRecord m -> showBraces $ commaSep $ zipWith showFld mtys (M.toList m)
                   where
                     showFld mty' (n, fv) =
                       showString n . showString "=" . showsPrecValue opts 0 mty' fv
                     mtys =
                       case mty of
                         Just (SS.TyRecord tm) | M.keys m == M.keys tm
                           -> map Just (M.elems tm)
                         _ -> replicate (M.size m) Nothing

    VFun {} -> showString "<<fun>>"
    VFunTerm {} -> showString "<<fun-term>>"
    VFunType {} -> showString "<<fun-type>>"
    VLambda {} -> showString "<<lambda>>"
    VTLambda {} -> showString "<<polymorphic function>>"
    VTerm _ t -> showsPrec p t
    VCtorApp s vs -> showString s . showString " " . (foldr (.) id (map shows vs))
    VIO {} -> showString "<<IO>>"
    VSimpset {} -> showString "<<simpset>>"
    VProofScript {} -> showString "<<proof script>>"
    VTheorem (Theorem t) -> showString "Theorem " . showParen True (showString (scPrettyTerm t))
    VJavaSetup {} -> showString "<<Java Setup>>"
    VLLVMSetup {} -> showString "<<LLVM Setup>>"
    VJavaMethodSpec {} -> showString "<<Java MethodSpec>>"
    VLLVMMethodSpec {} -> showString "<<LLVM MethodSpec>>"
    VCryptolModuleEnv {} -> showString "<<Cryptol ModuleEnv>>"
    VLLVMModule {} -> showString "<<LLVM Module>>"
    VJavaClass {} -> showString "<<Java Class>>"
    VProofResult Valid -> showString "Valid"
    VProofResult (Invalid t) -> showString "Invalid: " . shows t
    VProofResult (InvalidMulti ts) -> showString "Invalid: " . shows ts
    VSatResult Unsat -> showString "Unsat"
    VSatResult (Sat t) -> showString "Sat: " . shows t
    VSatResult (SatMulti ts) -> showString "Sat: " . shows ts

instance Show (Value s) where
    showsPrec p v = showsPrecValue defaultPPOpts p Nothing v

indexValue :: Value s -> Value s -> Value s
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value s -> String -> Value s
lookupValue (VRecord vm) name =
    case M.lookup name vm of
      Nothing -> error $ "no such record field: " ++ name
      Just x -> x
lookupValue _ _ = error "lookupValue"

tupleLookupValue :: Value s -> Integer -> Value s
tupleLookupValue (VTuple vs) i
  | fromIntegral i <= length vs = vs !! (fromIntegral i - 1)
  | otherwise = error $ "no such tuple index: " ++ show i
tupleLookupValue _ _ = error "tupleLookupValue"

evaluate :: SharedContext s -> SharedTerm s -> Value s
evaluate sc t = importValue (SC.evalSharedTerm eval t)
  where eval = SC.evalGlobal (scModule sc) SC.preludePrims
-- FIXME: is evalGlobal always appropriate? Or should we
-- parameterize on a meaning function for globals?

applyValue :: SharedContext s -> Value s -> Value s -> IO (Value s)
applyValue sc (VFun f) (VTerm _ t) = return (f (evaluate sc t))
applyValue _  (VFun f) x = return (f x)
applyValue _  (VFunTerm f) (VTerm _ t) = return (f t)
applyValue sc (VLambda f) (VTerm _ t) = f (evaluate sc t) (Just t)
applyValue _  (VLambda f) x = f x Nothing
applyValue sc (VTerm _ t) x = applyValue sc (evaluate sc t) x
-- applyValue sc (VAIG be ins outs) x = undefined
applyValue _ _ _ = fail "applyValue"

tapplyValue :: Value s -> SS.Type -> IO (Value s)
tapplyValue (VFunType f) t = return (f t)
tapplyValue (VTLambda f) t = f t
-- tapplyValue (VAIG be ins outs) t = undefined
tapplyValue v _ = return v

thenValue :: Value s -> Value s -> Value s
thenValue (VIO m1) (VIO m2) = VIO (m1 >> m2)
thenValue (VProofScript m1) (VProofScript m2) = VProofScript (m1 >> m2)
thenValue (VJavaSetup m1) (VJavaSetup m2) = VJavaSetup (m1 >> m2)
thenValue (VLLVMSetup m1) (VLLVMSetup m2) = VLLVMSetup (m1 >> m2)
thenValue _ _ = error "thenValue"

bindValue :: SharedContext s -> Value s -> Value s -> Value s
bindValue sc (VIO m1) v2 =
  VIO $ do
    v1 <- m1
    VIO m3 <- applyValue sc v2 v1
    m3
bindValue sc (VProofScript m1) v2 =
  VProofScript $ do
    v1 <- m1
    VProofScript m3 <- liftIO $ applyValue sc v2 v1
    m3
bindValue sc (VJavaSetup m1) v2 =
  VJavaSetup $ do
    v1 <- m1
    VJavaSetup m3 <- liftIO $ applyValue sc v2 v1
    m3
bindValue sc (VLLVMSetup m1) v2 =
  VLLVMSetup $ do
    v1 <- m1
    VLLVMSetup m3 <- liftIO $ applyValue sc v2 v1
    m3
bindValue _ _ _ = error "bindValue"

-- TODO: this should take the SAWScript type as a parameter, and
-- reconstruct tuples and records as appropriate.
importValue :: SC.Value -> Value s
importValue val =
    case val of
      SC.VFun f -> VFun (importValue . f . exportValue)
      SC.VTrue -> VBool True
      SC.VFalse -> VBool False
      SC.VNat n -> VInteger n
      SC.VWord w x -> VWord w x
      SC.VString s -> VString s
      SC.VTuple (V.toList -> [x, y]) -> vCons (importValue x) (importValue y)
      SC.VTuple (V.toList -> []) -> VTuple []
      SC.VTuple vs -> VTuple (V.toList (fmap importValue vs))
      SC.VRecord m -> VRecord (fmap importValue m)
      SC.VCtorApp ident args
        | ident == parseIdent "Prelude.False" -> VBool False
        | ident == parseIdent "Prelude.True" -> VBool True
        | otherwise ->
          VCtorApp (show ident) (V.toList (fmap importValue args))
      SC.VVector vs -> VArray (V.toList (fmap importValue vs))
      SC.VFloat {} -> error "VFloat unsupported"
      SC.VDouble {} -> error "VDouble unsupported"
      SC.VType -> error "VType unsupported"
  where
    vCons v1 (VTuple vs) = VTuple (v1 : vs)
    vCons v1 v2 = VTuple [v1, v2]

exportValue :: Value s -> SC.Value
exportValue val =
    case val of
      VBool b -> if b then SC.VTrue else SC.VFalse
      VString s -> SC.VString s
      VInteger n -> SC.VNat n
      VWord w x -> SC.VWord w x
      VArray vs -> SC.VVector (fmap exportValue (V.fromList vs))
      VTuple vs -> exportVTuple (map exportValue vs)
      VRecord vm -> exportVTuple (map exportValue (M.elems vm))
      VFun f -> SC.VFun (exportValue . f . importValue)
      VCtorApp s vs -> SC.VCtorApp (parseIdent s) (fmap exportValue (V.fromList vs))
      VFunTerm {} -> error "exportValue VFunTerm"
      VFunType {} -> error "exportValue VFunType"
      VLambda {} -> error "exportValue VLambda"
      VTLambda {} -> error "exportValue VTLambda"
      VTerm {} -> error "VTerm unsupported"
      VIO {} -> error "VIO unsupported"
      VSimpset {} -> error "VSimpset unsupported"
      VProofScript {} -> error "VProofScript unsupported"
      VTheorem {} -> error "VTheorem unsupported"
      VJavaSetup {} -> error "VJavaSetup unsupported"
      VLLVMSetup {} -> error "VLLVMSetup unsupported"
      VJavaMethodSpec {} -> error "VJavaMethodSpec unsupported"
      VLLVMMethodSpec {} -> error "VLLVMMethodSpec unsupported"
      VCryptolModuleEnv {} -> error "CryptolModuleEnv unsupported"
      VJavaClass {} -> error "JavaClass unsupported"
      VLLVMModule {} -> error "LLVMModule unsupported"
      VProofResult {} -> error "VProofResult unsupported"
      VSatResult {} -> error "VSatResult unsupported"
      -- VAIG {} -> error "VAIG unsupported" -- TODO: could be implemented

exportVTuple :: [SC.Value] -> SC.Value
exportVTuple [] = SC.VTuple (V.fromList [])
exportVTuple (x : xs) = SC.VTuple (V.fromList [x, exportVTuple xs])

exportSharedTerm :: SharedContext s -> Value s' -> IO (SharedTerm s)
exportSharedTerm sc val =
    case val of
      VBool b -> scBool sc b
      VString s -> scString sc s
      VInteger n -> scNat sc (fromIntegral n)
      VWord w x -> do
        let v = V.generate w (\i -> fromValue (toValue (testBit x (w - 1 - i))))
        bt <- scBoolType sc
        tms <- mapM (scBool sc) (V.toList v)
        scVector sc bt tms
      VArray [] -> error "exportSharedTerm (VArray [])"
      VArray vs@(v:_) -> do
        t <- exportSharedTerm sc v
        ty <- scTypeOf sc t
        scVector sc ty =<< mapM (exportSharedTerm sc) vs
      VTuple vs -> scTuple sc =<< mapM (exportSharedTerm sc) vs
      VRecord vm -> do
        vm' <- mapM (\(n, v) -> (n,) <$> exportSharedTerm sc v) (M.toList vm)
        scRecord sc (M.fromList vm')
      VCtorApp s vs ->
        scCtorApp sc (parseIdent s) =<< mapM (exportSharedTerm sc) vs
      VFun {} -> error "exportSharedTerm VFun" -- TODO: should we handle this?
      VFunTerm {} -> error "exportSharedTerm VFunTerm"
      VFunType {} -> error "exportSharedTerm VFunType"
      VLambda {} -> error "exportSharedTerm VLambda"
      VTLambda {} -> error "exportSharedTerm VTLambda"
      VTerm {} -> error "exportSharedTerm VTerm"
      VIO {} -> error "exportSharedTerm VIO"
      VSimpset {} -> error "exportSharedTerm VSimpset"
      VProofScript {} -> error "exportSharedTerm VProofScript"
      VTheorem {} -> error "exportSharedTerm VTheorem"
      VJavaSetup {} -> error "exportSharedTerm VJavaSetup"
      VLLVMSetup {} -> error "exportSharedTerm VLLVMSetup"
      VJavaMethodSpec {} -> error "exportSharedTerm VJavaMethodSpec"
      VLLVMMethodSpec {} -> error "exportSharedTerm VLLVMMethodSpec"
      VCryptolModuleEnv {} -> error "exportSharedTerm CryptolModuleEnv"
      VJavaClass {} -> error "exportSharedTerm JavaClass"
      VLLVMModule {} -> error "exportSharedTerm LLVMModule"
      VProofResult {} -> error "exportSharedTerm VProofResult"
      VSatResult {} -> error "exportSharedTerm VSatResult"
      -- VAIG {} -> error "exportSharedTerm VAIG" -- TODO: could be implemented

-- The ProofScript in RunVerify is in the SAWScript context, and
-- should stay there.
data ValidationPlan
  = Skip
  | RunVerify (ProofScript SAWCtx (SatResult SAWCtx))

data JavaSetupState
  = JavaSetupState {
      jsSpec :: JIR.JavaMethodSpecIR
    , jsContext :: SharedContext JSSCtx
    , jsTactic :: ValidationPlan
    }

type JavaSetup a = StateT JavaSetupState IO a

data LLVMSetupState
  = LLVMSetupState {
      lsSpec :: LIR.LLVMMethodSpecIR
    , lsContext :: SharedContext LSSCtx
    , lsTactic :: ValidationPlan
    }

type LLVMSetup a = StateT LLVMSetupState IO a

data TypedTerm s = TypedTerm C.Schema (SharedTerm s)

mkTypedTerm :: SharedContext s -> SharedTerm s -> IO (TypedTerm s)
mkTypedTerm sc trm = do
  ty <- scTypeOf sc trm
  ct <- scCryptolType sc ty
  return $ TypedTerm (C.Forall [] [] ct) trm

scCryptolType :: SharedContext s -> SharedTerm s -> IO C.Type
scCryptolType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asPi -> Just (_, t1, t2))
      -> C.tFun <$> scCryptolType sc t1 <*> scCryptolType sc t2
    (R.asBoolType -> Just ())
      -> return C.tBit
    (R.isVecType return -> Just (n R.:*: tp))
      -> C.tSeq (C.tNum n) <$> scCryptolType sc tp
    (R.asTupleType -> Just ts)
      -> C.tTuple <$> traverse (scCryptolType sc) ts
    (R.asRecordType -> Just tm)
       -> do tm' <- traverse (scCryptolType sc) tm
             return $ C.tRec [ (C.Name n, ct) | (n, ct) <- M.assocs tm' ]
    _ -> fail $ "scCryptolType: unsupported type" ++ show t'

-- IsValue class ---------------------------------------------------------------

-- | Used for encoding primitive operations in the Value type.
class IsValue s a where
    toValue :: a -> Value s
    fromValue :: Value s -> a
    funToValue :: (a -> Value s) -> Value s
    funToValue f = VFun (\v -> f (fromValue v))
    funFromValue :: Value s -> (a -> Value s)
    funFromValue (VFun g) = \x -> g (toValue x)
    funFromValue _        = error "fromValue (->)"

instance IsValue s (Value s) where
    toValue x = x
    fromValue x = x

instance (IsValue s a, IsValue s b) => IsValue s (a -> b) where
    toValue f = funToValue (\x -> toValue (f x))
    fromValue v = \x -> fromValue (funFromValue v x)

instance IsValue s () where
    toValue _ = VTuple []
    fromValue _ = ()

instance (IsValue s a, IsValue s b) => IsValue s (a, b) where
    toValue (x, y) = VTuple [toValue x, toValue y]
    fromValue (VTuple [x, y]) = (fromValue x, fromValue y)
    fromValue _ = error "fromValue (,)"

instance IsValue s a => IsValue s [a] where
    toValue xs = VArray (map toValue xs)
    fromValue (VArray xs) = map fromValue xs
    fromValue _ = error "fromValue []"

instance IsValue s a => IsValue s (IO a) where
    toValue io = VIO (fmap toValue io)
    fromValue (VIO io) = fmap fromValue io
    fromValue _ = error "fromValue IO"

instance IsValue s a => IsValue s (StateT (ProofGoal s) IO a) where
    toValue m = VProofScript (fmap toValue m)
    fromValue (VProofScript m) = fmap fromValue m
    fromValue _ = error "fromValue ProofScript"

instance (IsValue s a) => IsValue s (StateT JavaSetupState IO a) where
    toValue m = VJavaSetup (fmap toValue m)
    fromValue (VJavaSetup m) = fmap fromValue m
    fromValue _ = error "fromValue JavaSetup"

instance IsValue s a => IsValue s (StateT LLVMSetupState IO a) where
    toValue m = VLLVMSetup (fmap toValue m)
    fromValue (VLLVMSetup m) = fmap fromValue m
    fromValue _ = error "fromValue LLVMSetup"

instance IsValue s (TypedTerm s) where
    toValue (TypedTerm s t) = VTerm (Just s) t
    fromValue (VTerm (Just s) t) = TypedTerm s t
    fromValue _ = error "fromValue TypedTerm"

instance IsValue s (SharedTerm s) where
    toValue t = VTerm Nothing t
    fromValue (VTerm _ t) = t
    fromValue _ = error "fromValue SharedTerm"
    funToValue f = VFunTerm f
    funFromValue (VFunTerm f) = f
    funFromValue _ = error "fromValue (->)"

instance IsValue s SS.Type where
    toValue _ = error "toValue Type"
    fromValue _ = error "fromValue Type"
    funToValue f = VFunType f
    funFromValue (VFunType f) = f
    funFromValue _ = error "fromValue (->)"

instance IsValue s String where
    toValue n = VString n
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

instance IsValue s Integer where
    toValue n = VInteger n
    fromValue (VInteger n) = n
    fromValue _ = error "fromValue Integer"

instance IsValue s Prim.BitVector where
    toValue (Prim.BV w x) = VWord w x
    fromValue (VWord w x) = Prim.BV w x
    fromValue _ = error "fromValue BitVector"

instance IsValue s Bool where
    toValue b = VBool b
    fromValue (VBool b) = b
    fromValue _ = error "fromValue Bool"

instance IsValue s (Simpset (SharedTerm s)) where
    toValue ss = VSimpset ss
    fromValue (VSimpset ss) = ss
    fromValue _ = error "fromValue Simpset"

instance IsValue s (Theorem s) where
    toValue t = VTheorem t
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

instance IsValue SAWCtx JIR.JavaMethodSpecIR where
    toValue ms = VJavaMethodSpec ms
    fromValue (VJavaMethodSpec ms) = ms
    fromValue _ = error "fromValue JavaMethodSpec"

instance IsValue SAWCtx LIR.LLVMMethodSpecIR where
    toValue ms = VLLVMMethodSpec ms
    fromValue (VLLVMMethodSpec ms) = ms
    fromValue _ = error "fromValue LLVMMethodSpec"

instance IsValue s Cry.ModuleEnv where
    toValue me = VCryptolModuleEnv me
    fromValue (VCryptolModuleEnv me) = me
    fromValue _ = error "fromValue CryptolModuleEnv"

instance IsValue s JSS.Class where
    toValue c = VJavaClass c
    fromValue (VJavaClass c) = c
    fromValue _ = error "fromValue JavaClass"

instance IsValue s LLVMModule where
    toValue m = VLLVMModule m
    fromValue (VLLVMModule m) = m
    fromValue _ = error "fromValue LLVMModule"

instance IsValue s (ProofResult s) where
   toValue r = VProofResult r
   fromValue (VProofResult r) = r
   fromValue v = error $ "fromValue ProofResult: " ++ show v

instance IsValue s (SatResult s) where
   toValue r = VSatResult r
   fromValue (VSatResult r) = r
   fromValue _ = error "fromValue SatResult"
