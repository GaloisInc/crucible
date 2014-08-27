{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.Value where

import Control.Applicative
import Control.Monad.IO.Class ( liftIO )
import Control.Monad.State ( StateT(..) )
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
import qualified Verifier.LLVM.Codebase as LSS
import SAWScript.Proof
import SAWScript.Utils

import Verifier.SAW.FiniteValue
import qualified Verifier.SAW.Prim as Prim
import qualified Verifier.SAW.Recognizer as R
import Verifier.SAW.Rewriter ( Simpset )
import Verifier.SAW.SharedTerm

import qualified Verifier.SAW.Evaluator as SC
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
  | VLambda (Value s -> IO (Value s))
  | VTLambda (SS.Type -> IO (Value s))
  | VTerm (Maybe C.Schema) (SharedTerm s) -- TODO: remove the Maybe
  | VCtorApp String [Value s]
  | VIO (IO (Value s))
  | VProofScript (ProofScript s (Value s))
  | VSimpset (Simpset (SharedTerm s))
  | VTheorem (Theorem s)
  | VJavaSetup (JavaSetup (Value s))
  | VLLVMSetup (LLVMSetup (Value s))
  | VJavaMethodSpec JIR.JavaMethodSpecIR
  | VLLVMMethodSpec LIR.LLVMMethodSpecIR
  | VJavaType JSS.Type
  | VLLVMType LSS.MemType
  | VJavaClass JSS.Class
  | VLLVMModule LLVMModule
  | VSatResult SatResult
  | VProofResult ProofResult
  | VUninterp (Uninterp s)
  -- | VAIG (BitEngine Lit) (V.Vector Lit) (V.Vector Lit)

data LLVMModule =
  LLVMModule
  { modName :: String
  , modMod :: L.Module
  }

data ProofResult
  = Valid
  | Invalid FiniteValue
  | InvalidMulti [(String, FiniteValue)]
    deriving (Show)

data SatResult
  = Unsat
  | Sat FiniteValue
  | SatMulti [(String, FiniteValue)]
    deriving (Show)

flipSatResult :: SatResult -> ProofResult
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

    VLambda {} -> showString "<<function>>"
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
    VJavaType {} -> showString "<<Java type>>"
    VLLVMType t -> showString (show (LSS.ppMemType t))
    VLLVMModule {} -> showString "<<LLVM Module>>"
    VJavaClass {} -> showString "<<Java Class>>"
    VProofResult Valid -> showString "Valid"
    VProofResult (Invalid t) -> showString "Invalid: " . shows t
    VProofResult (InvalidMulti ts) -> showString "Invalid: " . shows ts
    VSatResult Unsat -> showString "Unsat"
    VSatResult (Sat t) -> showString "Sat: " . shows t
    VSatResult (SatMulti ts) -> showString "Sat: " . shows ts
    VUninterp u -> showString "Uninterp: " . shows u

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

evaluate :: SharedContext s -> SharedTerm s -> SC.Value
evaluate sc t = SC.evalSharedTerm eval t
  where eval = SC.evalGlobal (scModule sc) SC.preludePrims
-- FIXME: is evalGlobal always appropriate? Or should we
-- parameterize on a meaning function for globals?

applyValue :: SharedContext s -> Value s -> Value s -> IO (Value s)
applyValue _ (VLambda f) x = f x
-- applyValue sc (VAIG be ins outs) x = undefined
applyValue _ _ _ = fail "applyValue"

tapplyValue :: Value s -> SS.Type -> IO (Value s)
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

-- The ProofScript in RunVerify is in the SAWScript context, and
-- should stay there.
data ValidationPlan
  = Skip
  | RunVerify (ProofScript SAWCtx SatResult)

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

class FromValue s a where
    fromValue :: Value s -> a
    funToValue :: (a -> Value s) -> Value s
    funToValue f = VLambda (\v -> return (f (fromValue v)))

instance (FromValue s a, IsValue s b) => IsValue s (a -> b) where
    toValue f = funToValue (\x -> toValue (f x))

instance FromValue s (Value s) where
    fromValue x = x

instance IsValue s (Value s) where
    toValue x = x

instance IsValue s () where
    toValue _ = VTuple []

instance FromValue s () where
    fromValue _ = ()

instance (IsValue s a, IsValue s b) => IsValue s (a, b) where
    toValue (x, y) = VTuple [toValue x, toValue y]

instance (FromValue s a, FromValue s b) => FromValue s (a, b) where
    fromValue (VTuple [x, y]) = (fromValue x, fromValue y)
    fromValue _ = error "fromValue (,)"

instance IsValue s a => IsValue s [a] where
    toValue xs = VArray (map toValue xs)

instance FromValue s a => FromValue s [a] where
    fromValue (VArray xs) = map fromValue xs
    fromValue _ = error "fromValue []"

instance IsValue s a => IsValue s (IO a) where
    toValue io = VIO (fmap toValue io)

instance FromValue s a => FromValue s (IO a) where
    fromValue (VIO io) = fmap fromValue io
    fromValue _ = error "fromValue IO"

instance IsValue s a => IsValue s (StateT (ProofGoal s) IO a) where
    toValue m = VProofScript (fmap toValue m)

instance FromValue s a => FromValue s (StateT (ProofGoal s) IO a) where
    fromValue (VProofScript m) = fmap fromValue m
    fromValue _ = error "fromValue ProofScript"

instance IsValue s a => IsValue s (StateT JavaSetupState IO a) where
    toValue m = VJavaSetup (fmap toValue m)

instance FromValue s a => FromValue s (StateT JavaSetupState IO a) where
    fromValue (VJavaSetup m) = fmap fromValue m
    fromValue _ = error "fromValue JavaSetup"

instance IsValue s a => IsValue s (StateT LLVMSetupState IO a) where
    toValue m = VLLVMSetup (fmap toValue m)

instance FromValue s a => FromValue s (StateT LLVMSetupState IO a) where
    fromValue (VLLVMSetup m) = fmap fromValue m
    fromValue _ = error "fromValue LLVMSetup"

instance IsValue s (TypedTerm s) where
    toValue (TypedTerm s t) = VTerm (Just s) t

instance FromValue s (TypedTerm s) where
    fromValue (VTerm (Just s) t) = TypedTerm s t
    fromValue _ = error "fromValue TypedTerm"

instance IsValue s (SharedTerm s) where
    toValue t = VTerm Nothing t

instance FromValue s (SharedTerm s) where
    fromValue (VTerm _ t) = t
    fromValue _ = error "fromValue SharedTerm"

instance FromValue s SS.Type where
    fromValue _ = error "fromValue Type"
    funToValue f = VTLambda (\t -> return (f t))

instance IsValue s String where
    toValue n = VString n

instance FromValue s String where
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

instance IsValue s Integer where
    toValue n = VInteger n

instance FromValue s Integer where
    fromValue (VInteger n) = n
    fromValue _ = error "fromValue Integer"

instance IsValue s Int where
    toValue n = VInteger (toInteger n)

instance FromValue s Int where
    fromValue (VInteger n)
      | toInteger (minBound :: Int) <= n &&
        toInteger (maxBound :: Int) >= n = fromIntegral n
    fromValue _ = error "fromValue Int"

instance IsValue s Prim.BitVector where
    toValue (Prim.BV w x) = VWord w x

instance FromValue s Prim.BitVector where
    fromValue (VWord w x) = Prim.BV w x
    fromValue _ = error "fromValue BitVector"

instance IsValue s Bool where
    toValue b = VBool b

instance FromValue s Bool where
    fromValue (VBool b) = b
    fromValue _ = error "fromValue Bool"

instance IsValue s (Simpset (SharedTerm s)) where
    toValue ss = VSimpset ss

instance FromValue s (Simpset (SharedTerm s)) where
    fromValue (VSimpset ss) = ss
    fromValue _ = error "fromValue Simpset"

instance IsValue s (Theorem s) where
    toValue t = VTheorem t

instance FromValue s (Theorem s) where
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

instance IsValue SAWCtx JIR.JavaMethodSpecIR where
    toValue ms = VJavaMethodSpec ms

instance FromValue SAWCtx JIR.JavaMethodSpecIR where
    fromValue (VJavaMethodSpec ms) = ms
    fromValue _ = error "fromValue JavaMethodSpec"

instance IsValue SAWCtx LIR.LLVMMethodSpecIR where
    toValue ms = VLLVMMethodSpec ms

instance FromValue SAWCtx LIR.LLVMMethodSpecIR where
    fromValue (VLLVMMethodSpec ms) = ms
    fromValue _ = error "fromValue LLVMMethodSpec"

instance IsValue SAWCtx JSS.Type where
    toValue t = VJavaType t

instance FromValue SAWCtx JSS.Type where
    fromValue (VJavaType t) = t
    fromValue _ = error "fromValue JavaType"

instance IsValue SAWCtx LSS.MemType where
    toValue t = VLLVMType t

instance FromValue SAWCtx LSS.MemType where
    fromValue (VLLVMType t) = t
    fromValue _ = error "fromValue LLVMType"

instance IsValue s (Uninterp s) where
    toValue me = VUninterp me

instance FromValue s (Uninterp s) where
    fromValue (VUninterp me) = me
    fromValue _ = error "fromValue Uninterp"

instance IsValue s JSS.Class where
    toValue c = VJavaClass c

instance FromValue s JSS.Class where
    fromValue (VJavaClass c) = c
    fromValue _ = error "fromValue JavaClass"

instance IsValue s LLVMModule where
    toValue m = VLLVMModule m

instance FromValue s LLVMModule where
    fromValue (VLLVMModule m) = m
    fromValue _ = error "fromValue LLVMModule"

instance IsValue s ProofResult where
   toValue r = VProofResult r

instance FromValue s ProofResult where
   fromValue (VProofResult r) = r
   fromValue v = error $ "fromValue ProofResult: " ++ show v

instance IsValue s SatResult where
   toValue r = VSatResult r

instance FromValue s SatResult where
   fromValue (VSatResult r) = r
   fromValue _ = error "fromValue SatResult"
