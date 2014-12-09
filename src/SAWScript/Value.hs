{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.Value where

import Control.Monad.IO.Class ( liftIO )
import Control.Monad.State ( StateT(..) )
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import qualified Text.LLVM as L

import qualified SAWScript.AST as SS
import qualified SAWScript.JavaMethodSpecIR as JIR
import qualified SAWScript.LLVMMethodSpecIR as LIR
import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.LLVM.Codebase as LSS
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils

import Verifier.SAW.FiniteValue
import Verifier.SAW.Rewriter ( Simpset )
import Verifier.SAW.SharedTerm

import qualified Verifier.SAW.Evaluator as SC

-- Values ----------------------------------------------------------------------

data Value
  = VBool Bool
  | VString String
  | VInteger Integer
  | VArray [Value]
  | VTuple [Value]
  | VRecord (Map SS.Name Value)
  | VLambda (Value -> IO Value)
  | VTerm (TypedTerm SAWCtx)
  | VReturn Value -- Returned value in unspecified monad
  | VBind Value Value -- Monadic bind in unspecified monad
  | VIO (IO Value)
  | VProofScript (ProofScript SAWCtx Value)
  | VSimpset (Simpset (SharedTerm SAWCtx))
  | VTheorem (Theorem SAWCtx)
  | VJavaSetup (JavaSetup Value)
  | VLLVMSetup (LLVMSetup Value)
  | VJavaMethodSpec JIR.JavaMethodSpecIR
  | VLLVMMethodSpec LIR.LLVMMethodSpecIR
  | VJavaType JavaType
  | VLLVMType LSS.MemType
  | VCryptolModule (CryptolModule SAWCtx)
  | VJavaClass JSS.Class
  | VLLVMModule LLVMModule
  | VSatResult SatResult
  | VProofResult ProofResult
  | VUninterp (Uninterp SAWCtx)
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

isVUnit :: Value -> Bool
isVUnit (VTuple []) = True
isVUnit _ = False

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

showsPrecValue :: PPOpts -> Int -> Value -> ShowS
showsPrecValue opts p v =
  case v of
    VBool True -> showString "True"
    VBool False -> showString "False"
    VString s -> shows s
    VInteger n -> shows n
    VArray vs -> showBrackets $ commaSep $ map (showsPrecValue opts 0) vs
    VTuple vs -> showParen True $ commaSep $ map (showsPrecValue opts 0) vs
    VRecord m -> showBraces $ commaSep $ map showFld (M.toList m)
                   where
                     showFld (n, fv) =
                       showString n . showString "=" . showsPrecValue opts 0 fv

    VLambda {} -> showString "<<function>>"
    VTerm t -> showsPrec p (ttTerm t)
    VReturn {} -> showString "<<monadic>>"
    VBind {} -> showString "<<monadic>>"
    VIO {} -> showString "<<IO>>"
    VSimpset {} -> showString "<<simpset>>"
    VProofScript {} -> showString "<<proof script>>"
    VTheorem (Theorem t) -> showString "Theorem " . showParen True (showString (scPrettyTerm (ttTerm t)))
    VJavaSetup {} -> showString "<<Java Setup>>"
    VLLVMSetup {} -> showString "<<LLVM Setup>>"
    VJavaMethodSpec {} -> showString "<<Java MethodSpec>>"
    VLLVMMethodSpec {} -> showString "<<LLVM MethodSpec>>"
    VJavaType {} -> showString "<<Java type>>"
    VLLVMType t -> showString (show (LSS.ppMemType t))
    VCryptolModule {} -> showString "<<Cryptol Module>>" -- TODO: print list of bindings
    VLLVMModule {} -> showString "<<LLVM Module>>"
    VJavaClass {} -> showString "<<Java Class>>"
    VProofResult Valid -> showString "Valid"
    VProofResult (Invalid t) -> showString "Invalid: " . shows t
    VProofResult (InvalidMulti ts) -> showString "Invalid: " . shows ts
    VSatResult Unsat -> showString "Unsat"
    VSatResult (Sat t) -> showString "Sat: " . shows t
    VSatResult (SatMulti ts) -> showString "Sat: " . shows ts
    VUninterp u -> showString "Uninterp: " . shows u

instance Show Value where
    showsPrec p v = showsPrecValue defaultPPOpts p v

indexValue :: Value -> Value -> Value
indexValue (VArray vs) (VInteger x)
    | i < length vs = vs !! i
    | otherwise = error "array index out of bounds"
    where i = fromInteger x
indexValue _ _ = error "indexValue"

lookupValue :: Value -> String -> Value
lookupValue (VRecord vm) name =
    case M.lookup name vm of
      Nothing -> error $ "no such record field: " ++ name
      Just x -> x
lookupValue _ _ = error "lookupValue"

tupleLookupValue :: Value -> Integer -> Value
tupleLookupValue (VTuple vs) i
  | fromIntegral i <= length vs = vs !! (fromIntegral i - 1)
  | otherwise = error $ "no such tuple index: " ++ show i
tupleLookupValue _ _ = error "tupleLookupValue"

evaluate :: SharedContext s -> SharedTerm s -> SC.Value
evaluate sc t = SC.evalSharedTerm eval t
  where eval = SC.evalGlobal (scModule sc) SC.preludePrims
-- FIXME: is evalGlobal always appropriate? Or should we
-- parameterize on a meaning function for globals?

applyValue :: Value -> Value -> IO Value
applyValue (VLambda f) x = f x
applyValue _ _ = fail "applyValue"

thenValue :: Value -> Value -> Value
thenValue v1 v2 = VBind v1 (VLambda (const (return v2)))

bindValue :: Value -> Value -> IO Value
bindValue v1 v2 = return (VBind v1 v2)

forValue :: [Value] -> Value -> IO Value
forValue [] _ = return $ VReturn (VArray [])
forValue (x : xs) f =
  do m1 <- applyValue f x
     m2 <- forValue xs f
     bindValue m1 (VLambda $ \v1 ->
       bindValue m2 (VLambda $ \v2 ->
         return $ VReturn (VArray (v1 : fromValue v2))))

-- The ProofScript in RunVerify is in the SAWScript context, and
-- should stay there.
data ValidationPlan
  = Skip
  | RunVerify (ProofScript SAWCtx SatResult)

data JavaSetupState
  = JavaSetupState {
      jsSpec :: JIR.JavaMethodSpecIR
    , jsContext :: SharedContext SAWCtx
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

-- IsValue class ---------------------------------------------------------------

-- | Used for encoding primitive operations in the Value type.
class IsValue a where
    toValue :: a -> Value

class FromValue a where
    fromValue :: Value -> a

instance (FromValue a, IsValue b) => IsValue (a -> b) where
    toValue f = VLambda (\v -> return (toValue (f (fromValue v))))

instance FromValue Value where
    fromValue x = x

instance IsValue Value where
    toValue x = x

instance IsValue () where
    toValue _ = VTuple []

instance FromValue () where
    fromValue _ = ()

instance (IsValue a, IsValue b) => IsValue (a, b) where
    toValue (x, y) = VTuple [toValue x, toValue y]

instance (FromValue a, FromValue b) => FromValue (a, b) where
    fromValue (VTuple [x, y]) = (fromValue x, fromValue y)
    fromValue _ = error "fromValue (,)"

instance IsValue a => IsValue [a] where
    toValue xs = VArray (map toValue xs)

instance FromValue a => FromValue [a] where
    fromValue (VArray xs) = map fromValue xs
    fromValue _ = error "fromValue []"

instance IsValue a => IsValue (IO a) where
    toValue io = VIO (fmap toValue io)

instance FromValue a => FromValue (IO a) where
    fromValue (VIO io) = fmap fromValue io
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue IO"

instance IsValue a => IsValue (StateT (ProofGoal SAWCtx) IO a) where
    toValue m = VProofScript (fmap toValue m)

instance FromValue a => FromValue (StateT (ProofGoal SAWCtx) IO a) where
    fromValue (VProofScript m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- liftIO $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue ProofScript"

instance IsValue a => IsValue (StateT JavaSetupState IO a) where
    toValue m = VJavaSetup (fmap toValue m)

instance FromValue a => FromValue (StateT JavaSetupState IO a) where
    fromValue (VJavaSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- liftIO $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue JavaSetup"

instance IsValue a => IsValue (StateT LLVMSetupState IO a) where
    toValue m = VLLVMSetup (fmap toValue m)

instance FromValue a => FromValue (StateT LLVMSetupState IO a) where
    fromValue (VLLVMSetup m) = fmap fromValue m
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- liftIO $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue LLVMSetup"

instance IsValue (TypedTerm SAWCtx) where
    toValue t = VTerm t

instance FromValue (TypedTerm SAWCtx) where
    fromValue (VTerm t) = t
    fromValue _ = error "fromValue TypedTerm"

instance FromValue (SharedTerm SAWCtx) where
    fromValue (VTerm t) = ttTerm t
    fromValue _ = error "fromValue SharedTerm"

instance IsValue String where
    toValue n = VString n

instance FromValue String where
    fromValue (VString n) = n
    fromValue _ = error "fromValue String"

instance IsValue Integer where
    toValue n = VInteger n

instance FromValue Integer where
    fromValue (VInteger n) = n
    fromValue _ = error "fromValue Integer"

instance IsValue Int where
    toValue n = VInteger (toInteger n)

instance FromValue Int where
    fromValue (VInteger n)
      | toInteger (minBound :: Int) <= n &&
        toInteger (maxBound :: Int) >= n = fromIntegral n
    fromValue _ = error "fromValue Int"

instance IsValue Bool where
    toValue b = VBool b

instance FromValue Bool where
    fromValue (VBool b) = b
    fromValue _ = error "fromValue Bool"

instance IsValue (Simpset (SharedTerm SAWCtx)) where
    toValue ss = VSimpset ss

instance FromValue (Simpset (SharedTerm SAWCtx)) where
    fromValue (VSimpset ss) = ss
    fromValue _ = error "fromValue Simpset"

instance IsValue (Theorem SAWCtx) where
    toValue t = VTheorem t

instance FromValue (Theorem SAWCtx) where
    fromValue (VTheorem t) = t
    fromValue _ = error "fromValue Theorem"

instance IsValue JIR.JavaMethodSpecIR where
    toValue ms = VJavaMethodSpec ms

instance FromValue JIR.JavaMethodSpecIR where
    fromValue (VJavaMethodSpec ms) = ms
    fromValue _ = error "fromValue JavaMethodSpec"

instance IsValue LIR.LLVMMethodSpecIR where
    toValue ms = VLLVMMethodSpec ms

instance FromValue LIR.LLVMMethodSpecIR where
    fromValue (VLLVMMethodSpec ms) = ms
    fromValue _ = error "fromValue LLVMMethodSpec"

instance IsValue JavaType where
    toValue t = VJavaType t

instance FromValue JavaType where
    fromValue (VJavaType t) = t
    fromValue _ = error "fromValue JavaType"

instance IsValue LSS.MemType where
    toValue t = VLLVMType t

instance FromValue LSS.MemType where
    fromValue (VLLVMType t) = t
    fromValue _ = error "fromValue LLVMType"

instance IsValue (Uninterp SAWCtx) where
    toValue me = VUninterp me

instance FromValue (Uninterp SAWCtx) where
    fromValue (VUninterp me) = me
    fromValue _ = error "fromValue Uninterp"

instance IsValue (CryptolModule SAWCtx) where
    toValue m = VCryptolModule m

instance FromValue (CryptolModule SAWCtx) where
    fromValue (VCryptolModule m) = m
    fromValue _ = error "fromValue ModuleEnv"

instance IsValue JSS.Class where
    toValue c = VJavaClass c

instance FromValue JSS.Class where
    fromValue (VJavaClass c) = c
    fromValue _ = error "fromValue JavaClass"

instance IsValue LLVMModule where
    toValue m = VLLVMModule m

instance FromValue LLVMModule where
    fromValue (VLLVMModule m) = m
    fromValue _ = error "fromValue LLVMModule"

instance IsValue ProofResult where
   toValue r = VProofResult r

instance FromValue ProofResult where
   fromValue (VProofResult r) = r
   fromValue v = error $ "fromValue ProofResult: " ++ show v

instance IsValue SatResult where
   toValue r = VSatResult r

instance FromValue SatResult where
   fromValue (VSatResult r) = r
   fromValue _ = error "fromValue SatResult"
