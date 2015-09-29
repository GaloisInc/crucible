{-# OPTIONS_GHC -fno-warn-deprecated-flags #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.Value where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
#endif
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT(..), ask, asks)
import Control.Monad.State (StateT(..), get, put)
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import qualified Text.LLVM as L

import qualified SAWScript.AST as SS
import qualified SAWScript.CryptolEnv as CEnv
import qualified SAWScript.JavaMethodSpecIR as JIR
import qualified SAWScript.LLVMMethodSpecIR as LIR
import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.LLVM.Codebase as LSS
import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Options (Options)
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.ImportAIG
import SAWScript.SAWCorePrimitives( concretePrimitives )

import Verifier.SAW.FiniteValue
import Verifier.SAW.Rewriter ( Simpset )
import Verifier.SAW.SharedTerm

import qualified Verifier.SAW.Simulator.Concrete as Concrete
import qualified Cryptol.Eval.Value as C
import Verifier.SAW.Cryptol (exportValueWithSchema, exportFiniteValue)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema)
import Cryptol.Utils.PP (pretty)

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
  | VType Cryptol.Schema
  | VReturn Value -- Returned value in unspecified monad
  | VBind Value Value -- Monadic bind in unspecified monad
  | VTopLevel (TopLevel Value)
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
  | VAIG AIGNetwork

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
  , ppOptsAscii :: Bool
  , ppOptsBase :: Int
  }

defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts False False 10

cryptolPPOpts :: PPOpts -> C.PPOpts
cryptolPPOpts opts =
  C.defaultPPOpts
    { C.useAscii = ppOptsAscii opts
    , C.useBase = ppOptsBase opts
    }

commaSep :: [ShowS] -> ShowS
commaSep ss = foldr (.) id (intersperse (showString ",") ss)

showBrackets :: ShowS -> ShowS
showBrackets s = showString "[" . s . showString "]"

showBraces :: ShowS -> ShowS
showBraces s = showString "{" . s . showString "}"

showsProofResult :: PPOpts -> ProofResult -> ShowS
showsProofResult opts r =
  case r of
    Valid -> showString "Valid"
    Invalid t -> showString "Invalid: " . showVal t
    InvalidMulti ts -> showString "Invalid: [" . showMulti "" ts
  where
    opts' = cryptolPPOpts opts
    showVal t = shows (C.ppValue opts' (exportFiniteValue t))
    showEqn (x, t) = showString x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showsSatResult :: PPOpts -> SatResult -> ShowS
showsSatResult opts r =
  case r of
    Unsat -> showString "Unsat"
    Sat t -> showString "Sat: " . showVal t
    SatMulti ts -> showString "Sat: [" . showMulti "" ts
  where
    opts' = cryptolPPOpts opts
    showVal t = shows (C.ppValue opts' (exportFiniteValue t))
    showEqn (x, t) = showString x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showsPrecValue :: PPOpts -> Int -> Value -> ShowS
showsPrecValue opts p v =
  case v of
    VBool True -> showString "true"
    VBool False -> showString "false"
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
    VType sig -> showString (pretty sig)
    VReturn {} -> showString "<<monadic>>"
    VBind {} -> showString "<<monadic>>"
    VTopLevel {} -> showString "<<TopLevel>>"
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
    VProofResult r -> showsProofResult opts r
    VSatResult r -> showsSatResult opts r
    VUninterp u -> showString "Uninterp: " . shows u
    VAIG _ -> showString "<<AIG>>"

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

evaluate :: SharedContext s -> SharedTerm s -> Concrete.CValue
evaluate sc t = Concrete.evalSharedTerm (scModule sc) concretePrimitives t

evaluateTypedTerm :: SharedContext s -> TypedTerm s -> C.Value
evaluateTypedTerm sc (TypedTerm schema trm) =
  exportValueWithSchema schema (evaluate sc trm)

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

-- TopLevel Monad --------------------------------------------------------------

-- | TopLevel Read-Only Environment.
data TopLevelRO =
  TopLevelRO
  { roSharedContext :: SharedContext SAWCtx
  , roJavaCodebase  :: JSS.Codebase
  , roOptions       :: Options
  }

data TopLevelRW =
  TopLevelRW
  { rwValues  :: Map SS.LName Value
  , rwTypes   :: Map SS.LName SS.Schema
  , rwDocs    :: Map SS.Name String
  , rwCryptol :: CEnv.CryptolEnv SAWCtx
  , rwPPOpts  :: PPOpts
  }

newtype TopLevel a = TopLevel (ReaderT TopLevelRO (StateT TopLevelRW IO) a)
  deriving (Functor, Applicative, Monad, MonadIO)

runTopLevel :: TopLevel a -> TopLevelRO -> TopLevelRW -> IO (a, TopLevelRW)
runTopLevel (TopLevel m) = runStateT . runReaderT m

io :: IO a -> TopLevel a
io = liftIO

getSharedContext :: TopLevel (SharedContext SAWCtx)
getSharedContext = TopLevel (asks roSharedContext)

getJavaCodebase :: TopLevel JSS.Codebase
getJavaCodebase = TopLevel (asks roJavaCodebase)

getOptions :: TopLevel Options
getOptions = TopLevel (asks roOptions)

getTopLevelRO :: TopLevel TopLevelRO
getTopLevelRO = TopLevel ask

getTopLevelRW :: TopLevel TopLevelRW
getTopLevelRW = TopLevel get

putTopLevelRW :: TopLevelRW -> TopLevel ()
putTopLevelRW rw = TopLevel (put rw)

-- Other SAWScript Monads ------------------------------------------------------

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
    , jsSimulate :: Bool
    , jsSatBranches :: Bool
    }

type JavaSetup a = StateT JavaSetupState IO a

data LLVMSetupState
  = LLVMSetupState {
      lsSpec :: LIR.LLVMMethodSpecIR
    , lsContext :: SharedContext SAWCtx
    , lsTactic :: ValidationPlan
    , lsSimulate :: Bool
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

instance (IsValue a, IsValue b, IsValue c) => IsValue (a, b, c) where
    toValue (x, y, z) = VTuple [toValue x, toValue y, toValue z]

instance (FromValue a, FromValue b, FromValue c) => FromValue (a, b, c) where
    fromValue (VTuple [x, y, z]) = (fromValue x, fromValue y, fromValue z)
    fromValue _ = error "fromValue (,,)"

instance IsValue a => IsValue [a] where
    toValue xs = VArray (map toValue xs)


instance FromValue a => FromValue [a] where
    fromValue (VArray xs) = map fromValue xs
    fromValue _ = error "fromValue []"

instance IsValue a => IsValue (IO a) where
    toValue action = toValue (io action)

instance IsValue a => IsValue (TopLevel a) where
    toValue action = VTopLevel (fmap toValue action)

instance FromValue a => FromValue (TopLevel a) where
    fromValue (VTopLevel action) = fmap fromValue action
    fromValue (VReturn v) = return (fromValue v)
    fromValue (VBind m1 v2) = do
      v1 <- fromValue m1
      m2 <- io $ applyValue v2 v1
      fromValue m2
    fromValue _ = error "fromValue TopLevel"

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

instance IsValue (AIGNetwork) where
    toValue t = VAIG t

instance FromValue (AIGNetwork) where
    fromValue (VAIG t) = t
    fromValue _ = error "fromValue AIGNetwork"

instance IsValue (TypedTerm SAWCtx) where
    toValue t = VTerm t

instance FromValue (TypedTerm SAWCtx) where
    fromValue (VTerm t) = t
    fromValue _ = error "fromValue TypedTerm"

instance FromValue (SharedTerm SAWCtx) where
    fromValue (VTerm t) = ttTerm t
    fromValue _ = error "fromValue SharedTerm"

instance IsValue Cryptol.Schema where
    toValue s = VType s

instance FromValue Cryptol.Schema where
    fromValue (VType s) = s
    fromValue _ = error "fromValue Schema"

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
   fromValue v = error $ "fromValue SatResult: " ++ show v
