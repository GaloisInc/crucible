{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverlappingInstances #-}
module SAWScript.Value where

import Control.Monad.IO.Class ( liftIO )
import Control.Monad.State ( StateT(..) )
import Data.List ( intersperse )
import qualified Data.Map as M
import Data.Map ( Map )
import qualified Data.Vector as V

import qualified SAWScript.AST as SS
import SAWScript.JavaMethodSpecIR
import SAWScript.LLVMMethodSpecIR
import SAWScript.Proof
import SAWScript.Utils
import qualified Verifier.SAW.Prim as Prim
import Verifier.SAW.Rewriter ( Simpset )
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding ( incVars )

import qualified Verifier.SAW.Evaluator as SC
import qualified Cryptol.ModuleSystem as Cry

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
  | VTerm (SharedTerm s)
  | VCtorApp String [Value s]
  | VIO (IO (Value s))
  | VProofScript (ProofScript s (Value s))
  | VSimpset (Simpset (SharedTerm s))
  | VTheorem (Theorem s)
  | VJavaSetup (JavaSetup (Value s))
  | VLLVMSetup (LLVMSetup (Value s))
  | VJavaMethodSpec JavaMethodSpecIR
  | VLLVMMethodSpec LLVMMethodSpecIR
  | VCryptolModuleEnv Cry.ModuleEnv
  | VSatResult (SatResult s)
  | VProofResult (ProofResult s)
  -- | VAIG (BitEngine Lit) (V.Vector Lit) (V.Vector Lit)

data ProofResult s
  = Valid
  | Invalid (Value s)
    deriving (Show)

data SatResult s
  = Unsat
  | Sat (Value s)
    deriving (Show)

flipSatResult :: SatResult s -> ProofResult s
flipSatResult Unsat = Valid
flipSatResult (Sat t) = Invalid t

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

instance Show (Value s) where
    showsPrec p v =
      case v of
        VBool True -> showString "True"
        VBool False -> showString "False"
        VString s -> shows s
        VInteger n -> shows n
        VWord w x -> showParen (p > 9) (shows x . showString ":[" . shows w . showString "]")
        VArray vs | all isBool vs -> shows (arrayToWord vs)
                  | otherwise -> showList vs
        VTuple vs -> showParen True
                     (foldr (.) id (intersperse (showString ",") (map shows vs)))
        VRecord m -> showString "{" .
                     (foldr (.) id (intersperse (showString ",")
                                   (map showFld (M.toList m)))) .
                     showString "}"
                       where showFld (n, v) = shows n . showString "=" . shows v
        VFun {} -> showString "<<fun>>"
        VFunTerm {} -> showString "<<fun-term>>"
        VFunType {} -> showString "<<fun-type>>"
        VLambda {} -> showString "<<lambda>>"
        VTLambda {} -> showString "<<polymorphic function>>"
        VTerm t -> showsPrec p t
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
        VProofResult Valid -> showString "Valid"
        VProofResult (Invalid t) -> showString "Invalid: " . shows t
        VSatResult Unsat -> showString "Unsat"
        VSatResult (Sat t) -> showString "Sat: " . shows t

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
applyValue sc (VFun f) (VTerm t) = return (f (evaluate sc t))
applyValue _  (VFun f) x = return (f x)
applyValue _  (VFunTerm f) (VTerm t) = return (f t)
applyValue sc (VLambda f) (VTerm t) = f (evaluate sc t) (Just t)
applyValue _  (VLambda f) x = f x Nothing
applyValue sc (VTerm t) x = applyValue sc (evaluate sc t) x
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

importValue :: SC.Value -> Value s
importValue val =
    case val of
      SC.VFun f -> VFun (importValue . f . exportValue)
      SC.VTrue -> VBool True
      SC.VFalse -> VBool False
      SC.VNat n -> VInteger n
      SC.VWord w x -> VWord w x
      SC.VString s -> VString s
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

exportValue :: Value s -> SC.Value
exportValue val =
    case val of
      VBool b -> if b then SC.VTrue else SC.VFalse
      VString s -> SC.VString s
      VInteger n -> SC.VNat n
      VWord w x -> SC.VWord w x
      VArray vs -> SC.VVector (fmap exportValue (V.fromList vs))
      VTuple vs -> SC.VTuple (fmap exportValue (V.fromList vs))
      VRecord vm -> SC.VRecord (fmap exportValue vm)
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
      VProofResult {} -> error "VProofResult unsupported"
      VSatResult {} -> error "VSatResult unsupported"
      -- VAIG {} -> error "VAIG unsupported" -- TODO: could be implemented

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

instance IsValue s a => IsValue s (StateT (SharedTerm s) IO a) where
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

instance IsValue s (SharedTerm s) where
    toValue t = VTerm t
    fromValue (VTerm t) = t
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

instance IsValue SAWCtx JavaMethodSpecIR where
    toValue ms = VJavaMethodSpec ms
    fromValue (VJavaMethodSpec ms) = ms
    fromValue _ = error "fromValue JavaMethodSpec"

instance IsValue SAWCtx LLVMMethodSpecIR where
    toValue ms = VLLVMMethodSpec ms
    fromValue (VLLVMMethodSpec ms) = ms
    fromValue _ = error "fromValue LLVMMethodSpec"

instance IsValue s Cry.ModuleEnv where
    toValue me = VCryptolModuleEnv me
    fromValue (VCryptolModuleEnv me) = me
    fromValue _ = error "fromValue CryptolModuleEnv"

instance IsValue s (ProofResult s) where
   toValue r = VProofResult r
   fromValue (VProofResult r) = r
   fromValue _ = error "fromValue ProofResult"

instance IsValue s (SatResult s) where
   toValue r = VSatResult r
   fromValue (VSatResult r) = r
   fromValue _ = error "fromValue SatResult"
