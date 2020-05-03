{- |
Module           : Lang.Crucible.JVM.Translation.Monad
Description      : The JVMGenerator monad
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : huffman@galois.com, sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -haddock #-}

module Lang.Crucible.JVM.Translation.Monad where

-- base
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Control.Monad.State.Strict
import           Control.Lens hiding (op, (:>))

-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

-- bv-sized
import qualified Data.BitVector.Sized as BV

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx

-- crucible
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.Types
import           Lang.Crucible.Panic

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.Context
-- what4
import           What4.ProgramLoc (Position(InternalPos))

import Debug.Trace

------------------------------------------------------------------------
-- * Generator Monad


-- | Generator to construct a CFG from sequence of monadic actions:
-- See "Lang.Crucible.CFG.Generator".
--
-- * 's' is phantom to prevent mixing constructs from different CFGs
-- * 'ret' is return type of CFG
type JVMGenerator s ret = Generator JVM s (JVMState ret) ret IO

-- | Indicate that CFG generation failed due to ill-formed JVM code.
jvmFail :: HasCallStack => String -> JVMGenerator s ret a
jvmFail msg = error msg

-- | Output a message depending on the current verbosity level.
debug :: Int -> String -> JVMGenerator s ret ()
debug level mesg = do
  v <- use jsVerbosity
  when (level <= v) $ traceM mesg

----------------------------------------------------------------------
-- * Registers

data JVMReg s
  = DReg (Reg s JVMDoubleType)
  | FReg (Reg s JVMFloatType)
  | IReg (Reg s JVMIntType)
  | LReg (Reg s JVMLongType)
  | RReg (Reg s JVMRefType)
   deriving (Show)

------------------------------------------------------------------------
-- * JVMState used during the translation

data JVMState ret s
  = JVMState
  { _jsLabelMap  :: !(Map J.BBId (Label s))
  , _jsStackMap  :: !(Map J.BBId [JVMReg s])
  , _jsLocalsD   :: !(Map J.LocalVariableIndex (Reg s JVMDoubleType))
  , _jsLocalsF   :: !(Map J.LocalVariableIndex (Reg s JVMFloatType))
  , _jsLocalsI   :: !(Map J.LocalVariableIndex (Reg s JVMIntType))
  , _jsLocalsL   :: !(Map J.LocalVariableIndex (Reg s JVMLongType))
  , _jsLocalsR   :: !(Map J.LocalVariableIndex (Reg s JVMRefType))
  , _jsCFG       :: J.CFG
  , jsRetType    :: TypeRepr ret
  , jsContext    :: JVMContext
  , _jsVerbosity :: Int
  }

jsLabelMap :: Simple Lens (JVMState ret s) (Map J.BBId (Label s))
jsLabelMap = lens _jsLabelMap (\s v -> s { _jsLabelMap = v })

jsStackMap :: Simple Lens (JVMState ret s) (Map J.BBId [JVMReg s])
jsStackMap = lens _jsStackMap (\s v -> s { _jsStackMap = v })

jsLocalsD :: Simple Lens (JVMState ret s) (Map J.LocalVariableIndex (Reg s JVMDoubleType))
jsLocalsD = lens _jsLocalsD (\s v -> s { _jsLocalsD = v })

jsLocalsF :: Simple Lens (JVMState ret s) (Map J.LocalVariableIndex (Reg s JVMFloatType))
jsLocalsF = lens _jsLocalsF (\s v -> s { _jsLocalsF = v })

jsLocalsI :: Simple Lens (JVMState ret s) (Map J.LocalVariableIndex (Reg s JVMIntType))
jsLocalsI = lens _jsLocalsI (\s v -> s { _jsLocalsI = v })

jsLocalsL :: Simple Lens (JVMState ret s) (Map J.LocalVariableIndex (Reg s JVMLongType))
jsLocalsL = lens _jsLocalsL (\s v -> s { _jsLocalsL = v })

jsLocalsR :: Simple Lens (JVMState ret s) (Map J.LocalVariableIndex (Reg s JVMRefType))
jsLocalsR = lens _jsLocalsR (\s v -> s { _jsLocalsR = v })

jsCFG :: Simple Lens (JVMState ret s) J.CFG
jsCFG = lens _jsCFG (\s v -> s { _jsCFG = v })

jsVerbosity :: Simple Lens (JVMState ret s) Int
jsVerbosity = lens _jsVerbosity (\s v -> s { _jsVerbosity = v })


-- | Build the initial JVM generator state upon entry to the entry
-- point of a method.
initialState :: JVMContext -> Verbosity -> J.Method -> TypeRepr ret -> JVMState ret s
initialState ctx verbosity method ret =
  JVMState {
    _jsLabelMap = Map.empty,
    _jsStackMap = Map.empty,
    _jsLocalsD = Map.empty,
    _jsLocalsF = Map.empty,
    _jsLocalsI = Map.empty,
    _jsLocalsL = Map.empty,
    _jsLocalsR = Map.empty,
    _jsCFG = methodCFG method,
    jsRetType = ret,
    jsContext = ctx,
    _jsVerbosity = verbosity
  }

methodCFG :: J.Method -> J.CFG
methodCFG method =
  case J.methodBody method of
    J.Code _ _ cfg _ _ _ _ -> cfg
    _                      -> error ("Method " ++ show method ++ " has no body")

------------------------------------------------------------------
-- * JVMValue

-- | Tagged JVM value.
--
-- NOTE: we could switch the below to @type JVMValue s = Expr JVM s
-- JVMValueType@. However, that would give the translator less
-- information. With the type below, the translator can branch on the
-- variant. This is important for translating stack manipulations such
-- as 'popType1' and 'popType2'.
data JVMValue s
  = DValue (JVMDouble s)
  | FValue (JVMFloat s)
  | IValue (JVMInt s)
  | LValue (JVMLong s)
  | RValue (JVMRef s)
  deriving Show

-- | Returns a default value for given type, suitable for initializing
-- fields and arrays.
defaultValue :: J.Type -> JVMValue s
defaultValue (J.ArrayType _tp) = RValue $ App $ NothingValue knownRepr
defaultValue J.BooleanType     = IValue $ App $ BVLit knownRepr (BV.zero knownRepr)
defaultValue J.ByteType        = IValue $ App $ BVLit knownRepr (BV.zero knownRepr)
defaultValue J.CharType        = IValue $ App $ BVLit knownRepr (BV.zero knownRepr)
defaultValue (J.ClassType _st) = RValue $ App $ NothingValue knownRepr
defaultValue J.DoubleType      = DValue $ App $ DoubleLit 0.0
defaultValue J.FloatType       = FValue $ App $ FloatLit 0.0
defaultValue J.IntType         = IValue $ App $ BVLit knownRepr (BV.zero knownRepr)
defaultValue J.LongType        = LValue $ App $ BVLit knownRepr (BV.zero knownRepr)
defaultValue J.ShortType       = IValue $ App $ BVLit knownRepr (BV.zero knownRepr)

-- | Convert a statically tagged value to a dynamically tagged value.
valueToExpr :: JVMValue s -> Expr JVM s JVMValueType
valueToExpr (DValue x) = App $ InjectVariant knownRepr tagD x
valueToExpr (FValue x) = App $ InjectVariant knownRepr tagF x
valueToExpr (IValue x) = App $ InjectVariant knownRepr tagI x
valueToExpr (LValue x) = App $ InjectVariant knownRepr tagL x
valueToExpr (RValue x) = App $ InjectVariant knownRepr tagR x

projectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s (VariantType ctx) ->
  JVMGenerator s ret (Expr JVM s tp)
projectVariant tag var =
  do let mx = App (ProjectVariant knownRepr tag var)
     assertedJustExpr mx "incorrect variant"

injectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s tp ->
  Expr JVM s (VariantType ctx)
injectVariant tag val = App (InjectVariant knownRepr tag val)


fromJVMDynamic :: J.Type -> Expr JVM s JVMValueType -> JVMGenerator s ret (JVMValue s)
fromJVMDynamic ty dyn =
  case ty of
    J.BooleanType -> IValue <$> projectVariant tagI dyn
    J.ArrayType _ -> RValue <$> projectVariant tagR dyn
    J.ByteType    -> IValue <$> projectVariant tagI dyn
    J.CharType    -> IValue <$> projectVariant tagI dyn
    J.ClassType _ -> RValue <$> projectVariant tagR dyn
    J.DoubleType  -> DValue <$> projectVariant tagD dyn
    J.FloatType   -> FValue <$> projectVariant tagF dyn
    J.IntType     -> IValue <$> projectVariant tagI dyn
    J.LongType    -> LValue <$> projectVariant tagL dyn
    J.ShortType   -> IValue <$> projectVariant tagI dyn

toJVMDynamic :: J.Type -> JVMValue s -> JVMGenerator s ret (Expr JVM s JVMValueType)
toJVMDynamic ty val =
  case ty of
    J.BooleanType -> injectVariant tagI <$> fmap boolFromInt (fromIValue val)
    J.ArrayType _ -> injectVariant tagR <$> fromRValue val
    J.ByteType    -> injectVariant tagI <$> fmap byteFromInt (fromIValue val)
    J.CharType    -> injectVariant tagI <$> fmap charFromInt (fromIValue val)
    J.ClassType _ -> injectVariant tagR <$> fromRValue val
    J.DoubleType  -> injectVariant tagD <$> fromDValue val
    J.FloatType   -> injectVariant tagF <$> fromFValue val
    J.IntType     -> injectVariant tagI <$> fromIValue val
    J.LongType    -> injectVariant tagL <$> fromLValue val
    J.ShortType   -> injectVariant tagI <$> fmap shortFromInt (fromIValue val)


boolFromInt :: JVMInt s -> JVMInt s
boolFromInt x = App (BVZext w32 w1 (App (BVTrunc w1 w32 x)))

byteFromInt :: JVMInt s -> JVMInt s
byteFromInt i = App (BVSext w32 w8 (App (BVTrunc w8 w32 i)))

charFromInt :: JVMInt s -> JVMInt s
charFromInt i = App (BVZext w32 w16 (App (BVTrunc w16 w32 i)))

shortFromInt :: JVMInt s -> JVMInt s
shortFromInt i = App (BVSext w32 w16 (App (BVTrunc w16 w32 i)))

------------------------------------------------------------------------



fromIValue :: HasCallStack => JVMValue s -> JVMGenerator s ret (JVMInt s)
fromIValue (IValue v) = return v
fromIValue _ = jvmFail "fromIValue"

fromLValue :: HasCallStack => JVMValue s -> JVMGenerator s ret (JVMLong s)
fromLValue (LValue v) = return v
fromLValue _ = jvmFail "fromLValue"

fromDValue :: HasCallStack => JVMValue s -> JVMGenerator s ret (JVMDouble s)
fromDValue (DValue v) = return v
fromDValue _ = jvmFail "fromDValue"

fromFValue :: HasCallStack => JVMValue s -> JVMGenerator s ret (JVMFloat s)
fromFValue (FValue v) = return v
fromFValue _ = jvmFail "fromFValue"

fromRValue :: HasCallStack => JVMValue s -> JVMGenerator s ret (JVMRef s)
fromRValue (RValue v) = return v
fromRValue v = jvmFail $ "fromRValue:" ++ show v


------------------------------------------------------------------
-- * Some utilities for generation (not specific to the JVM)

-- | Generate code to test whether a 'Maybe' value is nothing.
gen_isNothing :: (IsSyntaxExtension p, KnownRepr TypeRepr tp, Monad m) =>
  Expr p s (MaybeType tp)
  -> Generator p s ret k m (Expr p s BoolType)
gen_isNothing expr =
  caseMaybe expr knownRepr
  MatchMaybe
  { onNothing = return $ App $ BoolLit True
  , onJust    = \_ -> return $ App $ BoolLit False
  }

-- | Generate code to test whether a 'Maybe' value is defined.
gen_isJust :: (IsSyntaxExtension p, KnownRepr TypeRepr tp, Monad m) =>
  Expr p s (MaybeType tp)
           -> Generator p s ret k m (Expr p s BoolType)
gen_isJust expr =
  caseMaybe expr knownRepr
  MatchMaybe
  { onNothing = return $ App $ BoolLit False
  , onJust    = \_ -> return $ App $ BoolLit True
  }


-- | Generate an expression that evaluates the function for
-- each element of an array.
forEach_ :: (IsSyntaxExtension p, KnownRepr TypeRepr tp, Monad m)
            => Expr p s (VectorType tp)
            -> (Expr p s tp -> Generator p s ret k m ())
            -> Generator p s ret k m ()
forEach_ vec body = do
  i <- newReg $ App (NatLit 0)

  while (InternalPos, do
            j <- readReg i
            return $ App $ NatLt j (App $ VectorSize vec)
        )
        (InternalPos, do
           j <- readReg i
           let v = App $ VectorGetEntry knownRepr vec j
           body v
           modifyReg i (\j0 -> App $ NatAdd j0 (App $ NatLit 1))
        )

-- | Generate an expression that evaluates the function for
-- each value in the range @i = 0; i<count; i++@.
iterate_ :: (IsSyntaxExtension p, Monad m)
  => Expr p s JVMIntType
  -> (Expr p s JVMIntType -> Generator p s ret k m ())
  -> Generator p s ret k m ()
iterate_ count body = do
  i <- newReg $ App (BVLit w32 (BV.zero w32))

  while (InternalPos, do
            j <- readReg i
            return $ App $ BVSlt w32 j count
        )
        (InternalPos, do
           j <- readReg i
           body j
           modifyReg i (\j0 -> App (BVAdd w32 j0 (App (BVLit w32 (BV.one w32)))))
        )
