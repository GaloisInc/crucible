{- |
Module           : Lang.Crucible.JVM.Translation
Description      : Translation of JVM AST into Crucible control-flow graph
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : huffman@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -haddock #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Lang.Crucible.JVM.Translation where

import Control.Monad.State.Strict
import Control.Monad.ST
import Control.Lens hiding (op, (:>))
import Data.Int (Int32)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.String (fromString)

import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

import qualified Data.Parameterized.Context as Ctx

import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           What4.ProgramLoc (Position(InternalPos))

----------------------------------------------------------------------
-- JVM types

-- | JVM extension.
type JVM = () -- TODO

type JVMObjectType = RecursiveType "JVM_object" EmptyCtx

type JVMDoubleType = FloatType DoubleFloat
type JVMFloatType  = FloatType SingleFloat
type JVMIntType    = BVType 32
type JVMLongType   = BVType 64
type JVMRefType    = MaybeType (ReferenceType JVMObjectType)

-- | A JVM value is either a double, float, int, long, or reference.
type JVMValueType = VariantType JVMValueCtx

type JVMValueCtx =
  EmptyCtx
  ::> JVMDoubleType
  ::> JVMFloatType
  ::> JVMIntType
  ::> JVMLongType
  ::> JVMRefType

-- | A class instance contains a table of fields.
-- TODO: Should also have a pointer to the class.
type JVMInstanceType = StringMapType JVMValueType

-- | An array is a length paired with a vector of values.
type JVMArrayType =
  StructType (EmptyCtx ::> JVMIntType ::> VectorType JVMValueType)

-- | An object is either a class instance or an array.
type JVMObjectImpl =
  VariantType (EmptyCtx ::> JVMInstanceType ::> JVMArrayType)

instance IsRecursiveType "JVM_object" where
  type UnrollType "JVM_object" ctx = JVMObjectImpl
  unrollType _nm _ctx = knownRepr :: TypeRepr JVMObjectImpl

----------------------------------------------------------------------
-- Index values for sums and products

tagD :: Ctx.Index JVMValueCtx JVMDoubleType
tagD =
  Ctx.skipIndex $ Ctx.skipIndex $ Ctx.skipIndex $
  Ctx.skipIndex $ Ctx.nextIndex Ctx.zeroSize

tagF :: Ctx.Index JVMValueCtx JVMFloatType
tagF =
  Ctx.skipIndex $ Ctx.skipIndex $ Ctx.skipIndex $
  Ctx.nextIndex $ Ctx.incSize Ctx.zeroSize

tagI :: Ctx.Index JVMValueCtx JVMIntType
tagI =
  Ctx.skipIndex $ Ctx.skipIndex $ Ctx.nextIndex $
  Ctx.incSize $ Ctx.incSize Ctx.zeroSize

tagL :: Ctx.Index JVMValueCtx JVMLongType
tagL =
  Ctx.skipIndex $ Ctx.nextIndex $ Ctx.incSize $
  Ctx.incSize $ Ctx.incSize Ctx.zeroSize

tagR :: Ctx.Index JVMValueCtx JVMRefType
tagR =
  Ctx.nextIndex $ Ctx.incSize $ Ctx.incSize $
  Ctx.incSize $ Ctx.incSize Ctx.zeroSize

tag1 :: Ctx.Index (EmptyCtx ::> a ::> b) a
tag1 = Ctx.skipIndex (Ctx.nextIndex Ctx.zeroSize)

tag2 :: Ctx.Index (EmptyCtx ::> a ::> b) b
tag2 = Ctx.nextIndex (Ctx.incSize Ctx.zeroSize)

----------------------------------------------------------------------
-- JVMValue

type JVMBool   s = Expr JVM s BoolType
type JVMDouble s = Expr JVM s JVMDoubleType
type JVMFloat  s = Expr JVM s JVMFloatType
type JVMInt    s = Expr JVM s JVMIntType
type JVMLong   s = Expr JVM s JVMLongType
type JVMRef    s = Expr JVM s JVMRefType
type JVMObject s = Expr JVM s JVMObjectType

{-
data JVMValue f
  = DValue (f JVMDoubleType)
  | FValue (f JVMFloatType)
  | IValue (f JVMIntType)
  | LValue (f JVMLongType)
  | RValue (f JVMRefType)
type JVMExpr s = JVMValue (Expr JVM s)
type JVMReg s = JVMValue (Reg s)
-}

data JVMValue s
  = DValue (JVMDouble s)
  | FValue (JVMFloat s)
  | IValue (JVMInt s)
  | LValue (JVMLong s)
  | RValue (JVMRef s)

data JVMReg s
  = DReg (Reg s JVMDoubleType)
  | FReg (Reg s JVMFloatType)
  | IReg (Reg s JVMIntType)
  | LReg (Reg s JVMLongType)
  | RReg (Reg s JVMRefType)

data JVMFrame v
  = JVMFrame
    { _operandStack :: ![v]
    , _localVariables :: !(Map J.LocalVariableIndex v)
    }

instance Functor JVMFrame where
  fmap f (JVMFrame os lv) = JVMFrame (fmap f os) (fmap f lv)

instance Foldable JVMFrame where
  foldr f z (JVMFrame os lv) = foldr f (foldr f z lv) os

instance Traversable JVMFrame where
  traverse f (JVMFrame os lv) = JVMFrame <$> traverse f os <*> traverse f lv

operandStack :: Simple Lens (JVMFrame v) [v]
operandStack = lens _operandStack (\s v -> s{ _operandStack = v})

localVariables :: Simple Lens (JVMFrame v) (Map J.LocalVariableIndex v)
localVariables = lens _localVariables (\s v -> s{ _localVariables = v})

type JVMExprFrame s = JVMFrame (JVMValue s)
type JVMRegisters s = JVMFrame (JVMReg s)

----------------------------------------------------------------------
-- JVMRef

rIsNull :: JVMRef s -> JVMGenerator h s ret (JVMBool s)
rIsNull mr =
  caseMaybe mr knownRepr
  MatchMaybe {
    onNothing = return bTrue,
    onJust = \_ -> return bFalse
    }

rEqual :: JVMRef s -> JVMRef s -> JVMGenerator h s ret (JVMBool s)
rEqual mr1 mr2 =
  caseMaybe mr1 knownRepr
  MatchMaybe {
    onNothing = rIsNull mr2,
    onJust = \r1 ->
    caseMaybe mr2 knownRepr
    MatchMaybe {
      onNothing = return bFalse,
      onJust = \r2 -> return (App (ReferenceEq knownRepr r1 r2))
      }
    }

----------------------------------------------------------------------
-- JVMContext

data JVMHandleInfo where
  JVMHandleInfo :: J.Method -> FnHandle init ret -> JVMHandleInfo

data JVMContext =
  JVMContext {
    symbolMap :: Map (J.ClassName, J.MethodKey) JVMHandleInfo
  }

------------------------------------------------------------------------
-- JVMState

data JVMState ret s
  = JVMState
  { _jsLabelMap :: !(Map J.BBId (Label s))
  , _jsFrameMap :: !(Map J.BBId (JVMFrame (JVMReg s)))
  , _jsCFG :: J.CFG
  , jsRetType :: TypeRepr ret
  , jsContext :: JVMContext
  }

jsLabelMap :: Simple Lens (JVMState ret s) (Map J.BBId (Label s))
jsLabelMap = lens _jsLabelMap (\s v -> s { _jsLabelMap = v })

jsFrameMap :: Simple Lens (JVMState ret s) (Map J.BBId (JVMFrame (JVMReg s)))
jsFrameMap = lens _jsFrameMap (\s v -> s { _jsFrameMap = v })

jsCFG :: Simple Lens (JVMState ret s) J.CFG
jsCFG = lens _jsCFG (\s v -> s { _jsCFG = v })

type JVMGenerator h s ret = Generator JVM h s (JVMState ret) ret

-- | Indicate that CFG generation failed due to ill-formed JVM code.
jvmFail :: String -> JVMGenerator h s ret a
jvmFail msg = fail msg

newJVMReg :: JVMValue s -> JVMGenerator h s ret (JVMReg s)
newJVMReg val =
  case val of
    DValue v -> DReg <$> newReg v
    FValue v -> FReg <$> newReg v
    IValue v -> IReg <$> newReg v
    LValue v -> LReg <$> newReg v
    RValue v -> RReg <$> newReg v

readJVMReg :: JVMReg s -> JVMGenerator h s ret (JVMValue s)
readJVMReg reg =
  case reg of
    DReg r -> DValue <$> readReg r
    FReg r -> FValue <$> readReg r
    IReg r -> IValue <$> readReg r
    LReg r -> LValue <$> readReg r
    RReg r -> RValue <$> readReg r

writeJVMReg :: JVMReg s -> JVMValue s -> JVMGenerator h s ret ()
writeJVMReg (DReg r) (DValue v) = assignReg r v
writeJVMReg (FReg r) (FValue v) = assignReg r v
writeJVMReg (IReg r) (IValue v) = assignReg r v
writeJVMReg (LReg r) (LValue v) = assignReg r v
writeJVMReg (RReg r) (RValue v) = assignReg r v
writeJVMReg _ _ = jvmFail "writeJVMReg"

saveStack :: [JVMReg s] -> [JVMValue s] -> JVMGenerator h s ret ()
saveStack [] [] = return ()
saveStack (r : rs) (v : vs) = writeJVMReg r v >> saveStack rs vs
saveStack _ _ = jvmFail "saveStack"

saveLocals ::
  Map J.LocalVariableIndex (JVMReg s) ->
  Map J.LocalVariableIndex (JVMValue s) ->
  JVMGenerator h s ret ()
saveLocals rs vs
  | Map.keys rs == Map.keys vs = sequence_ (Map.intersectionWith writeJVMReg rs vs)
  | otherwise                  = jvmFail "saveLocals"

newRegisters :: JVMExprFrame s -> JVMGenerator h s ret (JVMRegisters s)
newRegisters = traverse newJVMReg

readRegisters :: JVMRegisters s -> JVMGenerator h s ret (JVMExprFrame s)
readRegisters = traverse readJVMReg

writeRegisters :: JVMRegisters s -> JVMExprFrame s -> JVMGenerator h s ret ()
writeRegisters rs vs =
  do saveStack (rs^.operandStack) (vs^.operandStack)
     saveLocals (rs^.localVariables) (vs^.localVariables)

forceJVMValue :: JVMValue s -> JVMGenerator h s ret (JVMValue s)
forceJVMValue val =
  case val of
    DValue v -> DValue <$> forceEvaluation v
    FValue v -> FValue <$> forceEvaluation v
    IValue v -> IValue <$> forceEvaluation v
    LValue v -> LValue <$> forceEvaluation v
    RValue v -> RValue <$> forceEvaluation v

w8 :: NatRepr 8
w8 = knownNat

w16 :: NatRepr 16
w16 = knownNat

w32 :: NatRepr 32
w32 = knownNat

w64 :: NatRepr 64
w64 = knownNat


{-----
-- | Information about a JVM basic block
data JVMBlockInfo s
  = JVMBlockInfo
    {
      -- The crucible block label corresponding to this JVM block
      block_label    :: Label s

      -- map from labels to assignments that must be made before
      -- jumping.  If this is the block info for label l',
      -- and the map has [(i1,v1),(i2,v2)] in the phi_map for block l,
      -- then basic block l is required to assign i1 = v1 and i2 = v2
      -- before jumping to block l'.
    , block_phi_map    :: !(Map J.BBId (Seq (L.Ident, L.Type, L.Value)))
    }

buildBlockInfoMap :: J.CFG -> LLVMEnd h s ret (Map J.BBId (Label s))
buildBlockInfoMap d = Map.fromList <$> (mapM buildBlockInfo $ L.defBody d)

buildBlockInfo :: J.BasicBlock -> JVMEnd h s ret (J.BBId, Label s)
buildBlockInfo bb = do
  let phi_map = buildPhiMap (L.bbStmts bb)
  let Just blk_lbl = L.bbLabel bb
  lab <- newLabel
  return (blk_lbl, LLVMBlockInfo{ block_phi_map = phi_map
                                , block_label = lab
                                })
-------------------------------------------------------------------------------}

generateBasicBlock ::
  J.BasicBlock ->
  JVMRegisters s ->
  JVMGenerator h s ret a
generateBasicBlock bb rs =
  do -- Record the registers for this block.
     -- This also signals that generation of this block has started.
     jsFrameMap %= Map.insert (J.bbId bb) rs
     -- Read initial values
     vs <- readRegisters rs
     -- Translate all instructions
     evalStateT (mapM_ generateInstruction (J.bbInsts bb)) vs
     -- There should have been a block-terminating instruction
     jvmFail "generateBasicBlock: no terminal instruction"

-- | Prepare for a branch or jump to the given address, by generating
-- a transition block to copy the values into the appropriate
-- registers. If the target has already been translated (or is
-- currently being translated) then the registers already exist, so we
-- simply write into them. If the target has not been started yet, we
-- copy the values into fresh registers, and also recursively call
-- 'generateBasicBlock' on the target block to start translating it.
processBlockAtPC :: J.PC -> JVMExprFrame s -> JVMGenerator h s ret (Label s)
processBlockAtPC pc vs =
  defineBlockLabel $
  do bb <- getBasicBlockAtPC pc
     lbl <- getLabelAtPC pc
     fm <- use jsFrameMap
     case Map.lookup (J.bbId bb) fm of
       Just rs ->
         do writeRegisters rs vs
       Nothing ->
         do rs <- newRegisters vs
            defineBlock lbl (generateBasicBlock bb rs)
     jump lbl

getBasicBlockAtPC :: J.PC -> JVMGenerator h s ret J.BasicBlock
getBasicBlockAtPC pc =
  do cfg <- use jsCFG
     case J.bbByPC cfg pc of
       Nothing -> jvmFail "getBasicBlockAtPC"
       Just bb -> return bb

getLabelAtPC :: J.PC -> JVMGenerator h s ret (Label s)
getLabelAtPC pc =
  do bb <- getBasicBlockAtPC pc
     lm <- use jsLabelMap
     case Map.lookup (J.bbId bb) lm of
       Nothing -> jvmFail "getLabelAtPC"
       Just lbl -> return lbl

----------------------------------------------------------------------
-- JVM statement generator monad


-- | This has extra state that is only relevant in the context of a
-- single basic block: It tracks the values of the operand stack and
-- local variable array at each instruction.
type JVMStmtGen h s ret = StateT (JVMExprFrame s) (JVMGenerator h s ret)

-- | Indicate that CFG generation failed due to ill-formed JVM code.
sgFail :: String -> JVMStmtGen h s ret a
sgFail msg = lift $ jvmFail msg

sgUnimplemented :: String -> JVMStmtGen h s ret a
sgUnimplemented msg = sgFail $ "unimplemented: " ++ msg

getStack :: JVMStmtGen h s ret [JVMValue s]
getStack = use operandStack

putStack :: [JVMValue s] -> JVMStmtGen h s ret ()
putStack vs = operandStack .= vs

popValue :: JVMStmtGen h s ret (JVMValue s)
popValue =
  do vs <- getStack
     case vs of
       [] -> sgFail "popValue: empty stack"
       (v : vs') ->
         do putStack vs'
            return v

pushValue :: JVMValue s -> JVMStmtGen h s ret ()
pushValue v =
  do v' <- lift $ forceJVMValue v
     vs <- getStack
     putStack (v' : vs)

pushValues :: [JVMValue s] -> JVMStmtGen h s ret ()
pushValues vs =
  do vs' <- getStack
     putStack (vs ++ vs')

isType1 :: JVMValue s -> Bool
isType1 v =
  case v of
    DValue _ -> False
    LValue _ -> False
    _        -> True

isType2 :: JVMValue s -> Bool
isType2 = not . isType1

popType1 :: JVMStmtGen h s ret (JVMValue s)
popType1 =
  do v <- popValue
     if isType1 v then return v else sgFail "popType1"

popType2 :: JVMStmtGen h s ret [JVMValue s]
popType2 =
  do vs <- getStack
     case vs of
       v : vs' | isType2 v ->
         putStack vs' >> return [v]
       v1 : v2 : vs' | isType1 v1 && isType1 v2 ->
         putStack vs' >> return [v1, v2]
       _ ->
         sgFail "popType2"

fromIValue :: JVMValue s -> JVMStmtGen h s ret (JVMInt s)
fromIValue (IValue v) = return v
fromIValue _ = sgFail "fromIValue"

fromLValue :: JVMValue s -> JVMStmtGen h s ret (JVMLong s)
fromLValue (LValue v) = return v
fromLValue _ = sgFail "fromLValue"

fromDValue :: JVMValue s -> JVMStmtGen h s ret (JVMDouble s)
fromDValue (DValue v) = return v
fromDValue _ = sgFail "fromDValue"

fromFValue :: JVMValue s -> JVMStmtGen h s ret (JVMFloat s)
fromFValue (FValue v) = return v
fromFValue _ = sgFail "fromFValue"

fromRValue :: JVMValue s -> JVMStmtGen h s ret (JVMRef s)
fromRValue (RValue v) = return v
fromRValue _ = sgFail "fromRValue"

iPop :: JVMStmtGen h s ret (JVMInt s)
iPop = popValue >>= fromIValue

lPop :: JVMStmtGen h s ret (JVMLong s)
lPop = popValue >>= fromLValue

rPop :: JVMStmtGen h s ret (JVMRef s)
rPop = popValue >>= fromRValue

dPop :: JVMStmtGen h s ret (JVMDouble s)
dPop = popValue >>= fromDValue

fPop :: JVMStmtGen h s ret (JVMFloat s)
fPop = popValue >>= fromFValue

iPush :: JVMInt s -> JVMStmtGen h s ret ()
iPush i = pushValue (IValue i)

lPush :: JVMLong s -> JVMStmtGen h s ret ()
lPush l = pushValue (LValue l)

fPush :: JVMFloat s -> JVMStmtGen h s ret ()
fPush f = pushValue (FValue f)

dPush :: JVMDouble s -> JVMStmtGen h s ret ()
dPush d = pushValue (DValue d)

rPush :: JVMRef s -> JVMStmtGen h s ret ()
rPush r = pushValue (RValue r)

setLocal :: J.LocalVariableIndex -> JVMValue s -> JVMStmtGen h s ret ()
setLocal idx v =
  do v' <- lift $ forceJVMValue v
     localVariables %= Map.insert idx v'

getLocal :: J.LocalVariableIndex -> JVMStmtGen h s ret (JVMValue s)
getLocal idx =
  do vs <- use localVariables
     case Map.lookup idx vs of
       Just v -> return v
       Nothing -> sgFail "getLocal"

throwIfRefNull ::
  JVMRef s -> JVMStmtGen h s ret (Expr JVM s (ReferenceType JVMObjectType))
throwIfRefNull r = lift $ assertedJustExpr r "null dereference"

projectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s (VariantType ctx) ->
  JVMStmtGen h s ret (Expr JVM s tp)
projectVariant tag var =
  do let mx = App (ProjectVariant knownRepr tag var)
     lift $ assertedJustExpr mx "incorrect variant"

injectVariant ::
  KnownRepr (Ctx.Assignment TypeRepr) ctx =>
  Ctx.Index ctx tp ->
  Expr JVM s tp ->
  Expr JVM s (VariantType ctx)
injectVariant tag val = App (InjectVariant knownRepr tag val)

arrayLength :: Expr JVM s JVMArrayType -> JVMInt s
arrayLength arr = App (GetStruct arr tag1 knownRepr)

throw :: JVMRef s -> JVMStmtGen h s ret ()
throw _ = sgUnimplemented "throw"

rNull :: JVMRef s
rNull = App (NothingValue knownRepr)

iZero :: JVMInt s
iZero = App (BVLit w32 0)

bTrue :: JVMBool s
bTrue = App (BoolLit True)

bFalse :: JVMBool s
bFalse = App (BoolLit False)

processBlockAtPC' :: J.PC -> JVMStmtGen h s ret (Label s)
processBlockAtPC' pc =
  do vs <- get
     lift $ processBlockAtPC pc vs

nextPC :: J.PC -> JVMStmtGen h s ret J.PC
nextPC pc =
  do cfg <- lift $ use jsCFG
     case J.nextPC cfg pc of
       Nothing -> sgFail "nextPC"
       Just pc' -> return pc'

----------------------------------------------------------------------

pushRet ::
  forall h s ret tp. TypeRepr tp -> Expr JVM s tp -> JVMStmtGen h s ret ()
pushRet tp expr =
  tryPush dPush $
  tryPush fPush $
  tryPush iPush $
  tryPush lPush $
  tryPush rPush $
  sgFail "pushRet: invalid type"
  where
    tryPush ::
      forall t. KnownRepr TypeRepr t =>
      (Expr JVM s t -> JVMStmtGen h s ret ()) ->
      JVMStmtGen h s ret () -> JVMStmtGen h s ret ()
    tryPush push k =
      case testEquality tp (knownRepr :: TypeRepr t) of
        Just Refl -> push expr
        Nothing -> k

popArgument ::
  forall tp h s ret. TypeRepr tp -> JVMStmtGen h s ret (Expr JVM s tp)
popArgument tp =
  tryPop dPop $
  tryPop fPop $
  tryPop iPop $
  tryPop lPop $
  tryPop rPop $
  sgFail "pushRet: invalid type"
  where
    tryPop ::
      forall t. KnownRepr TypeRepr t =>
      JVMStmtGen h s ret (Expr JVM s t) ->
      JVMStmtGen h s ret (Expr JVM s tp) ->
      JVMStmtGen h s ret (Expr JVM s tp)
    tryPop pop k =
      case testEquality tp (knownRepr :: TypeRepr t) of
        Just Refl -> pop
        Nothing -> k

-- | Pop arguments from the stack; the last argument should be at the
-- top of the stack.
popArguments ::
  forall args h s ret.
  CtxRepr args -> JVMStmtGen h s ret (Ctx.Assignment (Expr JVM s) args)
popArguments args =
  case Ctx.viewAssign args of
    Ctx.AssignEmpty -> return Ctx.empty
    Ctx.AssignExtend tps tp ->
      do x <- popArgument tp
         xs <- popArguments tps
         return (Ctx.extend xs x)

callJVMHandle :: JVMHandleInfo -> JVMStmtGen h s ret ()
callJVMHandle (JVMHandleInfo _method handle) =
  do args <- popArguments (handleArgTypes handle)
     result <- lift $ call (App (HandleLit handle)) args
     pushRet (handleReturnType handle) result

----------------------------------------------------------------------

-- | Do the heavy lifting of translating JVM instructions to crucible code.
generateInstruction ::
  forall h s ret.
  (J.PC, J.Instruction) ->
  JVMStmtGen h s ret ()
generateInstruction (pc, instr) =
  case instr of
    -- Type conversion instructions
    J.D2f -> unary dPop fPush floatFromDouble
    J.D2i -> unary dPop iPush intFromDouble
    J.D2l -> unary dPop lPush longFromDouble
    J.F2d -> unary fPop dPush doubleFromFloat
    J.F2i -> unary fPop iPush intFromFloat
    J.F2l -> unary fPop lPush longFromFloat
    J.I2b -> unary iPop iPush byteFromInt
    J.I2c -> unary iPop iPush charFromInt
    J.I2d -> unary iPop dPush doubleFromInt
    J.I2f -> unary iPop fPush floatFromInt
    J.I2l -> unary iPop lPush longFromInt
    J.I2s -> unary iPop iPush shortFromInt
    J.L2d -> unary lPop dPush doubleFromLong
    J.L2f -> unary lPop fPush floatFromLong
    J.L2i -> unary lPop iPush intFromLong

    -- Arithmetic instructions
    J.Dadd  -> binary dPop dPop dPush dAdd
    J.Dsub  -> binary dPop dPop dPush dSub
    J.Dneg  -> unary dPop dPush dNeg
    J.Dmul  -> binary dPop dPop dPush dMul
    J.Ddiv  -> binary dPop dPop dPush dDiv
    J.Drem  -> binary dPop dPop dPush dRem
    J.Dcmpg -> binary dPop dPop iPush (error "dCmpg")
    J.Dcmpl -> binary dPop dPop iPush (error "dCmpl")
    J.Fadd  -> binary fPop fPop fPush fAdd
    J.Fsub  -> binary fPop fPop fPush fSub
    J.Fneg  -> unary fPop fPush (error "fNeg")
    J.Fmul  -> binary fPop fPop fPush fMul
    J.Fdiv  -> binary fPop fPop fPush fDiv
    J.Frem  -> binary fPop fPop fPush fRem
    J.Fcmpg -> binary fPop fPop iPush (error "fCmpg")
    J.Fcmpl -> binary fPop fPop iPush (error "fCmpl")
    J.Iadd  -> binary iPop iPop iPush (\a b -> App (BVAdd w32 a b))
    J.Isub  -> binary iPop iPop iPush (\a b -> App (BVSub w32 a b))
    J.Imul  -> binary iPop iPop iPush (\a b -> App (BVMul w32 a b))
    J.Idiv  -> binary iPop iPop iPush
               (\a b -> App (AddSideCondition (BaseBVRepr w32) (App (BVNonzero w32 b))
                             "java/lang/ArithmeticException"
                             (App (BVSdiv w32 a b))))
    J.Irem -> binary iPop iPop iPush
               (\a b -> App (AddSideCondition (BaseBVRepr w32) (App (BVNonzero w32 b))
                             "java/lang/ArithmeticException"
                             (App (BVSrem w32 a b))))
    J.Ineg  -> unary iPop iPush (error "iNeg")
    J.Iand  -> binary iPop iPop iPush (\a b -> App (BVAnd w32 a b))
    J.Ior   -> binary iPop iPop iPush (\a b -> App (BVOr  w32 a b))
    J.Ixor  -> binary iPop iPop iPush (\a b -> App (BVXor w32 a b))
    J.Ishl  -> binary iPop iPop iPush (error "iShl")
    J.Ishr  -> binary iPop iPop iPush (error "iShr")
    J.Iushr -> binary iPop iPop iPush (error "iUshr")
    J.Ladd  -> binary lPop lPop lPush (\a b -> App (BVAdd w64 a b))
    J.Lsub  -> binary lPop lPop lPush (\a b -> App (BVSub w64 a b))
    J.Lmul  -> binary lPop lPop lPush (\a b -> App (BVMul w64 a b))
    J.Lneg  -> unary lPop lPush (error "lNeg")
    J.Ldiv  -> binary lPop lPop (error "lPush")
               (\a b -> App (AddSideCondition (BaseBVRepr w64) (App (BVNonzero w64 b))
                             "java/lang/ArithmeticException"
                             (App (BVSdiv w64 a b))))
    J.Lrem -> binary lPop lPop lPush
               (\a b -> App (AddSideCondition (BaseBVRepr w64) (App (BVNonzero w64 b))
                             "java/lang/ArithmeticException"
                             (App (BVSrem w64 a b))))
    J.Land  -> binary lPop lPop lPush (\a b -> App (BVAnd w64 a b))
    J.Lor   -> binary lPop lPop lPush (\a b -> App (BVOr  w64 a b))
    J.Lxor  -> binary lPop lPop lPush (\a b -> App (BVXor w64 a b))
    J.Lcmp  -> binary lPop lPop iPush (error "lCmp")
    J.Lshl  -> binary lPop (longFromInt <$> iPop) lPush (\a b -> App (BVShl w64 a b))
    J.Lshr  -> binary lPop (longFromInt <$> iPop) lPush (\a b -> App (BVAshr w64 a b))
    J.Lushr -> binary lPop (longFromInt <$> iPop) lPush (\a b -> App (BVLshr w64 a b))

    -- Load and store instructions
    J.Iload idx -> getLocal idx >>= pushValue
    J.Lload idx -> getLocal idx >>= pushValue
    J.Fload idx -> getLocal idx >>= pushValue
    J.Dload idx -> getLocal idx >>= pushValue
    J.Aload idx -> getLocal idx >>= pushValue
    J.Istore idx -> popValue >>= setLocal idx
    J.Lstore idx -> popValue >>= setLocal idx
    J.Fstore idx -> popValue >>= setLocal idx
    J.Dstore idx -> popValue >>= setLocal idx
    J.Astore idx -> popValue >>= setLocal idx
    J.Ldc cpv ->
      case cpv of
        J.Double v   -> dPush (dConst v)
        J.Float v    -> fPush (fConst v)
        J.Integer v  -> iPush (iConst (toInteger v))
        J.Long v     -> lPush (lConst (toInteger v))
        J.String _v  -> sgUnimplemented "ldc string" -- pushValue . RValue =<< refFromString v
        J.ClassRef _ -> sgUnimplemented "ldc class" -- pushValue . RValue =<< getClassObject c

    -- Object creation and manipulation
    J.New _name ->
      do sgUnimplemented "new" -- pushValue . RValue =<< newObject name
    J.Getfield fldId ->
      do objectRef <- rPop
         rawRef <- throwIfRefNull objectRef
         obj <- lift $ readRef rawRef
         let uobj = App (UnrollRecursive knownRepr knownRepr obj)
         let minst = App (ProjectVariant knownRepr tag1 uobj)
         inst <- lift $ assertedJustExpr minst "getfield: not a valid class instance"
         let key = App (TextLit (fromString (J.fieldIdName fldId)))
         let mval = App (LookupStringMapEntry knownRepr inst key)
         val <- lift $ assertedJustExpr mval "getfield: field not found"
         case J.fieldIdType fldId of
           J.BooleanType -> iPush =<< projectVariant tagI val
           J.ArrayType _ -> rPush =<< projectVariant tagR val
           J.ByteType    -> iPush =<< projectVariant tagI val
           J.CharType    -> iPush =<< projectVariant tagI val
           J.ClassType _ -> rPush =<< projectVariant tagR val
           J.DoubleType  -> dPush =<< projectVariant tagD val
           J.FloatType   -> fPush =<< projectVariant tagF val
           J.IntType     -> iPush =<< projectVariant tagI val
           J.LongType    -> lPush =<< projectVariant tagL val
           J.ShortType   -> iPush =<< projectVariant tagI val
    J.Putfield fldId ->
      do val <- popValue
         objectRef <- rPop
         rawRef <- throwIfRefNull objectRef
         obj <- lift $ readRef rawRef
         let uobj = App (UnrollRecursive knownRepr knownRepr obj)
         let minst = App (ProjectVariant knownRepr tag1 uobj)
         inst <- lift $ assertedJustExpr minst "putfield: not a valid class instance"
         var <-
           case J.fieldIdType fldId of
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
         let key = App (TextLit (fromString (J.fieldIdName fldId)))
         let mvar = App (JustValue knownRepr var)
         let inst' = App (InsertStringMapEntry knownRepr inst key mvar)
         let uobj' = App (InjectVariant knownRepr tag1 inst')
         let obj' = App (RollRecursive knownRepr knownRepr uobj')
         lift $ writeRef rawRef obj'
    J.Getstatic _fieldId ->
      do sgUnimplemented "getstatic" --initializeClass $ J.fieldIdClass fieldId
         --pushStaticFieldValue fieldId
    J.Putstatic fieldId ->
      do --initializeClass $ J.fieldIdClass fieldId
         _value <-
           case J.fieldIdType fieldId of
             J.BooleanType -> return . IValue . boolFromInt =<< iPop
             J.ByteType    -> return . IValue . byteFromInt =<< iPop
             J.CharType    -> return . IValue . charFromInt =<< iPop
             J.ShortType   -> return . IValue . shortFromInt =<< iPop
             _             -> popValue
         sgUnimplemented "putstatic" --setStaticFieldValue fieldId value

    -- Array creation and manipulation
    J.Newarray arrayType ->
      do count <- iPop
         let nonneg = App (BVSle w32 (iConst 0) count)
         lift $ assertExpr nonneg "java/lang/NegativeArraySizeException"
         -- FIXME: why doesn't jvm-parser just store the element type?
         case arrayType of
           J.ArrayType elemType ->
             case elemType of
               J.BooleanType -> newarrayInstr tagI count (iConst 0)
               J.ArrayType _ -> sgFail "newarray: invalid element type"
               J.ByteType    -> newarrayInstr tagI count (iConst 0)
               J.CharType    -> newarrayInstr tagI count (iConst 0)
               J.ClassType _ -> sgFail "newarray: invalid element type"
               J.DoubleType  -> newarrayInstr tagD count (dConst 0)
               J.FloatType   -> newarrayInstr tagF count (fConst 0)
               J.IntType     -> newarrayInstr tagI count (iConst 0)
               J.LongType    -> newarrayInstr tagL count (lConst 0)
               J.ShortType   -> newarrayInstr tagI count (iConst 0)
           _ -> sgFail "newarray: expected array type"
    J.Multianewarray _elemType dimensions ->
      do counts <- reverse <$> sequence (replicate (fromIntegral dimensions) iPop)
         forM_ counts $ \count -> do
           let nonneg = App (BVSle w32 (iConst 0) count)
           lift $ assertExpr nonneg "java/lang/NegativeArraySizeException"
         sgUnimplemented "multianewarray" --pushValue . RValue =<< newMultiArray arrayType counts

    -- Load an array component onto the operand stack
    J.Baload -> aloadInstr tagI IValue -- byte
    J.Caload -> aloadInstr tagI IValue -- char
    J.Saload -> aloadInstr tagI IValue -- short
    J.Iaload -> aloadInstr tagI IValue
    J.Laload -> aloadInstr tagL LValue
    J.Faload -> aloadInstr tagF FValue
    J.Daload -> aloadInstr tagD DValue
    J.Aaload -> aloadInstr tagR RValue

    -- Store a value from the operand stack as an array component
    J.Bastore -> iPop >>= astoreInstr tagI byteFromInt
    J.Castore -> iPop >>= astoreInstr tagI charFromInt
    J.Sastore -> iPop >>= astoreInstr tagI shortFromInt
    J.Iastore -> iPop >>= astoreInstr tagI id
    J.Lastore -> lPop >>= astoreInstr tagL id
    J.Fastore -> fPop >>= astoreInstr tagF id
    J.Dastore -> dPop >>= astoreInstr tagD id
    J.Aastore -> rPop >>= astoreInstr tagR id

    -- Stack management instructions
    J.Pop ->
      do void popType1
    J.Pop2 ->
      do void popType2
    J.Dup ->
      do value <- popType1
         pushValue value
         pushValue value
    J.Dup_x1 ->
      do value1 <- popType1
         value2 <- popType1
         pushValue value1
         pushValue value2
         pushValue value1
    J.Dup_x2 ->
      do value1 <- popType1
         value2 <- popType2
         pushValue value1
         pushValues value2
         pushValue value1
    J.Dup2 ->
      do value <- popType2
         pushValues value
         pushValues value
    J.Dup2_x1 ->
      do value1 <- popType2
         value2 <- popType1
         pushValues value1
         pushValue value2
         pushValues value1
    J.Dup2_x2 ->
      do value1 <- popType2
         value2 <- popType2
         pushValues value1
         pushValues value2
         pushValues value1
    J.Swap ->
      do value1 <- popType1
         value2 <- popType1
         pushValue value1
         pushValue value2

    -- Conditional branch instructions
    J.If_acmpeq pc' ->
      do r2 <- rPop
         r1 <- rPop
         eq <- lift $ rEqual r1 r2
         pc'' <- nextPC pc
         branchIf eq pc' pc''
    J.If_acmpne pc' ->
      do r2 <- rPop
         r1 <- rPop
         eq <- lift $ rEqual r1 r2
         pc'' <- nextPC pc
         branchIf (App (Not eq)) pc' pc''
    J.Ifnonnull pc' ->
      do r <- rPop
         n <- lift $ rIsNull r
         pc'' <- nextPC pc
         branchIf (App (Not n)) pc' pc''
    J.Ifnull pc' ->
      do r <- rPop
         n <- lift $ rIsNull r
         pc'' <- nextPC pc
         branchIf n pc' pc''

    J.If_icmpeq pc' -> icmpInstr pc pc' $ \a b -> App (BVEq w32 a b)
    J.If_icmpne pc' -> icmpInstr pc pc' $ \a b -> App (Not (App (BVEq w32 a b)))
    J.If_icmplt pc' -> icmpInstr pc pc' $ \a b -> App (BVSlt w32 a b)
    J.If_icmpge pc' -> icmpInstr pc pc' $ \a b -> App (BVSle w32 b a)
    J.If_icmpgt pc' -> icmpInstr pc pc' $ \a b -> App (BVSlt w32 b a)
    J.If_icmple pc' -> icmpInstr pc pc' $ \a b -> App (BVSle w32 a b)

    J.Ifeq pc' -> ifInstr pc pc' $ \a -> App (Not (App (BVNonzero w32 a)))
    J.Ifne pc' -> ifInstr pc pc' $ \a -> App (BVNonzero w32 a)
    J.Iflt pc' -> ifInstr pc pc' $ \a -> App (BVSlt w32 a iZero)
    J.Ifge pc' -> ifInstr pc pc' $ \a -> App (BVSle w32 iZero a)
    J.Ifgt pc' -> ifInstr pc pc' $ \a -> App (BVSlt w32 iZero a)
    J.Ifle pc' -> ifInstr pc pc' $ \a -> App (BVSle w32 a iZero)

    J.Tableswitch pc' lo _hi pcs ->
      do iPop >>= switchInstr pc' (zip [lo ..] pcs)
    J.Lookupswitch pc' table ->
      do iPop >>= switchInstr pc' table
    J.Goto pc' ->
      do vs <- get
         lbl <- lift $ processBlockAtPC pc' vs
         lift $ jump lbl
    J.Jsr _pc' -> sgFail "generateInstruction: jsr/ret not supported"
    J.Ret _idx -> sgFail "ret" --warning "jsr/ret not implemented"

    -- Method invocation and return instructions
    J.Invokevirtual   _type      _methodKey -> sgUnimplemented "Invokevirtual"
    J.Invokeinterface _className _methodKey -> sgUnimplemented "Invokeinterface"
    J.Invokespecial   _type      _methodKey -> sgUnimplemented "Invokespecial"
    J.Invokestatic    className methodKey ->
      do ctx <- lift $ gets jsContext
         let mhandle = Map.lookup (className, methodKey) (symbolMap ctx)
         case mhandle of
           Nothing -> sgFail "invokestatic: method not found"
           Just handle -> callJVMHandle handle
    J.Invokedynamic   _word16 -> sgUnimplemented "Invokedynamic"

    J.Ireturn -> returnInstr iPop
    J.Lreturn -> returnInstr lPop
    J.Freturn -> returnInstr fPop
    J.Dreturn -> returnInstr dPop
    J.Areturn -> returnInstr rPop
    J.Return  -> returnInstr (return (App EmptyApp))

    -- Other XXXXX
    J.Aconst_null ->
      do rPush rNull
    J.Arraylength ->
      do arrayRef <- rPop
         rawRef <- throwIfRefNull arrayRef
         obj <- lift $ readRef rawRef
         let uobj = App (UnrollRecursive knownRepr knownRepr obj)
         len <- lift $
           do k <- newLambdaLabel
              l1 <- newLambdaLabel
              l2 <- newLambdaLabel
              defineLambdaBlock l1 (\_ -> reportError (App (TextLit "arraylength")))
              defineLambdaBlock l2 (jumpToLambda k . arrayLength)
              let labels = Ctx.empty `Ctx.extend` l1 `Ctx.extend` l2
              continueLambda k (branchVariant uobj labels)
         iPush len
    J.Athrow ->
      do _objectRef <- rPop
         -- For now, we assert that exceptions won't happen
         lift $ reportError (App (TextLit "athrow"))
         --throwIfRefNull objectRef
         --throw objectRef
    J.Checkcast _tp ->
      do objectRef <- rPop
         () <- sgUnimplemented "checkcast" --assertTrueM (isNull objectRef ||| objectRef `hasType` tp) "java/lang/ClassCastException"
         rPush objectRef
    J.Iinc idx constant ->
      do value <- getLocal idx >>= fromIValue
         let constValue = iConst (fromIntegral constant)
         setLocal idx (IValue (App (BVAdd w32 value constValue)))
    J.Instanceof _tp ->
      do _objectRef <- rPop
         sgUnimplemented "instanceof" -- objectRef `instanceOf` tp
    J.Monitorenter ->
      do void rPop
    J.Monitorexit ->
      do void rPop
    J.Nop ->
      do return ()

unary ::
  JVMStmtGen h s ret a ->
  (b -> JVMStmtGen h s ret ()) ->
  (a -> b) ->
  JVMStmtGen h s ret ()
unary pop push op =
  do value <- pop
     push (op value)

binary ::
  JVMStmtGen h s ret a ->
  JVMStmtGen h s ret b ->
  (c -> JVMStmtGen h s ret ()) ->
  (a -> b -> c) ->
  JVMStmtGen h s ret ()
binary pop1 pop2 push op =
  do value2 <- pop2
     value1 <- pop1
     push (value1 `op` value2)

newarrayInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  JVMInt s ->
  Expr JVM s t ->
  JVMStmtGen h s ret ()
newarrayInstr tag count x =
  do let val = App (InjectVariant knownRepr tag x)
     let vec = App (VectorReplicate knownRepr (App (BvToNat w32 count)) val)
     let ctx = Ctx.empty `Ctx.extend` count `Ctx.extend` vec
     let arr = App (MkStruct knownRepr ctx)
     let uobj = App (InjectVariant knownRepr tag2 arr)
     let obj = App (RollRecursive knownRepr knownRepr uobj)
     rawRef <- lift $ newRef obj
     let ref = App (JustValue knownRepr rawRef)
     rPush ref

aloadInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  (Expr JVM s t -> JVMValue s) ->
  JVMStmtGen h s ret ()
aloadInstr tag mkVal =
  do idx <- iPop
     arrayRef <- rPop
     rawRef <- throwIfRefNull arrayRef
     obj <- lift $ readRef rawRef
     let uobj = App (UnrollRecursive knownRepr knownRepr obj)
     let marr = App (ProjectVariant knownRepr tag2 uobj)
     arr <- lift $ assertedJustExpr marr "aload: not a valid array"
     let vec = App (GetStruct arr tag2 knownRepr)
     -- TODO: assert 0 <= idx < length arr
     let val = App (VectorGetEntry knownRepr vec (App (BvToNat w32 idx)))
     let mx = App (ProjectVariant knownRepr tag val)
     x <- lift $ assertedJustExpr mx "aload: invalid element type"
     pushValue (mkVal x)

astoreInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  (Expr JVM s t -> Expr JVM s t) ->
  Expr JVM s t ->
  JVMStmtGen h s ret ()
astoreInstr tag f x =
  do idx <- iPop
     arrayRef <- rPop
     rawRef <- throwIfRefNull arrayRef
     obj <- lift $ readRef rawRef
     let uobj = App (UnrollRecursive knownRepr knownRepr obj)
     let marr = App (ProjectVariant knownRepr tag2 uobj)
     arr <- lift $ assertedJustExpr marr "astore: not a valid array"
     let vec = App (GetStruct arr tag2 knownRepr)
     -- TODO: assert 0 <= idx < length arr
     let val = App (InjectVariant knownRepr tag (f x))
     let vec' = App (VectorSetEntry knownRepr vec (App (BvToNat w32 idx)) val)
     let arr' = App (SetStruct knownRepr arr tag2 vec')
     let uobj' = App (InjectVariant knownRepr tag2 arr')
     let obj' = App (RollRecursive knownRepr knownRepr uobj')
     lift $ writeRef rawRef obj'

icmpInstr ::
  J.PC {- ^ previous PC -} ->
  J.PC {- ^ branch target -} ->
  (JVMInt s -> JVMInt s -> JVMBool s) ->
  JVMStmtGen h s ret ()
icmpInstr pc_old pc_t cmp =
  do i2 <- iPop
     i1 <- iPop
     pc_f <- nextPC pc_old
     branchIf (cmp i1 i2) pc_t pc_f

ifInstr ::
  J.PC {- ^ previous PC -} ->
  J.PC {- ^ branch target -} ->
  (JVMInt s -> JVMBool s) ->
  JVMStmtGen h s ret ()
ifInstr pc_old pc_t cmp =
  do i <- iPop
     pc_f <- nextPC pc_old
     branchIf (cmp i) pc_t pc_f

branchIf ::
  JVMBool s ->
  J.PC {- ^ true label -} ->
  J.PC {- ^ false label -} ->
  JVMStmtGen h s ret ()
branchIf cond pc_t pc_f =
  do vs <- get
     lbl_t <- lift $ processBlockAtPC pc_t vs
     lbl_f <- lift $ processBlockAtPC pc_f vs
     lift $ branch cond lbl_t lbl_f

switchInstr ::
  J.PC {- ^ default target -} ->
  [(Int32, J.PC)] {- ^ jump table -} ->
  JVMInt s {- ^ scrutinee -} ->
  JVMStmtGen h s ret ()
switchInstr def [] _ =
  do vs <- get
     lift $ processBlockAtPC def vs >>= jump
switchInstr def ((i, pc) : table) x =
  do vs <- get
     l <- lift $ processBlockAtPC pc vs
     let cond = App (BVEq w32 x (iConst (toInteger i)))
     lift $ whenCond cond (jump l)
     switchInstr def table x

returnInstr ::
  forall h s ret tp.
  KnownRepr TypeRepr tp =>
  JVMStmtGen h s ret (Expr JVM s tp) ->
  JVMStmtGen h s ret ()
returnInstr pop =
  do retType <- lift $ jsRetType <$> get
     case testEquality retType (knownRepr :: TypeRepr tp) of
       Just Refl -> pop >>= (lift . returnFromFunction)
       Nothing -> sgFail "ireturn: type mismatch"

----------------------------------------------------------------------
-- Basic Value Operations

charFromInt :: JVMInt s -> JVMInt s
charFromInt i = App (BVZext w32 w16 (App (BVTrunc w16 w32 i)))

floatFromDouble :: JVMDouble s -> JVMFloat s
floatFromDouble _ = error "floatFromDouble"

intFromDouble :: JVMDouble s -> JVMInt s
intFromDouble _ = error "intFromDouble"

longFromDouble :: JVMDouble s -> JVMLong s
longFromDouble _ = error "longFromDouble"

doubleFromFloat :: JVMFloat s -> JVMDouble s
doubleFromFloat _ = error "doubleFromFloat"

intFromFloat :: JVMFloat s -> JVMInt s
intFromFloat _ = error "intFromFloat"

longFromFloat :: JVMFloat s -> JVMLong s
longFromFloat _ = error "longFromFloat"

boolFromInt :: JVMInt s -> JVMInt s
boolFromInt _ = error "boolFromInt"

byteFromInt :: JVMInt s -> JVMInt s
byteFromInt i = App (BVSext w32 w8 (App (BVTrunc w8 w32 i)))

doubleFromInt :: JVMInt s -> JVMDouble s
doubleFromInt _ = error "doubleFromInt"

floatFromInt :: JVMInt s -> JVMFloat s
floatFromInt _ = error "floatFromInt"

longFromInt :: JVMInt s -> JVMLong s
longFromInt _ = error "longFromInt"

shortFromInt :: JVMInt s -> JVMInt s
shortFromInt i = App (BVSext w32 w16 (App (BVTrunc w16 w32 i)))

doubleFromLong :: JVMLong s -> JVMDouble s
doubleFromLong _ = error "doubleFromLong"

floatFromLong :: JVMLong s -> JVMFloat s
floatFromLong _ = error "floatFromLong"

intFromLong :: JVMLong s -> JVMInt s
intFromLong _ = error "intFromLong"

iConst :: Integer -> JVMInt s
iConst i = App (BVLit w32 i)

lConst :: Integer -> JVMLong s
lConst i = App (BVLit w64 i)

dConst :: Double -> JVMDouble s
dConst _ = error "dConst"

fConst :: Float -> JVMFloat s
fConst _ = error "fConst"

dAdd, dSub, dMul, dDiv, dRem :: JVMDouble s -> JVMDouble s -> JVMDouble s
dAdd = error "dAdd"
dSub = error "dAdd"
dMul = error "dAdd"
dDiv = error "dAdd"
dRem = error "dAdd"

dNeg :: JVMDouble s -> JVMDouble s
dNeg = error "dNeg"

fAdd, fSub, fMul, fDiv, fRem :: JVMFloat s -> JVMFloat s -> JVMFloat s
fAdd = error "dAdd"
fSub = error "dAdd"
fMul = error "dAdd"
fDiv = error "dAdd"
fRem = error "dAdd"

----------------------------------------------------------------------

-- | Given a JVM type and a type context and a register assignment,
-- peel off the rightmost register from the assignment, which is
-- expected to match the given LLVM type. Pass the register and the
-- remaining type and register context to the given continuation.
--
-- This procedure is used to set up the initial state of the registers
-- at the entry point of a function.
packTypes ::
  [J.Type] ->
  CtxRepr ctx ->
  Ctx.Assignment (Atom s) ctx ->
  [JVMValue s]
packTypes [] ctx _asgn
  | Ctx.null ctx = []
  | otherwise = error "packTypes: arguments do not match JVM types"
packTypes (t : ts) ctx asgn =
  jvmTypeAsRepr t $ \mkVal ctp ->
  case ctx of
    ctx' Ctx.:> ctp' ->
      case testEquality ctp ctp' of
        Nothing -> error $ unwords ["crucible type mismatch", show ctp, show ctp']
        Just Refl ->
          mkVal (AtomExpr (Ctx.last asgn)) : packTypes ts ctx' (Ctx.init asgn)
  where
    jvmTypeAsRepr ::
      J.Type ->
      (forall tp. (Expr JVM s tp -> JVMValue s) -> TypeRepr tp -> [JVMValue s]) ->
      [JVMValue s]
    jvmTypeAsRepr ty k =
      case ty of
        J.ArrayType _ -> k RValue (knownRepr :: TypeRepr JVMRefType)
        J.BooleanType -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.ByteType    -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.CharType    -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.ClassType _ -> k RValue (knownRepr :: TypeRepr JVMRefType)
        J.DoubleType  -> k DValue (knownRepr :: TypeRepr JVMDoubleType)
        J.FloatType   -> k FValue (knownRepr :: TypeRepr JVMFloatType)
        J.IntType     -> k IValue (knownRepr :: TypeRepr JVMIntType)
        J.LongType    -> k LValue (knownRepr :: TypeRepr JVMLongType)
        J.ShortType   -> k IValue (knownRepr :: TypeRepr JVMIntType)

initialJVMExprFrame ::
  J.ClassName ->
  J.Method ->
  CtxRepr ctx ->
  Ctx.Assignment (Atom s) ctx ->
  JVMExprFrame s
initialJVMExprFrame cn method ctx asgn = JVMFrame [] locals
  where
    args = J.methodParameterTypes method
    static = J.methodIsStatic method
    args' = if static then args else J.ClassType cn : args
    vals = reverse (packTypes (reverse args') ctx asgn)
    idxs = J.methodParameterIndexes method
    idxs' = if static then idxs else 0 : idxs
    locals = Map.fromList (zip idxs' vals)

----------------------------------------------------------------------

-- | Build the initial JVM generator state upon entry to to the entry
-- point of a method.
initialState :: JVMContext -> J.Method -> TypeRepr ret -> JVMState ret s
initialState ctx method ret =
  JVMState {
    _jsLabelMap = Map.empty,
    _jsFrameMap = Map.empty,
    _jsCFG = methodCFG method,
    jsRetType = ret,
    jsContext = ctx
  }

methodCFG :: J.Method -> J.CFG
methodCFG method =
  case J.methodBody method of
    J.Code _ _ cfg _ _ _ _ -> cfg
    _                      -> error ("Method " ++ show method ++ " has no body")

generateMethod ::
  J.ClassName ->
  J.Method ->
  CtxRepr init ->
  Ctx.Assignment (Atom s) init ->
  JVMGenerator h s ret a
generateMethod cn method ctx asgn =
  do let cfg = methodCFG method
     let bbLabel bb = (,) (J.bbId bb) <$> newLabel
     lbls <- traverse bbLabel (J.allBBs cfg)
     jsLabelMap .= Map.fromList lbls
     bb0 <- maybe (jvmFail "no entry block") return (J.bbById cfg J.BBIdEntry)
     let vs0 = initialJVMExprFrame cn method ctx asgn
     rs0 <- newRegisters vs0
     generateBasicBlock bb0 rs0

-- | Translate a single JVM method into a crucible CFG.
defineMethod ::
  JVMContext -> J.ClassName -> J.Method -> ST h (C.AnyCFG JVM)
defineMethod ctx cn method =
  case Map.lookup (cn, J.methodKey method) (symbolMap ctx) of
    Nothing -> fail "internal error: Could not find method"
    Just (JVMHandleInfo _ (h :: FnHandle args ret)) ->
      do let argTypes = handleArgTypes h
         let retType  = handleReturnType h
         let def :: FunctionDef JVM h (JVMState ret) args ret
             def inputs = (s, f)
               where s = initialState ctx method retType
                     f = generateMethod cn method argTypes inputs
         (SomeCFG g, []) <- defineFunction InternalPos h def
         case toSSA g of
           C.SomeCFG g_ssa -> return (C.AnyCFG g_ssa)

-- | Define a block with a fresh lambda label, returning the label.
defineLambdaBlockLabel ::
  (IsSyntaxExtension ext, KnownRepr TypeRepr tp) =>
  (forall a. Expr ext s tp -> Generator ext h s t ret a) ->
  Generator ext h s t ret (LambdaLabel s tp)
defineLambdaBlockLabel action =
  do l <- newLambdaLabel
     defineLambdaBlock l action
     return l
