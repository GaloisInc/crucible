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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -haddock #-}

module Lang.Crucible.JVM.Translation where

import Control.Monad.State.Strict
import Control.Lens hiding (op, (:>))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.Types

-------------------------------------------------------------------------
-- JVMValue

-- | JVM extension.
type JVM = () -- TODO

type JVMObjectType = UnitType -- FIXME: This should be a CrucibleType
                              -- representation of JVM objects

type JVMDoubleType = FloatType DoubleFloat
type JVMFloatType  = FloatType SingleFloat
type JVMIntType    = BVType 32
type JVMLongType   = BVType 64
type JVMRefType    = MaybeType (ReferenceType JVMObjectType)


type JVMBool   s = Expr JVM s BoolType
type JVMDouble s = Expr JVM s JVMDoubleType
type JVMFloat  s = Expr JVM s JVMFloatType
type JVMInt    s = Expr JVM s JVMIntType
type JVMLong   s = Expr JVM s JVMLongType
type JVMRef    s = Expr JVM s JVMRefType

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

------------------------------------------------------------------------
-- JVMState

data JVMState ret s
  = JVMState
  { _jsLabelMap :: !(Map J.BBId (Label s))
  , _jsFrameMap :: !(Map J.BBId (JVMFrame (JVMReg s)))
  , _jsCFG :: J.CFG
  , jsRetType :: TypeRepr ret
    -- TODO: add JVM context stuff here (maybe Codebase?)
  }

jsLabelMap :: Simple Lens (JVMState ret s) (Map J.BBId (Label s))
jsLabelMap = lens _jsLabelMap (\s v -> s { _jsLabelMap = v })

jsFrameMap :: Simple Lens (JVMState ret s) (Map J.BBId (JVMFrame (JVMReg s)))
jsFrameMap = lens _jsFrameMap (\s v -> s { _jsFrameMap = v })

jsCFG :: Simple Lens (JVMState ret s) J.CFG
jsCFG = lens _jsCFG (\s v -> s { _jsCFG = v })

type JVMGenerator h s ret = Generator JVM h s (JVMState ret) ret

-- | Indicate that CFG generation failed due to ill-formed JVM code.
jvmFail :: Monad m => String -> m a
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
saveLocals rs vs = undefined rs vs

newRegisters :: JVMExprFrame s -> JVMGenerator h s ret (JVMRegisters s)
newRegisters = traverse newJVMReg

readRegisters :: JVMRegisters s -> JVMGenerator h s ret (JVMExprFrame s)
readRegisters = traverse readJVMReg

writeRegisters :: JVMRegisters s -> JVMExprFrame s -> JVMGenerator h s ret ()
writeRegisters rs vs =
  do saveStack (rs^.operandStack) (vs^.operandStack)
     saveLocals (rs^.localVariables) (vs^.localVariables)

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
     fail "generateBasicBlock: unreachable"

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

getStack :: JVMStmtGen h s ret [JVMValue s]
getStack = use operandStack

putStack :: [JVMValue s] -> JVMStmtGen h s ret ()
putStack vs = operandStack .= vs

popValue :: JVMStmtGen h s ret (JVMValue s)
popValue =
  do vs <- getStack
     case vs of
       [] -> jvmFail "popValue: empty stack"
       (v : vs') ->
         do putStack vs'
            return v

pushValue :: JVMValue s -> JVMStmtGen h s ret ()
pushValue v =
  do vs <- getStack
     putStack (v : vs)

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
     if isType1 v then return v else jvmFail "popType1"

popType2 :: JVMStmtGen h s ret [JVMValue s]
popType2 =
  do vs <- getStack
     case vs of
       v : vs' | isType2 v ->
         putStack vs' >> return [v]
       v1 : v2 : vs' | isType1 v1 && isType1 v2 ->
         putStack vs' >> return [v1, v2]
       _ ->
         jvmFail "popType2"

iPop :: JVMStmtGen h s ret (JVMInt s)
iPop =
  do v <- popValue
     case v of
       IValue i -> return i
       _ -> jvmFail "iPop"

lPop :: JVMStmtGen h s ret (JVMLong s)
lPop =
  do v <- popValue
     case v of
       LValue l -> return l
       _ -> jvmFail "lPop"

rPop :: JVMStmtGen h s ret (JVMRef s)
rPop =
  do v <- popValue
     case v of
       RValue r -> return r
       _ -> jvmFail "rPop"

dPop :: JVMStmtGen h s ret (JVMDouble s)
dPop =
  do v <- popValue
     case v of
       DValue d -> return d
       _ -> jvmFail "dPop"

fPop :: JVMStmtGen h s ret (JVMFloat s)
fPop =
  do v <- popValue
     case v of
       FValue f -> return f
       _ -> jvmFail "fPop"

iPush :: JVMInt s -> JVMStmtGen h s ret ()
iPush i = pushValue (IValue i)

lPush :: JVMLong s -> JVMStmtGen h s ret ()
lPush l = pushValue (LValue l)

fPush :: JVMFloat s -> JVMStmtGen h s ret ()
fPush f = pushValue (FValue f)

dPush :: JVMDouble s -> JVMStmtGen h s ret ()
dPush d = pushValue (DValue d)

guardArray :: JVMRef s -> JVMInt s -> JVMStmtGen h s ret ()
guardArray _ _ = fail "guardArray"

pushArrayValue :: JVMRef s -> JVMInt s -> JVMStmtGen h s ret ()
pushArrayValue _ _ = fail "pushArrayValue"

assertTrueM :: t0 -> [Char] -> JVMStmtGen h s ret ()
assertTrueM _ _ = fail "assertTrueM"

isValidEltOfArray :: JVMRef s -> JVMRef s -> t0
isValidEltOfArray _ _ = error "isValidEltOfArray"

setArrayValue :: JVMRef s -> JVMInt s -> t1 -> JVMStmtGen h s ret ()
setArrayValue _ _ _ = fail "setArrayValue"

getLocal :: J.LocalVariableIndex -> JVMStmtGen h s ret (JVMValue s)
getLocal _ = fail "getLocal"

throwIfRefNull :: JVMRef s -> JVMStmtGen h s ret ()
throwIfRefNull _ = fail "throwIfRefNull"

arrayLength :: JVMRef s -> JVMStmtGen h s ret (JVMInt s)
arrayLength _ = fail "arrayLength"

setLocal :: J.LocalVariableIndex -> JVMValue s -> JVMStmtGen h s ret ()
setLocal _ _ = fail "setLocal"

throw :: JVMRef s -> JVMStmtGen h s ret ()
throw _ = fail "throw"

byteArrayVal :: JVMRef s -> JVMInt s -> JVMStmtGen h s ret (JVMInt s0)
byteArrayVal _ _ = fail "byteArrayVal"

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
       Nothing -> fail "nextPC"
       Just pc' -> return pc'

----------------------------------------------------------------------

-- | Do the heavy lifting of translating JVM instructions to crucible code.
generateInstruction ::
  forall h s ret.
  (J.PC, J.Instruction) {- ^ instruction to translate -} ->
  JVMStmtGen h s ret ()
generateInstruction {-lab-} (pc, instr) =
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
        J.String _v  -> fail "ldc string" -- pushValue . RValue =<< refFromString v
        J.ClassRef _ -> fail "ldc class" -- pushValue . RValue =<< getClassObject c

    -- Object creation and manipulation
    J.New _name ->
      do fail "new" -- pushValue . RValue =<< newObject name
    J.Newarray _arrayType ->
      do _count <- iPop
         fail "newarray" --assertFalseM (count `iLt` iConst 0) "java/lang/NegativeArraySizeException"
         --pushValue . RValue =<< newMultiArray arrayType [count]
    J.Multianewarray _arrayType dimensions ->
      do counts <- return . reverse =<< sequence (replicate (fromIntegral dimensions) iPop)
         forM_ counts $ \_count -> do
           fail "multianewarray" -- assertFalseM (count `iLt` iConst 0) "java/lang/NegativeArraySizeException"
         fail "multianewarray" --pushValue . RValue =<< newMultiArray arrayType counts
    J.Getfield _fldId ->
      do objectRef <- rPop
         throwIfRefNull objectRef
         fail "getfield" --cb <- getCodebase
         --pushInstanceFieldValue objectRef =<< liftIO (locateField cb fldId)
    J.Getstatic _fieldId ->
      do fail "getstatic" --initializeClass $ J.fieldIdClass fieldId
         --pushStaticFieldValue fieldId
    J.Putfield fldId ->
      do val <- popValue
         objectRef <- rPop
         throwIfRefNull objectRef
         --cb <- getCodebase
         _value <- case (J.fieldIdType fldId, val) of
                     (J.BooleanType, IValue i) -> return (IValue (boolFromInt  i))
                     (J.ByteType,    IValue i) -> return (IValue (byteFromInt  i))
                     (J.CharType,    IValue i) -> return (IValue (charFromInt  i))
                     (J.ShortType,   IValue i) -> return (IValue (shortFromInt i))
                     _ -> return val
         fail "putfield" --fld <- liftIO $ locateField cb fldId
         --fail "putfield" --setInstanceFieldValue objectRef fld value
    J.Putstatic fieldId ->
      do --initializeClass $ J.fieldIdClass fieldId
         _value <-
           case J.fieldIdType fieldId of
             J.BooleanType -> return . IValue . boolFromInt =<< iPop
             J.ByteType    -> return . IValue . byteFromInt =<< iPop
             J.CharType    -> return . IValue . charFromInt =<< iPop
             J.ShortType   -> return . IValue . shortFromInt =<< iPop
             _             -> popValue
         fail "putstatic" --setStaticFieldValue fieldId value

    -- Load an array component onto the operand stack
    J.Baload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Caload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Saload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Iaload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Laload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Faload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Daload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx
    J.Aaload ->
      do idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         pushArrayValue arrayRef idx

    -- Store a value from the operand stack as an array component
    J.Bastore ->
      do value <- iPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         fixedVal <- byteArrayVal arrayRef value
         setArrayValue arrayRef idx (IValue fixedVal)
    J.Castore ->
      do value <- iPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         setArrayValue arrayRef idx (IValue (charFromInt value))
    J.Sastore ->
      do value <- iPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         setArrayValue arrayRef idx (IValue (shortFromInt value))
    J.Iastore ->
      do value <- iPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         setArrayValue arrayRef idx (IValue value)
    J.Lastore ->
      do value <- lPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         setArrayValue arrayRef idx (LValue value)
    J.Fastore ->
      do value <- fPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         setArrayValue arrayRef idx (FValue value)
    J.Dastore ->
      do value <- dPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         setArrayValue arrayRef idx (DValue value)
    J.Aastore ->
      do value <- rPop
         idx <- iPop
         arrayRef <- rPop
         guardArray arrayRef idx
         assertTrueM (isValidEltOfArray value arrayRef) "java/lang/ArrayStoreException"
         setArrayValue arrayRef idx (RValue value)

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

    J.Tableswitch {} -> undefined -- PC Int32 Int32 [PC]
    J.Lookupswitch {} -> undefined -- PC {-default -} [(Int32,PC)] {- (key, target) -}
    J.Goto pc' ->
      do vs <- get
         lbl <- lift $ processBlockAtPC pc' vs
         lift $ jump lbl
    J.Jsr _pc' -> fail "generateInstruction: jsr/ret not supported"
    J.Ret _idx -> fail "ret" --warning "jsr/ret not implemented"

    -- Method invocation and return instructions
    J.Invokevirtual   _type      _methodKey -> undefined
    J.Invokeinterface _className _methodKey -> undefined
    J.Invokespecial   _type      _methodKey -> undefined
    J.Invokestatic    _className _methodKey -> undefined
    J.Invokedynamic   _word16 -> undefined

    J.Ireturn -> returnInstr iPop
    J.Lreturn -> returnInstr lPop
    J.Freturn -> returnInstr fPop
    J.Dreturn -> returnInstr dPop
    J.Areturn -> returnInstr rPop
    J.Return  -> returnInstr (return (App EmptyApp))

    -- Other XXXXX
    J.Aconst_null ->
      do pushValue (RValue rNull)
    J.Arraylength ->
      do arrayRef <- rPop
         throwIfRefNull arrayRef
         iPush =<< arrayLength arrayRef
    J.Athrow ->
      do _objectRef <- rPop
         -- For now, we assert that exceptions won't happen
         lift $ reportError (App (TextLit "athrow"))
         --throwIfRefNull objectRef
         --throw objectRef
    J.Checkcast _tp ->
      do objectRef <- rPop
         () <- fail "checkcast" --assertTrueM (isNull objectRef ||| objectRef `hasType` tp) "java/lang/ClassCastException"
         pushValue $ RValue objectRef
    J.Iinc idx constant ->
      do IValue value <- getLocal idx -- FIXME: pattern binding may fail
         let constValue = iConst (fromIntegral constant)
         setLocal idx (IValue (App (BVAdd w32 value constValue)))
    J.Instanceof _tp ->
      do _objectRef <- rPop
         fail "instanceof" -- objectRef `instanceOf` tp
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

returnInstr ::
  forall h s ret tp.
  KnownRepr TypeRepr tp =>
  JVMStmtGen h s ret (Expr JVM s tp) ->
  JVMStmtGen h s ret ()
returnInstr pop =
  do retType <- lift $ jsRetType <$> get
     case testEquality retType (knownRepr :: TypeRepr tp) of
       Just Refl -> pop >>= (lift . returnFromFunction)
       Nothing -> fail "ireturn: type mismatch"

----------------------------------------------------------------------
-- Basic Value Operations

charFromInt :: JVMInt s -> JVMInt s
charFromInt _ = error "charFromInt"

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
byteFromInt _ = error "byteFromInt"

doubleFromInt :: JVMInt s -> JVMDouble s
doubleFromInt _ = error "doubleFromInt"

floatFromInt :: JVMInt s -> JVMFloat s
floatFromInt _ = error "floatFromInt"

longFromInt :: JVMInt s -> JVMLong s
longFromInt _ = error "longFromInt"

shortFromInt :: JVMInt s -> JVMInt s
shortFromInt _ = error "shortFromInt"

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
