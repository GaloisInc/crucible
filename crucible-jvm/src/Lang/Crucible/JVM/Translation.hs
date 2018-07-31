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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -haddock #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Lang.Crucible.JVM.Translation
  (
    module Lang.Crucible.JVM.Types
  , module Lang.Crucible.JVM.Generator
  , module Lang.Crucible.JVM.Class
  , module Lang.Crucible.JVM.Translation
  )
  where

-- base
import Data.Maybe (isJust, fromJust)
import Data.Semigroup(Semigroup(..),(<>))
import Control.Monad.State.Strict
import Control.Monad.ST
import Control.Monad.Reader
import Control.Lens hiding (op, (:>))
import Data.Int (Int32)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Vector(Vector)
import qualified Data.Vector as V
import Data.String (fromString)
import Data.Text (Text)
import Data.Word

import System.IO

-- jvm-parser
import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr as NR

-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Backend
import           Lang.Crucible.Panic

import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState   as C
import qualified Lang.Crucible.Simulator.OverrideSim   as C
import qualified Lang.Crucible.Simulator.RegValue      as C
import qualified Lang.Crucible.Simulator.Frame         as C
import qualified Lang.Crucible.Simulator.RegMap        as C

import qualified Lang.Crucible.Analysis.Postdom        as C
import qualified Lang.Crucible.Utils.MuxTree           as C

-- what4
import           What4.ProgramLoc (Position(InternalPos))
import           What4.Interface (IsExprBuilder)
import           What4.FunctionName (FunctionName(..))
import qualified What4.Interface                       as W4
import qualified What4.Partial                         as W4

import           What4.Utils.MonadST (liftST)

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.ClassRefs
import           Lang.Crucible.JVM.Generator
import           Lang.Crucible.JVM.Class

import Debug.Trace


---------------------------------------------------------------------------------
-- | Working with JVM objects

-- | Construct a new JVM object instance, given the class data structure
-- and the list of fields
newInstanceInstr ::
  JVMClass s 
  -- ^ class data structure
  ->  [J.Field]
  -- ^ Fields
  ->  JVMGenerator h s ret (JVMObject s) 
newInstanceInstr cls fields = do
    objFields <- mapM createField fields
    let strMap = foldr addField (App (EmptyStringMap knownRepr)) objFields
    let ctx    = Ctx.empty `Ctx.extend` strMap `Ctx.extend` cls
    let inst   = App (MkStruct knownRepr ctx)
    let uobj   = injectVariant Ctx.i1of2 inst
    return $ App (RollRecursive knownRepr knownRepr uobj)
  where
    createField field = do
      let str  = App (TextLit (fromString (J.fieldName field)))
      let expr = valueToExpr (defaultValue (J.fieldType field))
      let val  = App $ JustValue knownRepr expr
      return (str, val)
    addField (f,i) fs = 
      App (InsertStringMapEntry knownRepr fs f i)

-- | Access the field component of a JVM object (must be a class instance, not an array)
getInstanceFieldValue :: JVMObject s -> J.FieldId -> JVMGenerator h s ret (JVMValue s)
getInstanceFieldValue obj fieldId = do
  let uobj = App (UnrollRecursive knownRepr knownRepr obj)             
  inst <- projectVariant Ctx.i1of2 uobj
  let fields = App (GetStruct inst Ctx.i1of2 knownRepr)
  let key    = App (TextLit (fromString (J.fieldIdName fieldId)))
  let mval   = App (LookupStringMapEntry knownRepr fields key)
  dyn <- assertedJustExpr mval "getfield: field not found"
  fromJVMDynamic (J.fieldIdType fieldId) dyn

-- | Update a field of a JVM object (must be a class instance, not an array)
setInstanceFieldValue :: JVMObject s -> J.FieldId -> JVMValue s -> JVMGenerator h s ret (JVMObject s)
setInstanceFieldValue obj fieldId val = do
  let uobj   = App (UnrollRecursive knownRepr knownRepr obj)
  inst <- projectVariant Ctx.i1of2 uobj
  let fields = App (GetStruct inst Ctx.i1of2 knownRepr)
  let dyn  = valueToExpr val
  let key = App (TextLit (fromString (J.fieldIdName fieldId)))
  let mdyn = App (JustValue knownRepr dyn)
  let fields' = App (InsertStringMapEntry knownRepr fields key mdyn)
  let inst'  = App (SetStruct knownRepr inst Ctx.i1of2 fields')
  let uobj' = App (InjectVariant knownRepr Ctx.i1of2 inst')
  return $ App (RollRecursive knownRepr knownRepr uobj')

-- | Access the class table entry for the class that instantiated this instance
getJVMInstanceClass :: JVMObject s -> JVMGenerator h s ret (JVMClass s)
getJVMInstanceClass obj = do
  let uobj = App (UnrollRecursive knownRepr knownRepr obj)
  inst <- projectVariant Ctx.i1of2 uobj
  return $ App (GetStruct inst Ctx.i2of2 knownRepr)

------------------------------------------------------------------------------

-- String Creation

charLit :: Char -> Expr JVM s JVMValueType
charLit c = App (InjectVariant knownRepr tagI (App (BVLit w32 (toInteger (fromEnum c)))))

-- | Initializer for statically known string objects
-- 
refFromString ::  String -> JVMGenerator h s ret (JVMRef s)
refFromString s =  do
  
  -- create the string object
  let name = "java/lang/String"
  initializeClass name
  clsObj <-  getJVMClassByName name
  cls    <-  lookupClass name
  obj    <-  newInstanceInstr clsObj (J.classFields cls)
  rawRef <-  newRef obj
  let ref = App (JustValue knownRepr rawRef)

  -- create an array of characters
  -- TODO: Check this with unicode characters
  let chars = map charLit s
  let vec   = V.fromList chars
  let arr   = newarrayFromVec vec
  arrRef <- newRef arr

  -- It'd be preferable to use createInstance here, but the amount of
  -- infrastructure needed to create strings via the Java runtime is significant
  -- (thread local variables, character encodings, builtin unsafe operations,
  -- etc.), so we cheat and just forcibly set the (private) instance fields.
  -- We'll want want to REVISIT this in the future.
  _ <- setInstanceFieldValue
    obj
    (J.FieldId "java/lang/String" "value" J.charArrayTy)
    (RValue (App (JustValue knownRepr arrRef)))
  _ <- setInstanceFieldValue
    obj
    (J.FieldId "java/lang/String" "hash" J.IntType)
    (IValue (App (BVLit w32 0)))
  
  return ref


----------------------------------------------------------------------
-- JVMRef

rNull :: JVMRef s
rNull = App (NothingValue knownRepr)

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


-- TODO: what if we have more values? is it ok to not save them all?
-- See Java/lang/String/compareTo
saveLocals ::
  Map J.LocalVariableIndex (JVMReg s) ->
  Map J.LocalVariableIndex (JVMValue s) ->
  JVMGenerator h s ret ()
saveLocals rs vs
  | Set.fromAscList (Map.keys rs) `Set.isSubsetOf`
    Set.fromAscList (Map.keys vs) = sequence_ (Map.intersectionWith writeJVMReg rs vs)
  | otherwise                  = jvmFail $ "saveLocals:\n\t" ++ show rs ++ "\n\t" ++ show vs

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



----------------------------------------------------------------------

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
-}


-------------------------------------------------------------------------------

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
     (_, eframe) <- runStateT (mapM_ generateInstruction (J.bbInsts bb)) vs
     -- If we didn't already handle a block-terminating instruction,
     -- jump to the successor block, if there's only one.
     cfg <- use jsCFG
     case J.succs cfg (J.bbId bb) of
       [J.BBId succPC] ->
         do lbl <- processBlockAtPC succPC eframe
            _ <- jump lbl
            jvmFail "generateBasicBlock: ran off end of block"
       [] -> jvmFail "generateBasicBlock: no terminal instruction and no successor"
       _  -> jvmFail "generateBasicBlock: no terminal instruction and multiple successors"

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


iPop :: JVMStmtGen h s ret (JVMInt s)
iPop = popValue >>= lift . fromIValue

lPop :: JVMStmtGen h s ret (JVMLong s)
lPop = popValue >>= lift . fromLValue

rPop :: JVMStmtGen h s ret (JVMRef s)
rPop = popValue >>= lift . fromRValue

dPop :: JVMStmtGen h s ret (JVMDouble s)
dPop = popValue >>= lift . fromDValue

fPop :: JVMStmtGen h s ret (JVMFloat s)
fPop = popValue >>= lift . fromFValue

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

uPush :: Expr JVM s UnitType -> JVMStmtGen h s ret ()
uPush u = return ()


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

throw :: JVMRef s -> JVMStmtGen h s ret ()
throw _ = sgUnimplemented "throw"


iZero :: JVMInt s
iZero = App (BVLit w32 0)

bTrue :: JVMBool s
bTrue = App (BoolLit True)

bFalse :: JVMBool s
bFalse = App (BoolLit False)

arrayLength :: Expr JVM s JVMArrayType -> JVMInt s
arrayLength arr = App (GetStruct arr Ctx.i1of2 knownRepr)

----------------------------------------------------------------------

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
  tryPush uPush $  
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
callJVMHandle (JVMHandleInfo methodKey handle) =
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
    J.Dcmpg -> binaryGen dPop dPop iPush dCmpg
    J.Dcmpl -> binaryGen dPop dPop iPush dCmpl
    J.Fadd  -> binary fPop fPop fPush fAdd
    J.Fsub  -> binary fPop fPop fPush fSub
    J.Fneg  -> unary fPop fPush (error "fNeg")
    J.Fmul  -> binary fPop fPop fPush fMul
    J.Fdiv  -> binary fPop fPop fPush fDiv
    J.Frem  -> binary fPop fPop fPush fRem
    J.Fcmpg -> binaryGen fPop fPop iPush dCmpg
    J.Fcmpl -> binaryGen fPop fPop iPush dCmpl
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
    J.Ineg  -> unaryGen iPop iPush iNeg
    J.Iand  -> binary iPop iPop iPush (\a b -> App (BVAnd w32 a b))
    J.Ior   -> binary iPop iPop iPush (\a b -> App (BVOr  w32 a b))
    J.Ixor  -> binary iPop iPop iPush (\a b -> App (BVXor w32 a b))
    J.Ishl  -> binary iPop iPop iPush (\a b -> App (BVShl w32 a b))
    J.Ishr  -> binary iPop iPop iPush (\a b -> App (BVAshr w32 a b))
    J.Iushr -> binary iPop iPop iPush (\a b -> App (BVLshr w32 a b))
    J.Ladd  -> binary lPop lPop lPush (\a b -> App (BVAdd w64 a b))
    J.Lsub  -> binary lPop lPop lPush (\a b -> App (BVSub w64 a b))
    J.Lmul  -> binary lPop lPop lPush (\a b -> App (BVMul w64 a b))
    J.Lneg  -> unaryGen lPop lPush lNeg
    J.Ldiv  -> binary lPop lPop lPush -- TODO: why was this lPush an error?
               -- there is also a special case when when dividend is maxlong
               -- and divisor is -1 
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
    J.Lcmp  -> binaryGen lPop lPop iPush lCmp
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
        J.String v  -> pushValue . RValue =<< (lift $ refFromString v)
        J.ClassRef _ -> rPush rNull -- TODO: construct reflective class information


    -- Object creation and manipulation
    J.New name -> do
      --traceM $ "new " ++ show name
      cls    <- lift $ lookupClass name
      clsObj <- lift $ getJVMClass cls
      obj    <- lift $ newInstanceInstr clsObj (J.classFields cls)
      rawRef <- lift $ newRef obj
      let ref = App (JustValue knownRepr rawRef)
      rPush ref

    J.Getfield fieldId -> do
      --traceM $ "getfield " ++ show (J.fieldIdName fieldId)
      objectRef <- rPop
      rawRef <- throwIfRefNull objectRef
      obj <- lift $ readRef rawRef
      val <- lift $ getInstanceFieldValue obj fieldId
      pushValue val

    J.Putfield fieldId -> do
      -- traceM $ "putfield " ++ show (J.fieldIdName fieldId)
      val <- popValue
      objectRef <- rPop
      rawRef <- throwIfRefNull objectRef
      obj  <- lift $ readRef rawRef
      obj' <- lift $ setInstanceFieldValue obj fieldId val
      lift $ writeRef rawRef obj'

    J.Getstatic fieldId -> do
      val <- lift $ getStaticFieldValue fieldId
      pushValue val

    J.Putstatic fieldId -> do
      val <- popValue
      lift $ setStaticFieldValue fieldId val

    -- Array creation and manipulation
    J.Newarray arrayType ->
      do count <- iPop
         let nonneg = App (BVSle w32 (iConst 0) count)
         lift $ assertExpr nonneg "java/lang/NegativeArraySizeException"
         -- FIXME: why doesn't jvm-parser just store the element type?
         case arrayType of
           J.ArrayType elemType -> do
             -- REVISIT: old version did not allow arrays of arrays
             -- or arrays of objects. Why was that?
             -- We can disable that here if necessary by
             -- matching on the elem type
             let expr = valueToExpr $ defaultValue elemType 
             let obj = newarrayExpr count expr
             rawRef <- lift $ newRef obj
             let ref = App (JustValue knownRepr rawRef)
             rPush ref
{-             case elemType of
               J.ArrayType _ -> sgFail "newarray: invalid element type"
               J.ClassType _ -> sgFail "newarray: invalid element type" -}
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
    -- usual dynamic dispatch
    J.Invokevirtual tp@(J.ClassType className) methodKey ->
      generateInstruction (pc, J.Invokeinterface className methodKey)

    J.Invokevirtual tp@(J.ArrayType ty) methodKey ->
      sgFail $ "TODO: invoke virtual " ++ show (J.methodKeyName methodKey) ++ " unsupported for arrays"

    -- TODO: not sure what this is. 
    J.Invokevirtual   tp        _methodKey ->
      sgFail $ "Invalid static type for invokevirtual " ++ show tp 

    -- Dynamic dispatch through an interface
    J.Invokeinterface className methodKey -> do
      let mname = J.unClassName className ++ "/" ++ J.methodKeyName methodKey
      traceM $ "invoke: " ++ mname
      
      -- find the static type of the method
      let mretTy = javaTypeToRepr   <$> J.methodKeyReturnType     methodKey

      Some argRepr <- return $ javaTypesToCtxRepr $ reverse (J.methodKeyParameterTypes methodKey)
      Some retRepr <- return $ maybe (Some UnitRepr) id mretTy 

      args   <- popArguments argRepr

      objRef <- rPop

      rawRef <- throwIfRefNull objRef
      result <- lift $ do
          obj    <- readRef rawRef
          cls    <- getJVMInstanceClass obj

          let argRepr' = (Ctx.empty `Ctx.extend` (knownRepr :: TypeRepr JVMRefType))
                         Ctx.<++> argRepr 
          anym   <- findDynamicMethod cls methodKey
          fn     <- assertedJustExpr (App (UnpackAny (FunctionHandleRepr argRepr' retRepr) anym))
                        (App $ TextLit $ fromString ("invalid method type"
                                      ++ show (FunctionHandleRepr argRepr' retRepr)))
          call fn (Ctx.empty `Ctx.extend` objRef Ctx.<++> args)

      pushRet retRepr result
      traceM $ "finish invoke:" ++ mname
    
    J.Invokespecial   (J.ClassType methodClass) methodKey ->
      -- treat constructor invocations like static methods
      generateInstruction (pc, J.Invokestatic methodClass methodKey)

    -- TODO: still don't know what this one is
    J.Invokespecial   tp _methodKey -> sgUnimplemented $ "Invokespecial for " ++ show tp
      
    J.Invokestatic    className methodKey
      -- don't run the constructor for the object class (we don't have this
      -- class information)
      | className == "java/lang/Object" && J.methodKeyName methodKey == "<init>" ->
        return ()

      | className == "java/lang/Object" && J.methodKeyName methodKey == "hashCode" ->
        -- TODO: hashCode always returns 0, can we make it be an "abstract" int?
        iPush (App $ BVLit knownRepr 0)

      | className == "java/lang/Class" && J.methodKeyName methodKey == "getPrimitiveClass" -> do
        _arg <- rPop
        -- TODO: java reflection
        rPush rNull

      | otherwise -> do
        -- make sure that *this* class has already been initialized
        lift $ initializeClass className
        handle <- lift $ getStaticMethod className methodKey
        callJVMHandle handle

    -- and what is this??
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
         
    J.Checkcast (J.ClassType className) ->
      do objectRef <- rPop
         rawRef <- throwIfRefNull objectRef
         lift $ do obj <- readRef rawRef
                   cls <- getJVMInstanceClass obj
                   b <- isSubclass cls className 
                   assertExpr b "java/lang/ClassCastException"
         rPush objectRef

    J.Checkcast tp ->
      -- TODO checked casts for interfaces
      sgUnimplemented $ "checkcast unimplemented for interface " ++ show tp
    J.Iinc idx constant ->
      do value <- getLocal idx >>= lift . fromIValue
         let constValue = iConst (fromIntegral constant)
         setLocal idx (IValue (App (BVAdd w32 value constValue)))
    J.Instanceof (J.ClassType className) ->
      do objectRef <- rPop
         rawRef <- throwIfRefNull objectRef
         obj <- lift $ readRef rawRef
         cls <- lift $ getJVMInstanceClass obj
         b <- lift $ isSubclass cls className
         let ib = App (BaseIte knownRepr b (App $ BVLit w32 1) (App $ BVLit w32 0))
         iPush ib
    J.Instanceof _tp ->
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


unaryGen ::
  JVMStmtGen h s ret a ->
  (b -> JVMStmtGen h s ret ()) ->
  (a -> JVMGenerator h s ret b) ->
  JVMStmtGen h s ret ()
unaryGen pop push op =
  do value <- pop
     ret <- lift $ op value
     push ret

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

binaryGen ::
  JVMStmtGen h s ret a ->
  JVMStmtGen h s ret b ->
  (c -> JVMStmtGen h s ret ()) ->
  (a -> b -> JVMGenerator h s ret c) ->
  JVMStmtGen h s ret ()
binaryGen pop1 pop2 push op =
  do value2 <- pop2
     value1 <- pop1
     ret <- lift $ value1 `op` value2 
     push ret





newarrayExpr ::
  JVMInt s 
  -- ^ array size, must be nonnegative
  -> Expr JVM s JVMValueType
  -- ^ Initial value for all array elements
  -> Expr JVM s JVMObjectType
newarrayExpr count val =
  let vec = App (VectorReplicate knownRepr (App (BvToNat w32 count)) val)
      ctx = Ctx.empty `Ctx.extend` count `Ctx.extend` vec
      arr = App (MkStruct knownRepr ctx)
      uobj = injectVariant Ctx.i2of2 arr
  in 
     App (RollRecursive knownRepr knownRepr uobj)

newarrayFromVec ::
  Vector (Expr JVM s JVMValueType)
  -- ^ Initial values for all array elements
  -> Expr JVM s JVMObjectType
newarrayFromVec vec = 
  let count = App $ BVLit w32 (toInteger (V.length vec))
      ctx   = Ctx.empty `Ctx.extend` count `Ctx.extend` (App $ VectorLit knownRepr vec)
      arr   = App (MkStruct knownRepr ctx)
      uobj  = injectVariant Ctx.i2of2 arr
  in 
    App $ RollRecursive knownRepr knownRepr uobj
  



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
     let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
     arr <- lift $ assertedJustExpr marr "aload: not a valid array"
     let vec = App (GetStruct arr Ctx.i2of2 knownRepr)
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
     let marr = App (ProjectVariant knownRepr Ctx.i2of2 uobj)
     arr <- lift $ assertedJustExpr marr "astore: not a valid array"
     let vec = App (GetStruct arr Ctx.i2of2 knownRepr)
     -- TODO: assert 0 <= idx < length arr
     let val = App (InjectVariant knownRepr tag (f x))
     let vec' = App (VectorSetEntry knownRepr vec (App (BvToNat w32 idx)) val)
     let arr' = App (SetStruct knownRepr arr Ctx.i2of2 vec')
     let uobj' = App (InjectVariant knownRepr Ctx.i2of2 arr')
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

floatFromDouble :: JVMDouble s -> JVMFloat s
floatFromDouble d = App (FloatCast SingleFloatRepr d)

intFromDouble :: JVMDouble s -> JVMInt s
intFromDouble d = App (FloatToSBV w32 d)

longFromDouble :: JVMDouble s -> JVMLong s
longFromDouble d = App (FloatToSBV w64 d)

doubleFromFloat :: JVMFloat s -> JVMDouble s
doubleFromFloat f = App (FloatCast DoubleFloatRepr f)

intFromFloat :: JVMFloat s -> JVMInt s
intFromFloat f = App (FloatToSBV w32 f)

longFromFloat :: JVMFloat s -> JVMLong s
longFromFloat f = App (FloatToSBV w64 f)

doubleFromInt :: JVMInt s -> JVMDouble s
doubleFromInt i = App (FloatFromSBV DoubleFloatRepr i)

floatFromInt :: JVMInt s -> JVMFloat s
floatFromInt i = App (FloatFromSBV SingleFloatRepr i)

-- | TODO: double check this
longFromInt :: JVMInt s -> JVMLong s
longFromInt x = App (BVSext w64 w32 x)


doubleFromLong :: JVMLong s -> JVMDouble s
doubleFromLong l = App (FloatFromSBV DoubleFloatRepr l)

floatFromLong :: JVMLong s -> JVMFloat s
floatFromLong l = App (FloatFromSBV SingleFloatRepr l)

intFromLong :: JVMLong s -> JVMInt s
intFromLong l = App (BVTrunc w32 w64 l)

iConst :: Integer -> JVMInt s
iConst i = App (BVLit w32 i)

lConst :: Integer -> JVMLong s
lConst i = App (BVLit w64 i)

dConst :: Double -> JVMDouble s
dConst d = App (DoubleLit d)

fConst :: Float -> JVMFloat s
fConst f = App (FloatLit f)

-- TODO: is there a better way to specify -2^32?
minInt :: JVMInt s
minInt = App $ BVLit w32 (- (2 :: Integer) ^ (32 :: Int))

minLong :: JVMLong s 
minLong = App $ BVLit w64 (- (2 :: Integer) ^ (64 :: Int))

--TODO : doublecheck what Crucible does for BVSub
-- For int values, negation is the same as subtraction from
-- zero. Because the Java Virtual Machine uses two's-complement
-- representation for integers and the range of two's-complement
-- values is not symmetric, the negation of the maximum negative int
-- results in that same maximum negative number. Despite the fact that
-- overflow has occurred, no exception is thrown.
iNeg :: JVMInt s -> JVMGenerator h s ret (JVMInt s)
iNeg e = ifte (App $ BVEq w32 e minInt)
              (return minInt)
              (return $ App (BVSub knownRepr (App (BVLit knownRepr 0)) e))


lNeg :: JVMLong s -> JVMGenerator h s ret (JVMLong s)
lNeg e = ifte (App $ BVEq knownRepr e minLong)
              (return minLong)
              (return $ App (BVSub knownRepr (App (BVLit knownRepr 0)) e))



dAdd, dSub, dMul, dDiv, dRem :: JVMDouble s -> JVMDouble s -> JVMDouble s
dAdd e1 e2 = App (FloatAdd DoubleFloatRepr e1 e2)
dSub e1 e2 = App (FloatSub DoubleFloatRepr e1 e2)
dMul e1 e2 = App (FloatMul DoubleFloatRepr e1 e2)
dDiv e1 e2 = App (FloatDiv DoubleFloatRepr e1 e2)
dRem e1 e2 = App (FloatRem DoubleFloatRepr e1 e2)


--TODO: treatment of NaN
--TODO: difference between dCmpg/dCmpl
-- | If the two numbers are the same, the int 0 is pushed onto the
-- stack. If value2 is greater than value1, the int 1 is pushed onto the
-- stack. If value1 is greater than value2, -1 is pushed onto the
-- stack. If either numbers is NaN, the int 1 is pushed onto the
-- stack. +0.0 and -0.0 are treated as equal.
dCmpg, dCmpl :: forall fi s h ret.
                Expr JVM s (FloatType fi) -> Expr JVM s (FloatType fi) -> JVMGenerator h s ret (JVMInt s)
dCmpg e1 e2 = ifte (App (FloatEq e1 e2)) (return $ App $ BVLit w32 0)
                   (ifte (App (FloatGe e2 e1)) (return $ App $ BVLit w32 1)
                         (return $ App $ BVLit w32 (-1)))
dCmpl = dCmpg

dNeg :: JVMDouble s -> JVMDouble s
dNeg = error "dNeg"

fAdd, fSub, fMul, fDiv, fRem :: JVMFloat s -> JVMFloat s -> JVMFloat s
fAdd e1 e2 = App (FloatAdd SingleFloatRepr e1 e2)
fSub e1 e2 = App (FloatSub SingleFloatRepr e1 e2)
fMul e1 e2 = App (FloatMul SingleFloatRepr e1 e2)
fDiv e1 e2 = App (FloatDiv SingleFloatRepr e1 e2)
fRem e1 e2 = App (FloatRem SingleFloatRepr e1 e2)


-- TODO: are these signed or unsigned integers?
-- | Takes two two-word long integers off the stack and compares them. If
-- the two integers are the same, the int 0 is pushed onto the stack. If
-- value2 is greater than value1, the int 1 is pushed onto the stack. If
-- value1 is greater than value2, the int -1 is pushed onto the stack.
lCmp :: JVMLong s -> JVMLong s -> JVMGenerator h s ret (JVMInt s)
lCmp e1 e2 =  ifte (App (BVEq knownRepr e1 e2)) (return $ App $ BVLit w32 0)
                   (ifte (App (BVSlt knownRepr e1 e2)) (return $ App $ BVLit w32 1)
                         (return $ App $ BVLit w32 (-1)))



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
    Ctx.Empty ->
      error "packTypes: arguments do not match JVM types"
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


-- | Define a block with a fresh lambda label, returning the label.
defineLambdaBlockLabel ::
  (IsSyntaxExtension ext, KnownRepr TypeRepr tp) =>
  (forall a. Expr ext s tp -> Generator ext h s t ret a) ->
  Generator ext h s t ret (LambdaLabel s tp)
defineLambdaBlockLabel action =
  do l <- newLambdaLabel
     defineLambdaBlock l action
     return l

-----------------------------------------------------------------------------
-- | translateClass

type StaticFieldTable = Map (J.ClassName, String) (GlobalVar JVMValueType)
type MethodHandleTable = Map (J.ClassName, J.MethodKey) JVMHandleInfo

data MethodTranslation = forall args ret. MethodTranslation
   { methodHandle :: FnHandle args ret
   , methodCCFG   :: C.SomeCFG JVM args ret
   }

data ClassTranslation =
  ClassTranslation
  { cfgMap        :: Map (J.ClassName,J.MethodKey) MethodTranslation
  , initCFG       :: C.AnyCFG JVM 
  }
  
data JVMTranslation =
  JVMTranslation
  { translatedClasses :: Map J.ClassName ClassTranslation 
  , transContext      :: JVMContext
  }

-- left biased
instance Semigroup ClassTranslation where
  ct1 <> ct2 = ClassTranslation
               { cfgMap  = Map.union (cfgMap ct1) (cfgMap ct2)
               , initCFG = initCFG ct1
               }
               
instance Semigroup JVMTranslation where
  j1 <> j2   = JVMTranslation
               { translatedClasses = Map.unionWith ((<>))
                                     (translatedClasses j1) (translatedClasses j2)
               , transContext = transContext j1 <> transContext j2
               }


-----------------------------------------------------------------------------

-- | Given the name of a class and the field name, define the name of the global variable
globalVarName :: J.ClassName -> String -> Text
globalVarName cn fn = fromString (J.unClassName cn ++ "." ++ fn)


allParameterTypes :: J.ClassName -> Bool -> J.MethodKey -> [J.Type]
allParameterTypes className isStatic m
  | isStatic  = J.methodKeyParameterTypes m
  | otherwise = J.ClassType className : J.methodKeyParameterTypes m

methodHandleName :: J.ClassName -> J.MethodKey -> FunctionName
methodHandleName cn mn = fromString (J.unClassName cn ++ "." ++ J.methodKeyName mn)

jvmToFunHandleRepr ::
  J.ClassName -> Bool -> J.MethodKey ->
  (forall args ret. CtxRepr args -> TypeRepr ret -> a)
  -> a
jvmToFunHandleRepr className isStatic meth k =
   let args  = Ctx.fromList (map javaTypeToRepr (allParameterTypes className isStatic meth))
       ret   = maybe (Some C.UnitRepr) javaTypeToRepr (J.methodKeyReturnType meth)
   in case (args, ret) of
     (Some argsRepr, Some retRepr) -> k argsRepr retRepr



-- | allocate a new method handle and add it to the table of method handles
declareMethod :: HandleAllocator s -> J.Class -> MethodHandleTable -> J.Method ->  ST s MethodHandleTable
declareMethod halloc mcls ctx meth =
  let cname = J.className mcls
      mkey  = J.methodKey meth
  in 
   jvmToFunHandleRepr cname (J.methodIsStatic meth) mkey $
      \ argsRepr retRepr -> do
         h <- mkHandle' halloc (methodHandleName cname mkey) argsRepr retRepr
         return $ Map.insert (cname, mkey) (JVMHandleInfo mkey h) ctx

-- | allocate the static fields and add it to the static field table
declareStaticField :: HandleAllocator s
    -> J.Class
    -> StaticFieldTable
    -> J.Field
    -> ST s StaticFieldTable
declareStaticField halloc c m f = do
  let cn = J.className c
  let fn = J.fieldName f
  let ty = J.fieldType f
  traceM $ "declaring: " ++ J.unClassName cn ++ "." ++ fn
  gvar <- C.freshGlobalVar halloc (globalVarName cn fn) (knownRepr :: TypeRepr JVMValueType)
  return $ (Map.insert (cn,fn) gvar m)

-- | Create the initial JVMContext (contains only the global variable for the dynamic
-- class table
mkInitialJVMContext :: HandleAllocator s -> ST s JVMContext
mkInitialJVMContext halloc = do
  gv <- C.freshGlobalVar halloc (fromString "JVM_CLASS_TABLE")
                                (knownRepr :: TypeRepr JVMClassTableType)
  return $ JVMContext
    { methodHandles     = Map.empty
    , staticFields      = Map.empty
    , classTable        = Map.empty
    , dynamicClassTable = gv
    }

-- This is called in Interpreter.hs
mkInitialJVMTranslation :: HandleAllocator s -> ST s JVMTranslation
mkInitialJVMTranslation halloc = do
  ctx <- mkInitialJVMContext halloc
  return $ JVMTranslation { translatedClasses = Map.empty
                          , transContext      = ctx }

-- | extend the JVM context in preparation for translating class c
extendJVMContext :: HandleAllocator s -> JVMContext -> J.Class -> ST s JVMContext
extendJVMContext halloc ctx0 c = do
  sm <- foldM (declareMethod halloc c) Map.empty (J.classMethods c)
  st <- foldM (declareStaticField halloc c) Map.empty (J.classFields c)
  return $ JVMContext
    { methodHandles     = sm 
    , staticFields      = st
    , classTable        = Map.singleton (J.className c) c
    , dynamicClassTable = dynamicClassTable ctx0
    } <> ctx0

addToClassTable :: J.Class -> JVMContext -> JVMContext
addToClassTable c ctx =
  trace ("Adding " ++ show (J.className c)) $ 
  ctx { classTable = Map.insert (J.className c) c (classTable ctx) }


-- | Translate a single JVM method definition into a crucible CFG
translateMethod :: JVMContext
                -> J.Class
                -> J.Method
                -> ST s ((J.ClassName, J.MethodKey), MethodTranslation)
translateMethod ctx c m = do
  let cName = J.className c
  let mKey  = J.methodKey m
  traceM $ "translating " ++ J.unClassName cName ++ "/" ++ J.methodName m
  case Map.lookup (cName,mKey) (methodHandles ctx)  of
    Just (JVMHandleInfo _ h)  -> 
      case (handleArgTypes h, handleReturnType h) of
        ((argTypes :: CtxRepr args), (retType :: TypeRepr ret)) -> do
          let  def :: FunctionDef JVM h (JVMState ret) args ret
               def inputs = (s, f)
                 where s = initialState ctx m retType
                       f = generateMethod cName m argTypes inputs
          (SomeCFG g, []) <- defineFunction InternalPos h def
          let g' = toSSA g
            --traceM $ show g'
          traceM $ "finished translating " ++ J.unClassName cName ++ "/" ++ J.methodName m
          return ((cName,mKey), MethodTranslation h g')
    Nothing -> fail $ "internal error: Could not find method " ++ show mKey

------------------------------------------------------------------------
-- | initMemProc
--
initCFGProc :: HandleAllocator s
            -> JVMContext
            -> ST s (C.AnyCFG JVM)
initCFGProc halloc ctx = do
   h <- mkHandle halloc "class_table_init"
   let gv = dynamicClassTable ctx
   let meth = undefined
       def :: FunctionDef JVM s (JVMState UnitType) EmptyCtx UnitType
       def _inputs = (s, f)
              where s = initialState ctx meth knownRepr
                    f = do writeGlobal gv (App $ EmptyStringMap knownRepr)
                           return (App EmptyApp)
                    
   (SomeCFG g,[]) <- defineFunction InternalPos h def
   case toSSA g of
     C.SomeCFG g' -> return $! C.AnyCFG g'


-- | skip certain methods, as well as any that refer to
-- unknown types and classes
skipMethod :: JVMContext -> J.Class -> J.Method -> Bool
skipMethod ctx c m =
  let crs  = classRefs m
      name = J.unClassName (J.className c) ++ "/" ++ J.methodName m
  in
     -- the method body/type references a class that we don't know about
     any (\cr -> not (Map.member cr (classTable ctx))) (Set.elems crs)
     -- it's one of these specific methods
  || name `elem` [ "java/lang/Object/toString"
                 , "java/lang/Object/wait"
                 , "java/lang/Throwable/getStackTrace"
--                 , "java/lang/Integer/getChars"
--                 , "java/lang/Long/getChars"
                    -- bug somewhere in use of writeRegisters, it's providing more values than regs
                 ] where
  

translateClass ::  HandleAllocator s -- ^ Generator for nonces
               -> JVMContext 
               -> J.Class           -- ^ Class to translate
               -> ST s JVMTranslation
translateClass halloc ctx c = translateClasses halloc ctx [c]

translateClasses :: HandleAllocator s -- ^ Generator for nonces
               -> JVMContext 
               -> [J.Class]           -- ^ Class to translate
               -> ST s JVMTranslation
translateClasses halloc ctx1 cs = do
  
  -- create initial context, declaring the statically known methods and fields.
  ctx <- foldM (extendJVMContext halloc) ctx1 cs

  let trans c = do
        traceM $ "translating " ++ J.unClassName (J.className c)
        let methods = J.classMethods c
        -- translate methods
        let should_translate m = not (J.methodIsAbstract m || J.methodIsNative m || skipMethod ctx c m)
        traceM $ "...skipping methods " ++ show (map J.methodName (filter (not . should_translate)
                                                                (J.classMethods c)))
        pairs <- mapM (translateMethod ctx c) (filter should_translate (J.classMethods c))
        -- initialization code
        -- currently unused
        initCFG0 <- initCFGProc halloc ctx
        -- return result
        return $ JVMTranslation 
          { translatedClasses = Map.singleton (J.className c)
            (ClassTranslation { cfgMap        = Map.fromList pairs
                              , initCFG       = initCFG0
                              })
          , transContext = ctx }

  trs <- mapM trans cs
  return $ foldr1 (<>) trs

--------------------------------------------------------------------------------

-- | Make method bindings for static simulation
mkBindings :: JVMContext
           -> Map J.ClassName ClassTranslation
           -> C.FunctionBindings p sym JVM
mkBindings ctx transClassMap =
  C.fnBindingsFromList (map mkFunBinding (Map.toList (methodHandles ctx)))
  where mkFunBinding ((cn0,_), JVMHandleInfo mKey _) = do
          case Map.lookup (cn0, mKey) (cfgMap (transClassMap Map.! cn0)) of
            Just (MethodTranslation h (C.SomeCFG g)) -> 
              C.FnBinding h (C.UseCFG g (C.postdomInfo g))
            Nothing  -> error $ "cannot find method!" ++ (J.unClassName cn0)
              ++ "." ++ (J.methodKeyName mKey)

--------------------------------------------------------------------------------

-- Most of this part is adapted from crucible-llvm Lang.Crucible.LLVM.Intrinsics
data JVMOverride p sym = forall args ret.
  JVMOverride
  { jvmOverride_className      :: J.ClassName
  , jvmOverride_methodKey      :: J.MethodKey
  , jvmOverride_methodIsStatic :: Bool
  , jvmOverride_args           :: CtxRepr args
  , jvmOverride_ret            :: TypeRepr ret
  , jvmOverride_def            :: forall rtp args' ret'.
         sym ->
--         JVMContext ->
         Ctx.Assignment (C.RegEntry sym) args ->
         C.OverrideSim p sym JVM rtp args' ret' (C.RegValue sym ret)
  }

newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall rtp l a.
    Ctx.Assignment (C.RegEntry sym) args ->
    C.OverrideSim p sym JVM rtp l a (Ctx.Assignment (C.RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall rtp l a.
    C.RegValue sym tp ->
    C.OverrideSim p sym JVM rtp l a (C.RegValue sym tp')) }


transformJVMArgs :: forall m p sym args args'.
  (IsSymInterface sym, Monad m) =>
  sym ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym args args')
transformJVMArgs _ Ctx.Empty Ctx.Empty =
  return (ArgTransformer (\_ -> return Ctx.Empty))
transformJVMArgs sym (rest' Ctx.:> tp') (rest Ctx.:> tp) = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformJVMRet sym tp tp'
                 (ArgTransformer fs) <- transformJVMArgs sym rest' rest
                 xs' <- fs xs
                 x'  <- C.RegEntry tp' <$> f (C.regValue x)
                 pure (xs' Ctx.:> x')))
transformJVMArgs _ _ _ =
  panic "Intrinsics.transformJVMArgs"
    [ "transformJVMArgs: argument shape mismatch!" ]

transformJVMRet ::
  (IsSymInterface sym, Monad m) =>
  sym ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ret ret')
-- maybe do some work here?
transformJVMRet _sym ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformJVMRet _sym ret ret'
  = panic "Intrinsics.transformJVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the JVM calling convention.
build_jvm_override ::
  IsSymInterface sym =>
  sym ->
  FunctionName ->
  CtxRepr args ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall rtp' l' a'. Ctx.Assignment (C.RegEntry sym) args ->
   C.OverrideSim p sym JVM rtp' l' a' (C.RegValue sym ret)) ->
  C.OverrideSim p sym JVM rtp l a (C.Override p sym JVM args' ret')
build_jvm_override sym fnm args ret args' ret' llvmOverride =
  do fargs <- transformJVMArgs sym args args'
     fret  <- transformJVMRet  sym ret  ret'
     return $ C.mkOverride' fnm ret' $
            do C.RegMap xs <- C.getOverrideArgs
               applyValTransformer fret =<< llvmOverride =<< applyArgTransformer fargs xs

register_jvm_override :: forall p sym l a rtp
                       . (IsSymInterface sym)
                      => JVMOverride p sym 
                      -> StateT JVMContext (C.OverrideSim p sym JVM rtp l a) ()
register_jvm_override (JVMOverride { jvmOverride_className=cn
                                     , jvmOverride_methodKey=mk
                                     , jvmOverride_methodIsStatic=isStatic
                                     , jvmOverride_args=overrideArgs
                                     , jvmOverride_ret=overrideRet
                                     , jvmOverride_def=def }) = do
  jvmctx <- get

  let fnm = methodHandleName cn mk
  
  sym <- lift $ C.getSymInterface
  

  jvmToFunHandleRepr cn isStatic mk  $ \derivedArgs derivedRet -> do
    o <- lift $ build_jvm_override sym fnm overrideArgs overrideRet derivedArgs derivedRet (def sym)
    case Map.lookup (cn,mk) (methodHandles jvmctx) of
      Just (JVMHandleInfo _mkey h) -> do
        case testEquality (handleArgTypes h) derivedArgs of
           Nothing ->
             panic "Intrinsics.register_jvm_override"
               [ "Argument type mismatch when registering override."
               , "*** Override name: " ++ show fnm
               ]
           Just Refl ->
             case testEquality (handleReturnType h) derivedRet of
               Nothing ->
                 panic "Intrinsics.register_jvm_override"
                   [ "return type mismatch when registering override"
                   , "*** Override name: " ++ show fnm
                   ]
               Just Refl -> lift $ C.bindFnHandle h (C.UseOverride o)
      Nothing ->
        do ctx <- lift $ use C.stateContext
           let ha = C.simHandleAllocator ctx
           h <- lift $ liftST $ mkHandle' ha fnm derivedArgs derivedRet
           lift $ C.bindFnHandle h (C.UseOverride o)
           put (jvmctx { methodHandles = Map.insert (cn,mk) (JVMHandleInfo mk h) (methodHandles jvmctx) })

--------------------------------------------------------------------------------

-- | This is an example of a nop override
-- Explicitly calling the garbage collector does nothing during symbolic
-- execution
gc_override ::(IsSymInterface sym) => JVMOverride p sym
gc_override =
  let isStatic = False
      mk       = J.makeMethodKey "gc" "()V" in
  jvmToFunHandleRepr "java/lang/Runtime" isStatic mk $ \ argsRepr retRepr ->
    JVMOverride { jvmOverride_className="java/lang/System"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \sym args -> return ()
                }

-- | Convert a register value to a string, using What4's 'printSymExpr'
-- Won't necessarily look like a standard types
showReg :: forall sym arg. (IsSymInterface sym) => TypeRepr arg -> C.RegValue sym arg -> String
showReg repr arg
  | Just Refl <- testEquality repr doubleRepr
  = show $ W4.printSymExpr arg -- SymExpr sym BaseRealType
  | Just Refl <- testEquality repr floatRepr
  = show $ W4.printSymExpr arg
  | Just Refl <- testEquality repr intRepr
  = show $ W4.printSymExpr arg -- SymExpr sym (BaseBVType ..)
  | Just Refl <- testEquality repr longRepr
  = show $ W4.printSymExpr arg
  | Just Refl <- testEquality repr refRepr
  = error "TODO: Not sure what do do for general references"
  | otherwise
  = error "Internal error: invalid regval type"

printlnMthd :: forall sym arg p. (IsSymInterface sym) => 
  String -> TypeRepr arg -> JVMOverride p sym
printlnMthd = printStream "println" True 

printMthd :: forall sym arg p. (IsSymInterface sym) => 
  String -> TypeRepr arg -> JVMOverride p sym
printMthd = printStream "print" True 

-- Should we print to the print handle in the simulation context?
-- or just to stdout
printStream :: forall sym arg p. (IsSymInterface sym) => String -> Bool ->
  String -> TypeRepr arg -> JVMOverride p sym
printStream name newl descr t =
  let isStatic = False in
  let mk = J.makeMethodKey name descr in
  jvmToFunHandleRepr "java/io/PrintStream" isStatic mk $ \ argsRepr retRepr ->
    if (testEquality argsRepr (Ctx.Empty `Ctx.extend` refRepr `Ctx.extend` t) == Nothing)
       then error "descriptor does not match type"
    else if (testEquality retRepr UnitRepr == Nothing)
       then error "descriptor does not have void return type"
    else JVMOverride { jvmOverride_className="java/io/PrintStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` t
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \sym args -> do
                    let reg = C.regValue (Ctx.last args)
                    let str = showReg @sym t reg
                    h <- C.printHandle <$> C.getContext
                    liftIO $ (if newl then hPutStrLn else hPutStr) h str
                    liftIO $ hFlush h
                }

flush_override :: (IsSymInterface sym) => JVMOverride p sym
flush_override =
  let isStatic = False in
  let mk = J.makeMethodKey "flush" "()V" in
  JVMOverride   { jvmOverride_className="java/io/BufferedOutputStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=UnitRepr
                , jvmOverride_def=
                  \sym args -> do
                    h <- C.printHandle <$> C.getContext
                    liftIO $ hFlush h
                }

-- java.lang.Throwable.fillInStackTrace  (i.e. just returns this)
-- REVISIT: We may want to correctly populate the Throwable instance,
-- instead of this just being a pass-through.
fillInStackTrace_override :: (IsSymInterface sym) => JVMOverride p sym
fillInStackTrace_override =
  let isStatic = False in
  let mk = J.makeMethodKey "fillInStackTrace" "()Ljava/lang/Throwable" in
  JVMOverride   { jvmOverride_className="java/io/BufferedOutputStream"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=refRepr
                , jvmOverride_def=
                  \sym args -> do
                    let reg = C.regValue (Ctx.last args)
                    return reg
                }

-- OMG This is difficult to define
isArray_override :: forall p sym. (IsSymInterface sym) => JVMOverride p sym
isArray_override =
  let isStatic = False in
  let mk = J.makeMethodKey "isArray" "()Z" in
  JVMOverride   { jvmOverride_className="java/lang/Class"
                , jvmOverride_methodKey=mk
                , jvmOverride_methodIsStatic=isStatic
                , jvmOverride_args=Ctx.Empty `Ctx.extend` refRepr
                , jvmOverride_ret=intRepr
                , jvmOverride_def=
                  \sym args -> do
                    let reg :: W4.PartExpr (W4.Pred sym) (C.MuxTree sym (RefCell JVMObjectType))
                        reg = C.regValue (Ctx.last args)
                    bvFalse <- liftIO $ return $ W4.bvLit sym knownRepr 0
                    let k :: RefCell JVMObjectType -> IO (W4.SymBV sym 32)
                        k = undefined
                    let h :: W4.Pred sym -> (W4.SymBV sym 32) -> (W4.SymBV sym 32) -> IO (W4.SymBV sym 32)
                        h = undefined
                    let g :: (C.MuxTree sym (RefCell JVMObjectType)) -> IO (W4.SymBV sym 32)
                                                                     -> IO (W4.SymBV sym 32)
                        g mux curr = undefined

                    liftIO $ foldr g bvFalse reg
                }




stdOverrides :: (IsSymInterface sym) => [JVMOverride p sym]
stdOverrides = 
   [  printlnMthd "()V"   UnitRepr
    , printlnMthd "(Z)V"  intRepr
    , printlnMthd "(C)V"  intRepr  -- TODO: special case for single char, i.e. binary output
    , printlnMthd "([C)V" refRepr  -- TODO: array of chars
    , printlnMthd "(D)V"  doubleRepr
    , printlnMthd "(F)V"  floatRepr
    , printlnMthd "(I)V"  intRepr
    , printlnMthd "(J)V"  longRepr 
    , printlnMthd "(Ljava/lang/Object;)V" refRepr -- TODO: object toString
    , printlnMthd "(Ljava/lang/String;)V" refRepr -- TODO: String objects
    
    , printMthd "()V"   UnitRepr
    , printMthd "(Z)V"  intRepr
    , printMthd "(C)V"  intRepr  -- TODO: special case for single char, i.e. binary output
    , printMthd "([C)V" refRepr  -- TODO: array of chars
    , printMthd "(D)V"  doubleRepr
    , printMthd "(F)V"  floatRepr
    , printMthd "(I)V"  intRepr
    , printMthd "(J)V"  longRepr 
    , printMthd "(Ljava/lang/Object;)V" refRepr -- TODO: object toString
    , printMthd "(Ljava/lang/String;)V" refRepr -- TODO: String objects

    , flush_override
    , gc_override
    , fillInStackTrace_override
    ] 

{-
callPutChar
  :: (IsSymInterface sym)
  => sym
  -> C.RegEntry sym (BVType 32)
  -> C.OverrideSim p sym JVM r args ret (C.RegValue sym (BVType 32))
callPutChar _sym
 (regValue -> ch) = do
    h <- printHandle <$> getContext
    let chval = maybe '?' (toEnum . fromInteger) (asUnsignedBV ch)
    liftIO $ hPutChar h chval
    return ch
-}

{-
callPrintStream
  :: (IsSymInterface sym)
  => sym
  -> C.RegEntry sym (JVMValue s)
  -> C.OverrideSim p sym JVM r args ret (RegValue sym (BVType 32))
callPrintStream sym 
  (regValue -> strPtr) = do
      ((str, n), mem') <- liftIO $ runStateT (executeDirectives (printfOps sym valist) ds) mem
      h <- printHandle <$> getContext
      liftIO $ hPutStr h str
      liftIO $ bvLit sym knownNat (toInteger n)

{-
  ( "java/io/PrintStream"
                    , 
                    , MethodBody knownRepr (knownRepr :: TypeRepr UnitType) $
                      -- ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)
                      do state <- ask
                         let simctx  = _stateContext state  -- (undefined :: C.SimContext p sym JVM)
                         let tree    = _stateTree state
                         printStream True (t == "(C)V")
                         let globals = C.emptyGlobals
                         let val = (undefined :: _)
                         return $ C.ResultState (C.FinishedResult simctx (C.TotalRes (C.GlobalPair val globals)))
                    --  \_ args -> printStream True (t == "(C)V") args
                    )
-}

printStream :: Bool -> Bool -> [JVMValue s] -> ReaderT (C.SimState p sym ext r f a) IO ()
printStream nl _ []       = liftIO $ (if nl then putStrLn else putStr) "" >> hFlush stdout
printStream nl binary [x] = do
    let putStr' s = liftIO $ (if nl then putStrLn else putStr) s >> hFlush stdout
    case x of
      IValue (asInt sbe -> Just v)
        | binary    -> putStr' [chr $ fromEnum v]
        | otherwise -> putStr' $ show v
      v@IValue{} -> putStr' . render $ ppValue sbe v

      LValue (asLong sbe -> Just v) -> putStr' $ show v
      v@LValue{} -> putStr' . render $ ppValue sbe v
      FValue f -> putStr' (show f)
      DValue d -> putStr' (show d)
      RValue r -> do
        ms <- lookupStringRef r
        case ms of
          Just str  -> putStr' str
          Nothing   -> do
            let key = makeMethodKey "toString" "()Ljava/lang/String;"
            msref <- execInstanceMethod "java/lang/Object" key r []
            case msref of
              Just sref -> putStr' =<< drefString (unRValue sref)
              _ -> err "toString terminated abnormally"
      _ -> abort $ "Unable to display values of type other than "
                 ++ "int, long, and reference to constant string"
printStream _ _ _ = abort $ "Unable to print more than one argument"
-}

{-

data MethodBody p sym = forall (args :: Ctx CrucibleType) (ret :: CrucibleType).
  MethodBody 
    (CtxRepr args)
    (TypeRepr ret)
    (forall r. C.ExecCont p sym JVM r (C.OverrideLang ret) (Just args))
  

overrideInstanceMethod :: HandleAllocator s -> J.ClassName -> J.MethodKey -> MethodBody p sym ->
   ST s (C.FnBinding p sym JVM)
overrideInstanceMethod halloc cn mk (MethodBody argsRepr retRepr code) = do
   let funName = fromString (J.unClassName cn ++ "." ++ J.methodKeyName mk)
   handle <- mkHandle' halloc funName argsRepr retRepr
   let override = C.Override funName code 
   return $ C.FnBinding handle (C.UseOverride override)

overrideStaticMethod = undefined


-- | Register all predefined overrides for builtin native implementations.
stdOverrides :: HandleAllocator s -> ST s (C.FunctionBindings p sym JVM)
stdOverrides halloc = do
  mapM_ (\(cn, key, impl) -> overrideInstanceMethod halloc cn key impl)
    [ printlnMthd "()V"
    , printlnMthd "(Z)V"
    , printlnMthd "(C)V"
    , printlnMthd "([C)V"
    , printlnMthd "(D)V"
    , printlnMthd "(F)V"
    , printlnMthd "(I)V"
    , printlnMthd "(J)V"
    , printlnMthd "(Ljava/lang/Object;)V"
    , printlnMthd "(Ljava/lang/String;)V"
    , printMthd   "(Z)V"
    , printMthd   "(C)V"
    , printMthd   "([C)V"
    , printMthd   "(D)V"
    , printMthd   "(F)V"
    , printMthd   "(I)V"
    , printMthd   "(J)V"
    , printMthd   "(Ljava/lang/Object;)V"
    , printMthd   "(Ljava/lang/String;)V"
    , appendIntegralMthd "(I)Ljava/lang/StringBuilder;"
    , appendIntegralMthd "(J)Ljava/lang/StringBuilder;"
    -- java.io.BufferedOutputStream.flush
    , ( "java/io/BufferedOutputStream"
      , J.makeMethodKey "flush" "()V"
      , \_ _ -> liftIO $ hFlush stdout
      )
    -- java.lang.Runtime.gc
    , ( "java/lang/Runtime"
      , J.makeMethodKey "gc" "()V"
      -- Should we implement a garbage collector? ;)
      , \_ _ -> return ()
      )
    -- java.lang.Throwable.fillInStackTrace
    -- REVISIT: We may want to correctly populate the Throwable instance,
    -- instead of this just being a pass-through.
    , ( "java/lang/Throwable"
      , J.makeMethodKey "fillInStackTrace" "()Ljava/lang/Throwable;"
      , \this _ -> pushValue (RValue this)
      )
    -- java.lang.Class.isArray
    , ( "java/lang/Class"
      , J.makeMethodKey "isArray" "()Z"
      , \this _ -> pushValue =<< classNameIsArray =<< getClassName this
      )
    -- java.lang.Class.isPrimitive
    , ( "java/lang/Class"
      , J.makeMethodKey "isPrimitive" "()Z"
      , \this _ -> pushValue =<< classNameIsPrimitive =<< getClassName this
      )
    -- java.lang.Class.getComponentType
    , ( "java/lang/Class"
      , J.makeMethodKey "getComponentType" "()Ljava/lang/Class;"
      , \this _ -> do
          nm <- getClassName this
          pushValue =<< RValue
                        <$> if classNameIsArray' nm
                            then getJVMClassByName (mkClassName (tail nm)) -- BH: why tail?
                            else return NullRef
      )
    -- java.lang.class.getClassLoader -- REVISIT: This implementation makes it so
    -- that custom class loaders are not supported.
    , ( "java/lang/Class"
      , J.makeMethodKey "getClassLoader" "()Ljava/lang/ClassLoader;"
      , \_ _ -> pushValue (RValue NullRef)
      )
    -- java.lang.String.intern -- FIXME (must reconcile reference w/ strings map)
    , ( "java/lang/String"
      , J.makeMethodKey "intern" "()Ljava/lang/String;"
      , \this _ -> pushValue =<< RValue <$> (refFromString =<< drefString this)
      )
    ]

  --------------------------------------------------------------------------------
  -- Static method overrides

  mapM_ (\(cn, key, impl) -> overrideStaticMethod cn key impl)
    [ -- Java.lang.System.arraycopy
      let arrayCopyKey =
            J.makeMethodKey "arraycopy"
              "(Ljava/lang/Object;ILjava/lang/Object;II)V"
      in
        ( "java/lang/System"
        , arrayCopyKey
        , \opds -> do
            let nativeClass = "com/galois/core/NativeImplementations"
            pushStaticMethodCall nativeClass arrayCopyKey opds Nothing
        )
      -- java.lang.System.exit(int status)
    , fillArrayMethod "([ZZ)V"
    , fillArrayMethod "([ZIIZ)V"
    , fillArrayMethod "([BB)V"
    , fillArrayMethod "([BIIB)V"
    , fillArrayMethod "([CC)V"
    , fillArrayMethod "([CIIC)V"
    , fillArrayMethod "([DD)V"
    , fillArrayMethod "([DIID)V"
    , fillArrayMethod "([FF)V"
    , fillArrayMethod "([FIIF)V"
    , fillArrayMethod "([II)V"
    , fillArrayMethod "([IIII)V"
    , fillArrayMethod "([JJ)V"
    , fillArrayMethod "([JIIJ)V"
    , fillArrayMethod "([SS)V"
    , fillArrayMethod "([SIIS)V"
    , fillArrayMethod "([Ljava/lang/Object;Ljava/lang/Object;)V"
    , fillArrayMethod "([Ljava/lang/Object;IILjava/lang/Object;)V"
    , ( "java/lang/System"
      , J.makeMethodKey "exit" "(I)V"
      , \[IValue status] -> do
          sbe <- use backend
          let codeStr = case asInt sbe status of
                          Nothing -> "unknown exit code"
                          Just code -> "exit code " ++ show code
          errorPath . FailRsn
            $ "java.lang.System.exit(int status) called with " ++ codeStr
      )
      -- java.lang.Float.floatToRawIntBits: override for invocation by
      -- java.lang.Math's static initializer
    , ( "java/lang/Float"
      , J.makeMethodKey "floatToRawIntBits" "(F)I"
      , \args -> case args of
                   [FValue flt] -> do
                     when (flt /= (-0.0 :: Float)) $
                       abort "floatToRawIntBits: overridden for -0.0f only"
                     pushValue =<< IValue <$>
                       App $ LitInt (fromIntegral (0x80000000 :: Word32))
                   _ -> abort "floatToRawIntBits: called with incorrect arguments"
      )
      -- java.lang.Double.doubleToRawLongBits: override for invocation by
      -- java.lang.Math's static initializer
    , ( "java/lang/Double"
      , J.makeMethodKey "doubleToRawLongBits" "(D)J"
      , \args -> case args of
                   [DValue dbl] -> do
                     when (dbl /= (-0.0 :: Double)) $
                       abort "doubltToRawLongBits: overriden -0.0d only"
                     pushValue =<< withSBE (\sbe -> LValue <$>
                                             termLong sbe (fromIntegral (0x8000000000000000 :: Word64)))
                   _ -> abort "floatToRawIntBits: called with incorrect arguments"
      )
      -- Set up any necessary state for the native methods of various
      -- classes. At the moment, nothing is necessary.
    , ( "java/lang/Class"
      , J.makeMethodKey "registerNatives" "()V"
      , \_ -> return ()
      )
    , ( "java/lang/ClassLoader"
      , J.makeMethodKey "registerNatives" "()V"
      , \_ -> return ()
      )
    , ( "java/lang/Thread"
      , J.makeMethodKey "registerNatives" "()V"
      , \_ -> return ()
      )
    , ( "java/lang/Class"
      , J.makeMethodKey "desiredAssertionStatus0" "(Ljava/lang/Class;)Z"
      , \_ -> pushValue =<< withSBE (\sbe -> IValue <$> termInt sbe 1)
      )
    , ( "java/lang/Class"
      , J.makeMethodKey "getPrimitiveClass" "(Ljava/lang/String;)Ljava/lang/Class;"
      , \args -> error "TODO: look at simulator code"
      )
    , ( "java/io/FileInputStream", J.makeMethodKey "initIDs" "()V", \ _ -> return () )
    , ( "java/io/FileOutputStream", J.makeMethodKey "initIDs" "()V", \ _ -> return () )
    , ( "java/io/RandomAccessFile", J.makeMethodKey "initIDs" "()V", \ _ -> return () )
    , ( "java/io/ObjectStreamClass", J.makeMethodKey "initNative" "()V", \ _ -> return () )
    , ( "java/security/AccessController"
      , J.makeMethodKey "doPrivileged" "(Ljava/security/PrivilegedAction;)Ljava/lang/Object;"
      , \args -> error "TODO: look at static simulator code"
      )
    , ( "java/lang/System", J.makeMethodKey "nanoTime" "()J", \ _ -> do
          dbugM "warning: long java.lang.System.nanoTime() always returns 0 during symbolic execution" 
          pushValue =<< withSBE (\sbe -> LValue <$> termLong sbe 0)
      )
    , ( "java/lang/System", J.makeMethodKey "currentTimeMillis" "()J", \ _ -> do
          whenVerbosity (>=2) 
          pushValue =<< withSBE (\sbe -> LValue <$> termLong sbe 0)
      )
    , ( "java/lang/System", J.makeMethodKey "identityHashCode" "(Ljava/lang/Object;)I", \ _ -> do
          dbugM "warning: int java.lang.System.identityHashCode(Object) always returns 0 during symbolic executin"
          pushValue =<< withSBE (\sbe -> IValue <$> termInt sbe 0)
      )

    -- Here we override the "valueOf" methods that are used for autoboxing primitive types.
    -- We do this because these methods are defined to use a lookup table cache; if we attempt
    -- to autobox a symbolic value, this results in indexing a reference array by a symbolic
    -- value, which is not allowed.  Instead, we override these methods to just directly call
    -- the appropriate class constructor.

    , ( "java/lang/Boolean", J.makeMethodKey "valueOf" "(Z)Ljava/lang/Boolean;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Boolean" (Just [(BooleanType, IValue x)])
      )
    , ( "java/lang/Byte", J.makeMethodKey "valueOf" "(B)Ljava/lang/Byte;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Byte" (Just [(ByteType, IValue x)])
      )
    , ( "java/lang/Short", J.makeMethodKey "valueOf" "(S)Ljava/lang/Short;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Short" (Just [(ShortType, IValue x)])
      )
    , ( "java/lang/Integer", J.makeMethodKey "valueOf" "(I)Ljava/lang/Integer;", \([IValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Integer" (Just [(IntType, IValue x)])
      )
    , ( "java/lang/Long", J.makeMethodKey "valueOf" "(J)Ljava/lang/Long;", \([LValue x]) -> do
          pushValue . RValue =<< createInstance "java/lang/Long" (Just [(LongType, LValue x)])
      )
    ]
  where
    printlnMthd t = ( "java/io/PrintStream"
                    , J.makeMethodKey "println" t
                    , MethodBody knownRepr (knownRepr :: TypeRepr UnitType) $
                      -- ReaderT (SimState p sym ext r f a) IO (ExecState p sym ext r)
                      do state <- ask
                         let simctx  = _stateContext state  -- (undefined :: C.SimContext p sym JVM)
                         let tree    = _stateTree state
                         printStream True (t == "(C)V")
                         let globals = C.emptyGlobals
                         let val = (undefined :: _)
                         return $ C.ResultState (C.FinishedResult simctx (C.TotalRes (C.GlobalPair val globals)))
                    --  \_ args -> printStream True (t == "(C)V") args
                    )
    printMthd t   = ( "java/io/PrintStream"
                    , J.makeMethodKey "print" t
                    , \_ args -> printStream False (t == "(C)V") args
                    )
    fillArrayMethod t =
      ( "java/util/Arrays"
      , J.makeMethodKey "fill" t
      , \args ->
          case args of
            [RValue ref, val] -> fillArray ref Nothing val
            [RValue ref, beg, end, val] -> fillArray ref (Just (beg, end)) val
            _ -> abort "Arrays.fill called with invalid args"
      )

    -- | Allows the user to append pretty-printed renditions of symbolic
    -- ints/longs as strings; however, we should REVISIT this.  Concatenation of
    -- the typical form form ("x = " + x) where x is symbolic is currently very
    -- inefficient since the concrete string representation of x is still
    -- executed through many array operations in the {Abstract,}StringBuilder
    -- implementations and so forth.  This leads to the odd situation where:
    --
    -- System.out.print("x = ");
    -- System.out.println(x);
    --
    -- is vastly more efficient than the equivalent concatenating version.
    appendIntegralMthd t =
      let cn = "java/lang/StringBuilder"
      in
        ( cn
        , makeMethodKey "append" t
        , \this [st] -> do
            let redir = makeMethodKey "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;"
                warn  = dbugM $
                  "Warning: string concatenation of symbolic variables is "
                    ++ "very inefficient in this release. \n  Consider using "
                    ++ "'System.out.print(\"x = \"); System.out.println(x);'"
                    ++ "\n  instead of 'System.out.println(\"x = \" + x); "
                    ++ "also see Symbolic.Debug.trace()."
            sbe <- use backend
            case st of
              IValue (asInt sbe -> Just{}) -> return ()
              LValue (asLong sbe -> Just{}) -> return ()
              _ -> warn
            sr        <- refFromString . render . ppValue sbe $ st
            void $ execInstanceMethod cn redir this [RValue sr]
        )

--}
