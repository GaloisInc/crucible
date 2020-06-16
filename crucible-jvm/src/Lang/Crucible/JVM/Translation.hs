{- |
Module           : Lang.Crucible.JVM.Translation
Description      : Translation of JVM AST into Crucible control-flow graph
Copyright        : (c) Galois, Inc 2018
License          : BSD3
Maintainer       : huffman@galois.com, sweirich@galois.com
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -haddock #-}

module Lang.Crucible.JVM.Translation
  ( translateMethod
  ) where

-- base
import           Control.Monad.State.Strict
import           Control.Lens hiding (op, (:>))
import           Data.Int (Int32)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.String (fromString)

-- jvm-parser
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J
import qualified Language.JVM.CFG as J

-- bv-sized
import qualified Data.BitVector.Sized as BV

-- parameterized-utils
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Parameterized.NatRepr as NR
import           Data.Parameterized.Nonce

-- crucible
import qualified Lang.Crucible.CFG.Core as C
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.CFG.Generator
import           Lang.Crucible.CFG.SSAConversion (toSSA)
import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types
import           Lang.Crucible.Panic

-- what4
import           What4.ProgramLoc (Position(InternalPos))

-- crucible-jvm
import           Lang.Crucible.JVM.Types
import           Lang.Crucible.JVM.Context
import           Lang.Crucible.JVM.Translation.Numeric
import           Lang.Crucible.JVM.Translation.Monad
import           Lang.Crucible.JVM.Translation.Class

import           Debug.Trace

----------------------------------------------------------------------------------------------
-- * Static Overrides

{- Implementation of native methods from the Java library -}

-- | For static methods, there is no need to create an override handle
--   we can just dispatch to our code in the interpreter automatically

staticOverrides :: J.ClassName -> J.MethodKey -> Maybe (JVMStmtGen s ret ())
staticOverrides className methodKey
{-
  | className == "java/lang/StrictMath" && J.methodKeyName methodKey == "sqrt"
  = Just $ do doub <- dPop
              -- TODO: implement sqrt
              dPush doub
-}
  | className == "java/lang/Double" && J.methodKeyName methodKey == "longBitsToDouble"
   = Just $ do lon <- lPop
               -- TODO: this is not correct, we just want to interpret the bits
               let doub = doubleFromLong lon
               dPush doub
  | className == "java/lang/Double" && J.methodKeyName methodKey == "doubleToRawLongBits"
   = Just $ do doub <- dPop
               -- TODO: this is not correct, see
               -- https://docs.oracle.com/javase/8/docs/api/java/lang/Double.html#doubleToLongBits-double-
               let lon = longFromDouble doub
               lPush lon


  | className == "java/lang/System" && J.methodKeyName methodKey == "arraycopy"
  = Just $ do len     <- iPop
              destPos <- iPop
              dest    <- rPop
              srcPos  <- iPop
              src     <- rPop

              rawSrcRef <- throwIfRefNull src
              srcObj  <- lift $ readRef rawSrcRef

              rawDestRef <- throwIfRefNull dest

              -- i = srcPos;
              iReg <- lift $ newReg srcPos

              let end = iAdd srcPos len

              lift $ while (InternalPos, do
                        j <- readReg iReg
                        return $ App $ BVSlt w32 j end)

                    (InternalPos, do
                        j <- readReg iReg

                        --- val = src[i+srcPos]
                        val <- arrayIdx srcObj j

                        -- dest[i+destPos] = val
                        destObj  <- readRef rawDestRef
                        newDestObj <- arrayUpdate destObj (iAdd destPos j) val
                        writeRef rawDestRef newDestObj

                        -- i++;
                        modifyReg iReg (iAdd (iConst 1))
                        )

  | className == "java/lang/System" && J.methodKeyName methodKey == "exit"
  = Just $ do _status <- iPop
              -- TODO: figure out how to exit the simulator
              -- let codeStr = "unknown exit code"
              -- _ <- lift $ returnFromFunction (App EmptyApp)
              -- (App $ TextLit (fromString $ "java.lang.System.exit(int status) called with " ++ codeStr))
              return ()

  -- System.gc is a NOP
  | className == "java/lang/System" && J.methodKeyName methodKey == "gc"
  = Just $ do return ()

  --
  -- Do nothing for registering native state
  --
  | J.methodKeyName methodKey == "registerNatives"
    && className `elem` ["java/lang/System",
                         "java/lang/ClassLoader",
                         "java/lang/Thread",
                         "java/lang/Class"]
  = Just $ return ()

  | className == "java/lang/Arrays" && J.methodKeyName methodKey == "copyOfRange"
  = Nothing

  | className == "java/lang/String" && J.methodKeyName methodKey == "<init>"
  = case (J.methodKeyParameterTypes methodKey) of
         [] -> Just $ return ()
         [J.ArrayType J.CharType, J.IntType, J.IntType] -> Just $ do
           traceM "TODO: 3 arg string constructor unimplemented"
           _count  <- iPop
           _offset <- iPop
           _arrRef <- rPop
           _obj    <- rPop

           -- how do we get access to "this" ??
           return ()
         _ -> Nothing

  | className == "java/io/ObjectStreamField" && J.methodKeyName methodKey == "<init>"
  = trace ("java/io/ObjectStreamField/<init>  " ++ show (J.methodKeyParameterTypes methodKey)) $
    case (J.methodKeyParameterTypes methodKey) of
      [_,_] -> Just $ do
        _name <- rPop    -- String
        _type <- rPop    -- Class
        _obj <-  rPop
        return ()
      [_,_,_] -> Just $ do
        _name <- rPop
        _type <- rPop     -- Class<?>
        _unshared <- iPop -- boolean
        _obj <-  rPop
        return ()

      _ -> Nothing
  | className == "java/lang/Object" && J.methodKeyName methodKey == "hashCode"
  =  Just $ do
        -- TODO: hashCode always returns 0, can we make it be an "abstract" int?
        iPush (App $ BVLit knownRepr (BV.zero knownRepr))

  | className == "java/lang/Class" &&
    J.methodKeyName methodKey == "getPrimitiveClass"
  =  Just $
        do _arg <- rPop
           -- TODO: java reflection
           rPush rNull

  -- valueOf methods
  | [ argTy ] <- J.methodKeyParameterTypes methodKey,
    J.methodKeyName methodKey == "valueOf"
    && (className, argTy) `elem`
    [ ("java/lang/Boolean", J.BooleanType)
    , ("java/lang/Byte", J.ByteType)
    , ("java/lang/Short", J.ShortType)
    , ("java/lang/Integer", J.IntType)
    , ("java/lang/Long", J.LongType)
    ]
  = Just $ do
      val <- popValue
      ref <- lift $ do
        initializeClass className
        clsObj <- getJVMClassByName className
        cls    <- lookupClassGen className
        fids   <- getAllFields cls
        obj    <- newInstanceInstr clsObj fids
        obj1   <- setInstanceFieldValue obj
                  (J.FieldId className "value" argTy)
                  val
        rawRef <- newRef obj1
        return $ App (JustValue knownRepr rawRef)

      rPush ref

  | otherwise = Nothing





----------------------------------------------------------------------
-- * JVMRef

-- | Crucible expression for Java null reference.
rNull :: JVMRef s
rNull = App (NothingValue knownRepr)

-- | Crucible generator to test if reference is null.
rIsNull :: JVMRef s -> JVMGenerator s ret (JVMBool s)
rIsNull mr =
  caseMaybe mr knownRepr
  MatchMaybe {
    onNothing = return bTrue,
    onJust = \_ -> return bFalse
    }

-- | Dynamically test whether two references are equal.
rEqual :: JVMRef s -> JVMRef s -> JVMGenerator s ret (JVMBool s)
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
-- * Registers and stack values

-- | Create a register value from a value with a statically
-- known tag.
newJVMReg :: JVMValue s -> JVMGenerator s ret (JVMReg s)
newJVMReg val =
  case val of
    DValue v -> DReg <$> newReg v
    FValue v -> FReg <$> newReg v
    IValue v -> IReg <$> newReg v
    LValue v -> LReg <$> newReg v
    RValue v -> RReg <$> newReg v

readJVMReg :: JVMReg s -> JVMGenerator s ret (JVMValue s)
readJVMReg reg =
  case reg of
    DReg r -> DValue <$> readReg r
    FReg r -> FValue <$> readReg r
    IReg r -> IValue <$> readReg r
    LReg r -> LValue <$> readReg r
    RReg r -> RValue <$> readReg r

writeJVMReg :: JVMReg s -> JVMValue s -> JVMGenerator s ret ()
writeJVMReg (DReg r) (DValue v) = assignReg r v
writeJVMReg (FReg r) (FValue v) = assignReg r v
writeJVMReg (IReg r) (IValue v) = assignReg r v
writeJVMReg (LReg r) (LValue v) = assignReg r v
writeJVMReg (RReg r) (RValue v) = assignReg r v
writeJVMReg _ _ = jvmFail "writeJVMReg"

newStack :: [JVMValue s] -> JVMGenerator s ret [JVMReg s]
newStack = traverse newJVMReg

readStack :: [JVMReg s] -> JVMGenerator s ret [JVMValue s]
readStack = traverse readJVMReg

saveStack :: [JVMReg s] -> [JVMValue s] -> JVMGenerator s ret ()
saveStack [] [] = return ()
saveStack (r : rs) (v : vs) = writeJVMReg r v >> saveStack rs vs
saveStack _ _ = jvmFail "saveStack"

-- | Look up the register for a local variable of a particular type.
-- Create the register on-the-fly if it does not exist yet.
lookupLocalReg ::
  KnownRepr TypeRepr tp =>
  Lens' (JVMState ret s) (Map J.LocalVariableIndex (Reg s tp)) ->
  J.LocalVariableIndex -> JVMGenerator s ret (Reg s tp)
lookupLocalReg l idx =
  do m <- use l
     case Map.lookup idx m of
       Just r -> return r
       Nothing ->
         do r <- newUnassignedReg knownRepr
            l %= Map.insert idx r
            return r

writeLocal :: J.LocalVariableIndex -> JVMValue s -> JVMGenerator s ret ()
writeLocal idx val =
  case val of
    DValue v -> lookupLocalReg jsLocalsD idx >>= flip assignReg v
    FValue v -> lookupLocalReg jsLocalsF idx >>= flip assignReg v
    IValue v -> lookupLocalReg jsLocalsI idx >>= flip assignReg v
    LValue v -> lookupLocalReg jsLocalsL idx >>= flip assignReg v
    RValue v -> lookupLocalReg jsLocalsR idx >>= flip assignReg v

forceJVMValue :: JVMValue s -> JVMGenerator s ret (JVMValue s)
forceJVMValue val =
  case val of
    DValue v -> DValue <$> forceEvaluation v
    FValue v -> FValue <$> forceEvaluation v
    IValue v -> IValue <$> forceEvaluation v
    LValue v -> LValue <$> forceEvaluation v
    RValue v -> RValue <$> forceEvaluation v

-------------------------------------------------------------------------------
-- * Basic blocks

generateBasicBlock ::
  J.BasicBlock ->
  [JVMReg s] ->
  JVMGenerator s ret a
generateBasicBlock bb rs =
  do -- Record the stack registers for this block.
     -- This also signals that generation of this block has started.
     jsStackMap %= Map.insert (J.bbId bb) rs
     -- Read initial values
     vs <- readStack rs
     -- Translate all instructions
     vs' <- execStateT (mapM_ generateInstruction (J.bbInsts bb)) vs
     -- If we didn't already handle a block-terminating instruction,
     -- jump to the successor block, if there's only one.
     cfg <- use jsCFG
     case J.succs cfg (J.bbId bb) of
       [J.BBId succPC] ->
         do lbl <- processBlockAtPC succPC vs'
            jump lbl
       [] -> jvmFail "generateBasicBlock: no terminal instruction and no successor"
       _  -> jvmFail "generateBasicBlock: no terminal instruction and multiple successors"

-- | Prepare for a branch or jump to the given address, by generating
-- a transition block to copy the stack values into the appropriate
-- registers. If the target has already been translated (or is
-- currently being translated) then the registers already exist, so we
-- simply write into them. If the target has not been started yet, we
-- copy the values into fresh registers, and also recursively call
-- 'generateBasicBlock' on the target block to start translating it.
processBlockAtPC :: HasCallStack => J.PC -> [JVMValue s] -> JVMGenerator s ret (Label s)
processBlockAtPC pc vs =
  defineBlockLabel $
  do bb <- getBasicBlockAtPC pc
     lbl <- getLabelAtPC pc
     sm <- use jsStackMap
     case Map.lookup (J.bbId bb) sm of
       Just rs ->
         do saveStack rs vs
       Nothing ->
         do rs <- newStack vs
            defineBlock lbl (generateBasicBlock bb rs)
     jump lbl

getBasicBlockAtPC :: J.PC -> JVMGenerator s ret J.BasicBlock
getBasicBlockAtPC pc =
  do cfg <- use jsCFG
     case J.bbByPC cfg pc of
       Nothing -> jvmFail "getBasicBlockAtPC"
       Just bb -> return bb

getLabelAtPC :: J.PC -> JVMGenerator s ret (Label s)
getLabelAtPC pc =
  do bb <- getBasicBlockAtPC pc
     lm <- use jsLabelMap
     case Map.lookup (J.bbId bb) lm of
       Nothing -> jvmFail "getLabelAtPC"
       Just lbl -> return lbl



----------------------------------------------------------------------
-- * JVM statement generator monad


-- | This has extra state that is only relevant in the context of a
-- single basic block: It tracks the values of the operand stack at
-- each instruction.
type JVMStmtGen s ret = StateT [JVMValue s] (JVMGenerator s ret)

-- | Indicate that CFG generation failed due to ill-formed JVM code.
sgFail :: HasCallStack => String -> JVMStmtGen s ret a
sgFail msg = lift $ jvmFail msg

sgUnimplemented :: HasCallStack => String -> JVMStmtGen s ret a
sgUnimplemented msg = sgFail $ "unimplemented: " ++ msg

getStack :: JVMStmtGen s ret [JVMValue s]
getStack = get

putStack :: [JVMValue s] -> JVMStmtGen s ret ()
putStack = put

popValue :: HasCallStack => JVMStmtGen s ret (JVMValue s)
popValue =
  do vs <- getStack
     case vs of
       [] -> sgFail "popValue: empty stack"
       (v : vs') ->
         do putStack vs'
            return v

pushValue :: JVMValue s -> JVMStmtGen s ret ()
pushValue v =
  do v' <- lift $ forceJVMValue v
     vs <- getStack
     putStack (v' : vs)

pushValues :: [JVMValue s] -> JVMStmtGen s ret ()
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

popType1 :: HasCallStack => JVMStmtGen s ret (JVMValue s)
popType1 =
  do v <- popValue
     if isType1 v then return v else sgFail "popType1"

popType2 :: HasCallStack => JVMStmtGen s ret [JVMValue s]
popType2 =
  do vs <- getStack
     case vs of
       v : vs' | isType2 v ->
         putStack vs' >> return [v]
       v1 : v2 : vs' | isType1 v1 && isType1 v2 ->
         putStack vs' >> return [v1, v2]
       _ ->
         sgFail "popType2"


iPop :: JVMStmtGen s ret (JVMInt s)
iPop = popValue >>= lift . fromIValue

iPopNonzero :: JVMStmtGen s ret (JVMInt s)
iPopNonzero =
  do v <- iPop
     lift $ assertExpr (App (BVNonzero knownNat v)) "java/lang/ArithmeticException"
     return v

lPop :: JVMStmtGen s ret (JVMLong s)
lPop = popValue >>= lift . fromLValue

lPopNonzero :: JVMStmtGen s ret (JVMLong s)
lPopNonzero =
  do v <- lPop
     lift $ assertExpr (App (BVNonzero knownNat v)) "java/lang/ArithmeticException"
     return v

rPop :: HasCallStack => JVMStmtGen s ret (JVMRef s)
rPop = popValue >>= lift . fromRValue

dPop :: JVMStmtGen s ret (JVMDouble s)
dPop = popValue >>= lift . fromDValue

fPop :: JVMStmtGen s ret (JVMFloat s)
fPop = popValue >>= lift . fromFValue

iPush :: JVMInt s -> JVMStmtGen s ret ()
iPush i = pushValue (IValue i)

lPush :: JVMLong s -> JVMStmtGen s ret ()
lPush l = pushValue (LValue l)

fPush :: JVMFloat s -> JVMStmtGen s ret ()
fPush f = pushValue (FValue f)

dPush :: JVMDouble s -> JVMStmtGen s ret ()
dPush d = pushValue (DValue d)

rPush :: JVMRef s -> JVMStmtGen s ret ()
rPush r = pushValue (RValue r)

uPush :: Expr JVM s UnitType -> JVMStmtGen s ret ()
uPush _u = return ()


setLocal :: J.LocalVariableIndex -> JVMValue s -> JVMStmtGen s ret ()
setLocal idx v = lift (writeLocal idx v)

iLoad :: J.LocalVariableIndex -> JVMStmtGen s ret (JVMInt s)
iLoad idx = lift (lookupLocalReg jsLocalsI idx >>= readReg)

lLoad :: J.LocalVariableIndex -> JVMStmtGen s ret (JVMLong s)
lLoad idx = lift (lookupLocalReg jsLocalsL idx >>= readReg)

fLoad :: J.LocalVariableIndex -> JVMStmtGen s ret (JVMFloat s)
fLoad idx = lift (lookupLocalReg jsLocalsF idx >>= readReg)

dLoad :: J.LocalVariableIndex -> JVMStmtGen s ret (JVMDouble s)
dLoad idx = lift (lookupLocalReg jsLocalsD idx >>= readReg)

rLoad :: J.LocalVariableIndex -> JVMStmtGen s ret (JVMRef s)
rLoad idx = lift (lookupLocalReg jsLocalsR idx >>= readReg)


throwIfRefNull ::
  JVMRef s -> JVMStmtGen s ret (Expr JVM s (ReferenceType JVMObjectType))
throwIfRefNull r = lift $ assertedJustExpr r "null dereference"

----------------------------------------------------------------------

nextPC :: J.PC -> JVMStmtGen s ret J.PC
nextPC pc =
  do cfg <- lift $ use jsCFG
     case J.nextPC cfg pc of
       Nothing -> sgFail "nextPC"
       Just pc' -> return pc'

----------------------------------------------------------------------

pushRet ::
  forall s ret tp. HasCallStack => TypeRepr tp -> Expr JVM s tp -> JVMStmtGen s ret ()
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
      forall t. (HasCallStack, KnownRepr TypeRepr t) =>
      (Expr JVM s t -> JVMStmtGen s ret ()) ->
      JVMStmtGen s ret () -> JVMStmtGen s ret ()
    tryPush push k =
      case testEquality tp (knownRepr :: TypeRepr t) of
        Just Refl -> push expr
        Nothing -> k

popArgument ::
  forall tp s ret. HasCallStack => TypeRepr tp -> JVMStmtGen s ret (Expr JVM s tp)
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
      JVMStmtGen s ret (Expr JVM s t) ->
      JVMStmtGen s ret (Expr JVM s tp) ->
      JVMStmtGen s ret (Expr JVM s tp)
    tryPop pop k =
      case testEquality tp (knownRepr :: TypeRepr t) of
        Just Refl -> pop
        Nothing -> k

-- | Pop arguments from the stack; the last argument should be at the
-- top of the stack.
popArguments ::
  forall args s ret.
  HasCallStack => CtxRepr args -> JVMStmtGen s ret (Ctx.Assignment (Expr JVM s) args)
popArguments args =
  case Ctx.viewAssign args of
    Ctx.AssignEmpty -> return Ctx.empty
    Ctx.AssignExtend tps tp ->
      do x <- popArgument tp
         xs <- popArguments tps
         return (Ctx.extend xs x)

----------------------------------------------------------------------

-- * Instruction generation

bTrue :: JVMBool s
bTrue = App (BoolLit True)

bFalse :: JVMBool s
bFalse = App (BoolLit False)


-- | Do the heavy lifting of translating JVM instructions to crucible code.
generateInstruction ::
  forall s ret. HasCallStack =>
  (J.PC, J.Instruction) ->
  JVMStmtGen s ret ()
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
    J.Dcmpg -> binary dPop dPop iPush dCmpg
    J.Dcmpl -> binary dPop dPop iPush dCmpl
    J.Fadd  -> binary fPop fPop fPush fAdd
    J.Fsub  -> binary fPop fPop fPush fSub
    J.Fneg  -> unary fPop fPush fNeg
    J.Fmul  -> binary fPop fPop fPush fMul
    J.Fdiv  -> binary fPop fPop fPush fDiv
    J.Frem  -> binary fPop fPop fPush fRem
    J.Fcmpg -> binary fPop fPop iPush fCmpg
    J.Fcmpl -> binary fPop fPop iPush fCmpl
    J.Iadd  -> binary iPop iPop iPush iAdd
    J.Isub  -> binary iPop iPop iPush iSub
    J.Imul  -> binary iPop iPop iPush iMul
    J.Idiv  -> binary iPop iPopNonzero iPush iDiv
    J.Irem  -> binary iPop iPopNonzero iPush iRem
    J.Ineg  -> unary iPop iPush iNeg
    J.Iand  -> binary iPop iPop iPush iAnd
    J.Ior   -> binary iPop iPop iPush iOr
    J.Ixor  -> binary iPop iPop iPush iXor
    J.Ishl  -> binary iPop iPop iPush iShl
    J.Ishr  -> binary iPop iPop iPush iShr
    J.Iushr -> binary iPop iPop iPush iUshr
    J.Ladd  -> binary lPop lPop lPush lAdd
    J.Lsub  -> binary lPop lPop lPush lSub
    J.Lmul  -> binary lPop lPop lPush lMul
    J.Lneg  -> unary lPop lPush lNeg
    J.Ldiv  -> binary lPop lPopNonzero lPush lDiv
    J.Lrem  -> binary lPop lPopNonzero lPush lRem
    J.Land  -> binary lPop lPop lPush lAnd
    J.Lor   -> binary lPop lPop lPush lOr
    J.Lxor  -> binary lPop lPop lPush lXor
    J.Lcmp  -> binary lPop lPop iPush lCmp
    J.Lshl  -> binary lPop iPop lPush lShl
    J.Lshr  -> binary lPop iPop lPush lShr
    J.Lushr -> binary lPop iPop lPush lUshr

    -- Load and store instructions
    J.Iload idx -> iLoad idx >>= iPush
    J.Lload idx -> lLoad idx >>= lPush
    J.Fload idx -> fLoad idx >>= fPush
    J.Dload idx -> dLoad idx >>= dPush
    J.Aload idx -> rLoad idx >>= rPush

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


    J.New name  -> do
      lift $ debug 2 $ "new " ++ show name ++ " (start)"
      cls    <- lift $ lookupClassGen name
      clsObj <- lift $ getJVMClass cls
      -- find the fields not just in this class, but also in the super classes
      fields <- lift $ getAllFields cls
      lift $ debug 3 $ "fields are " ++ show fields
      obj    <- lift $ newInstanceInstr clsObj fields
      rawRef <- lift $ newRef obj
      lift $ debug 2 $ "new " ++ show name ++ " (finish)"
      rPush $ App (JustValue knownRepr rawRef)

    J.Getfield fieldId -> do
      lift $ debug 2 $ "getfield " ++ show (fieldIdText fieldId)
      objectRef <- rPop
      rawRef <- throwIfRefNull objectRef
      obj <- lift $ readRef rawRef
      val <- lift $ getInstanceFieldValue obj fieldId
      pushValue val

    J.Putfield fieldId -> do
      lift $ debug 2 $ "putfield " ++ show (fieldIdText fieldId)
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


    -- array creation
    J.Newarray arrayType -> do
      count  <- iPop
      obj    <- lift $ newArray count arrayType
      rawRef <- lift $ newRef obj
      rPush (App $ JustValue knownRepr rawRef)

    J.Multianewarray arrType dimensions -> do
      counts <- reverse <$> sequence (replicate (fromIntegral dimensions) iPop)
      obj    <- lift $ newMultiArray arrType counts
      rawRef <- lift $ newRef obj
      rPush (App $ JustValue knownRepr rawRef)

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
    J.Invokevirtual (J.ClassType className) methodKey ->
      generateInstruction (pc, J.Invokeinterface className methodKey)

    J.Invokevirtual (J.ArrayType _ty) methodKey ->
      sgFail $ "TODO: invoke virtual " ++ show (J.methodKeyName methodKey)
                                       ++ " unsupported for arrays"

    J.Invokevirtual   tp        _methodKey ->
      sgFail $ "Invalid static type for invokevirtual " ++ show tp

    -- Dynamic dispatch through an interface
    J.Invokeinterface className methodKey -> do
      let mname = J.unClassName className ++ "/" ++ J.methodKeyName methodKey
      lift $ debug 2 $ "invoke: " ++ mname

      -- find the static type of the method (without this!)
      let argTys = Ctx.fromList (map javaTypeToRepr (J.methodKeyParameterTypes methodKey))
      let retTy  = maybe (Some C.UnitRepr) javaTypeToRepr (J.methodKeyReturnType methodKey)

      case (argTys, retTy) of
        (Some argRepr, Some retRepr) -> do

            args <- popArguments argRepr
            objRef <- rPop

            rawRef <- throwIfRefNull objRef
            result <- lift $ do
              obj    <- readRef rawRef
              cls    <- getJVMInstanceClass obj
              anym   <- findDynamicMethod cls methodKey

              let argRepr' = (Ctx.empty `Ctx.extend` (knownRepr :: TypeRepr JVMRefType)) Ctx.<++> argRepr
              fn     <- assertedJustExpr (App (UnpackAny (FunctionHandleRepr argRepr' retRepr) anym))
                        (App $ StringLit $ fromString ("invalid method type:"
                                      ++ show (FunctionHandleRepr argRepr' retRepr)
                                      ++ " for "
                                      ++ show methodKey))
              call fn (Ctx.empty `Ctx.extend` objRef Ctx.<++> args)

            pushRet retRepr result
            lift $ debug 2 $ "finish invoke:" ++ mname

    J.Invokespecial   (J.ClassType methodClass) methodKey ->
      -- treat constructor invocations like static methods
      generateInstruction (pc, J.Invokestatic methodClass methodKey)

    J.Invokespecial   tp _methodKey ->
      -- TODO
      sgUnimplemented $ "Invokespecial for " ++ show tp

    J.Invokestatic    className methodKey
      | Just action <- staticOverrides className methodKey
      -- look for a static override for this class and run that
      -- instead
      ->  do let mname = J.unClassName className ++ "/" ++ J.methodKeyName methodKey
             lift $ debug 2 $ "invoke static: " ++ mname
             action

      | otherwise ->
        -- make sure that *this* class has already been initialized
        do lift $ initializeClass className
           (JVMHandleInfo _ handle) <- lift $ getStaticMethod className methodKey
           args <- popArguments (handleArgTypes handle)
           result <- lift $ call (App (HandleLit handle)) args
           pushRet (handleReturnType handle) result

    J.Invokedynamic   _word16 ->
      -- TODO
      sgUnimplemented "TODO: Invokedynamic needs more support from jvm-parser"

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
         len <- lift $ arrayLength obj
         iPush len

    J.Athrow ->
      do objectRef <- rPop
         _obj <- throwIfRefNull objectRef

         -- For now, we assert that exceptions won't happen
         lift $ reportError (App $ StringLit $ fromString "athrow")
         --throw objectRef


    J.Checkcast ty  ->
      do objectRef <- rPop
         lift $ checkCast objectRef ty
         rPush objectRef

    J.Iinc idx constant ->
      do value <- iLoad idx
         let constValue = iConst (fromIntegral constant)
         setLocal idx (IValue (iAdd value constValue))

    J.Instanceof tTy ->
      -- instanceof returns False when argument is null
      do objectRef <- rPop
         b <- lift $ caseMaybe objectRef knownRepr
           MatchMaybe
           { onNothing = return bFalse
           , onJust    = \rawRef -> do
               obj <- readRef rawRef
               sTy <- getObjectType obj
               isSubType sTy tTy
           }
         iPush $ iIte b (iConst 1) (iConst 0)

    J.Monitorenter ->
      do void rPop
    J.Monitorexit ->
      do void rPop
    J.Nop ->
      do return ()

unary ::
  JVMStmtGen s ret a ->
  (b -> JVMStmtGen s ret ()) ->
  (a -> b) ->
  JVMStmtGen s ret ()
unary pop push op =
  do value <- pop
     push (op value)

binary ::
  JVMStmtGen s ret a ->
  JVMStmtGen s ret b ->
  (c -> JVMStmtGen s ret ()) ->
  (a -> b -> c) ->
  JVMStmtGen s ret ()
binary pop1 pop2 push op =
  do value2 <- pop2
     value1 <- pop1
     push (value1 `op` value2)


aloadInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  (Expr JVM s t -> JVMValue s) ->
  JVMStmtGen s ret ()
aloadInstr tag mkVal =
  do idx <- iPop
     arrayRef <- rPop
     rawRef <- throwIfRefNull arrayRef
     obj <- lift $ readRef rawRef
     val <- lift $ arrayIdx obj idx
     let mx = App (ProjectVariant knownRepr tag val)
     x <- lift $ assertedJustExpr mx "aload: invalid element type"
     pushValue (mkVal x)

astoreInstr ::
  KnownRepr TypeRepr t =>
  Ctx.Index JVMValueCtx t ->
  (Expr JVM s t -> Expr JVM s t) ->
  Expr JVM s t ->
  JVMStmtGen s ret ()
astoreInstr tag f x =
  do idx <- iPop
     arrayRef <- rPop
     rawRef <- throwIfRefNull arrayRef
     obj <- lift $ readRef rawRef
     let val = App (InjectVariant knownRepr tag (f x))
     obj' <- lift $ arrayUpdate obj idx val
     lift $ writeRef rawRef obj'

icmpInstr ::
  J.PC {- ^ previous PC -} ->
  J.PC {- ^ branch target -} ->
  (JVMInt s -> JVMInt s -> JVMBool s) ->
  JVMStmtGen s ret ()
icmpInstr pc_old pc_t cmp =
  do i2 <- iPop
     i1 <- iPop
     pc_f <- nextPC pc_old
     branchIf (cmp i1 i2) pc_t pc_f

ifInstr ::
  J.PC {- ^ previous PC -} ->
  J.PC {- ^ branch target -} ->
  (JVMInt s -> JVMBool s) ->
  JVMStmtGen s ret ()
ifInstr pc_old pc_t cmp =
  do i <- iPop
     pc_f <- nextPC pc_old
     branchIf (cmp i) pc_t pc_f

branchIf ::
  JVMBool s ->
  J.PC {- ^ true label -} ->
  J.PC {- ^ false label -} ->
  JVMStmtGen s ret ()
branchIf cond pc_t pc_f =
  do vs <- get
     lbl_t <- lift $ processBlockAtPC pc_t vs
     lbl_f <- lift $ processBlockAtPC pc_f vs
     lift $ branch cond lbl_t lbl_f

switchInstr ::
  J.PC {- ^ default target -} ->
  [(Int32, J.PC)] {- ^ jump table -} ->
  JVMInt s {- ^ scrutinee -} ->
  JVMStmtGen s ret ()
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
  forall s ret tp.
  KnownRepr TypeRepr tp =>
  JVMStmtGen s ret (Expr JVM s tp) ->
  JVMStmtGen s ret ()
returnInstr pop =
  do retType <- lift $ jsRetType <$> get
     case testEquality retType (knownRepr :: TypeRepr tp) of
       Just Refl -> pop >>= (lift . returnFromFunction)
       Nothing -> sgFail "ireturn: type mismatch"

----------------------------------------------------------------------

-- * Method translation (`generateMethod`)

-- | Given a JVM type and a type context and a register assignment,
-- peel off the rightmost register from the assignment, which is
-- expected to match the given LLVM type. Pass the register and the
-- remaining type and register context to the given continuation.
--
-- This procedure is used to set up the initial state of the registers
-- at the entry point of a function.
packTypes ::
  HasCallStack => [J.Type] ->
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

-- | Create the initial set of local variables for a method translation.
initialJVMLocalVars :: HasCallStack =>
  J.ClassName ->
  J.Method ->
  CtxRepr ctx ->
  Ctx.Assignment (Atom s) ctx ->
  Map J.LocalVariableIndex (JVMValue s)
initialJVMLocalVars cn method ctx asgn = locals
  where
    args = J.methodParameterTypes method
    static = J.methodIsStatic method
    args' = if static then args else J.ClassType cn : args
    vals = reverse (packTypes (reverse args') ctx asgn)
    idxs = J.methodParameterIndexes method
    idxs' = if static then idxs else 0 : idxs
    locals = Map.fromList (zip idxs' vals)


-- | Generate the CFG for a Java method.
generateMethod ::
  J.ClassName ->
  J.Method ->
  CtxRepr init ->
  Ctx.Assignment (Atom s) init ->
  JVMGenerator s ret a
generateMethod cn method ctx asgn =
  do let cfg = methodCFG method
     let bbLabel bb = (,) (J.bbId bb) <$> newLabel
     lbls <- traverse bbLabel (J.allBBs cfg)
     jsLabelMap .= Map.fromList lbls
     bb0 <- maybe (jvmFail "no entry block") return (J.bbById cfg J.BBIdEntry)
     -- initialize local variables with method arguments
     _ <- Map.traverseWithKey writeLocal (initialJVMLocalVars cn method ctx asgn)
     generateBasicBlock bb0 []


-- | Top-level function for method translation.
translateMethod :: JVMContext
                 -> Verbosity
                 -> J.ClassName
                 -> J.Method
                 -> FnHandle args ret
                 -> IO (C.SomeCFG JVM args ret)
translateMethod ctx verbosity cName m h =
  case (handleArgTypes h, handleReturnType h) of
    ((argTypes :: CtxRepr args), (retType :: TypeRepr ret)) -> do
      let  def :: FunctionDef JVM (JVMState ret) args ret IO
           def inputs = (s, f)
             where s = initialState ctx verbosity m retType
                   f = generateMethod cName m argTypes inputs
      sng <- newIONonceGenerator
      (SomeCFG g, []) <- defineFunction InternalPos sng h def
      return $ toSSA g
