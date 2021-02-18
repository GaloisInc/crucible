{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.Wasm.Translate where

import Control.Monad
import Control.Monad.State.Strict
import Data.Foldable(toList)
import Data.Word
import Numeric.Natural
import GHC.Stack

import qualified Data.Sequence as Seq

import Data.Parameterized.Context
import Data.Parameterized.Some
import Data.Parameterized.Nonce

import qualified Data.BitVector.Sized as BV
import Data.List (genericDrop)

import qualified Language.Wasm.Structure as Wasm

import qualified Lang.Crucible.Simulator as Sim
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types

import Lang.Crucible.Analysis.Postdom
import Lang.Crucible.CFG.Generator
import qualified Lang.Crucible.CFG.Core as C
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.SSAConversion

import What4.ProgramLoc
import What4.Utils.StringLiteral

import Lang.Crucible.Wasm.Extension
import Lang.Crucible.Wasm.Memory
import Lang.Crucible.Wasm.Instantiate
import Lang.Crucible.Wasm.Utils

translateFunctions ::
  ModuleInstance ->
  Store ->
  IO [Sim.FnBinding p sym WasmExt]
translateFunctions im st = sequence
  [ case Seq.lookup addr (storeFuncs st) of
      Nothing -> panic "translateFunction" ["function not found"]
      Just (SomeHandle h) -> translateFunction fty fn im st h
  | (fty,Just fn,addr) <- toList (instFuncAddrs im)
  ]

type WasmGenerator s ret = Generator WasmExt s WasmGenState ret IO

data WasmGenState s =
  WasmGenState
  { genLocals :: Seq.Seq (Some (Reg s))
     -- ^ Function-local variables
  , genStack  :: Seq.Seq (StackVal s)
     -- ^ Value stack.  Back/right end of the sequence is
     --   the working end of the stack to match the
     --   order presented in the Wasm specification.
  }

emptyGenState :: WasmGenState s
emptyGenState =
  WasmGenState
  { genLocals = mempty
  , genStack  = mempty
  }

addLocal :: Reg s tp -> WasmGenState s -> WasmGenState s
addLocal r st = st{ genLocals = genLocals st Seq.|> Some r }

data StackVal s
  = StackI32 (Atom s (BVType 32))
  | StackI64 (Atom s (BVType 64))
  | StackF32 (Atom s (FloatType SingleFloat))
  | StackF64 (Atom s (FloatType DoubleFloat))

  | StackBool (Atom s BoolType)
    -- ^ A @StackBool@ constructor represents a delayed coersion of a boolean
    --   value into a bitvector.  Boolean values do not exist in the Wasm
    --   spec; but we represent them explicitly to avoid noisy round trip
    --   expressions that coerce to and from bitvectors.
    --   Where boolean stack values appear, they should be understood as
    --   representing either the 0 or the 1 value of the appropriate
    --   bitvector size.

class PushStack s x where
  pushStack :: x -> WasmGenerator s ret ()

instance PushStack s (StackVal s) where
  pushStack x = modify (\st -> st{ genStack = genStack st Seq.|> x })

instance PushStack s (Atom s BoolType) where
  pushStack = pushStack . StackBool

instance PushStack s (Atom s (BVType 32)) where
  pushStack = pushStack . StackI32

instance PushStack s (Atom s (BVType 64)) where
  pushStack = pushStack . StackI64

instance PushStack s (Atom s (FloatType SingleFloat)) where
  pushStack = pushStack . StackF32

instance PushStack s (Atom s (FloatType DoubleFloat)) where
  pushStack = pushStack . StackF64

instance PushStack s (Atom s tp) => PushStack s (Expr WasmExt s tp) where
  pushStack x = pushStack =<< mkAtom x

instance PushStack s Word32 where
  pushStack x = pushStack =<< mkAtom (App (BVLit (knownNat @32) (BV.word32 x)))

instance PushStack s Word64 where
  pushStack x = pushStack =<< mkAtom (App (BVLit (knownNat @64) (BV.word64 x)))

instance PushStack s Float where
  pushStack x = pushStack =<< mkAtom (App (FloatLit x))

instance PushStack s Double where
  pushStack x = pushStack =<< mkAtom (App (DoubleLit x))

instance PushStack s ConstantValue where
  pushStack (I32Val x) = pushStack x
  pushStack (I64Val x) = pushStack x
  pushStack (F32Val x) = pushStack x
  pushStack (F64Val x) = pushStack x


iteVals ::
  Expr WasmExt s BoolType ->
  StackVal s ->
  StackVal s ->
  WasmGenerator s ret (StackVal s)

-- promote boolean values as required
iteVals c (StackI32 x) (StackBool b) =
  do y <- mkAtom (App (BoolToBV knownNat (AtomExpr b)))
     iteVals c (StackI32 x) (StackI32 y)
iteVals c (StackI64 x) (StackBool b) =
  do y <- mkAtom (App (BoolToBV knownNat (AtomExpr b)))
     iteVals c (StackI64 x) (StackI64 y)
iteVals c (StackBool b) (StackI32 y) =
  do x <- mkAtom (App (BoolToBV knownNat (AtomExpr b)))
     iteVals c (StackI32 x) (StackI32 y)
iteVals c (StackBool b) (StackI64 y) =
  do x <- mkAtom (App (BoolToBV knownNat (AtomExpr b)))
     iteVals c (StackI64 x) (StackI64 y)

iteVals c (StackBool x) (StackBool y) =
  StackBool <$> mkAtom (App (BoolIte c (AtomExpr x) (AtomExpr y)))

iteVals c (StackI32 x) (StackI32 y) =
  StackI32 <$> mkAtom (App (BVIte c knownRepr (AtomExpr x) (AtomExpr y)))

iteVals c (StackI64 x) (StackI64 y) =
  StackI64 <$> mkAtom (App (BVIte c knownRepr (AtomExpr x) (AtomExpr y)))

iteVals c (StackF32 x) (StackF32 y) =
  StackF32 <$> mkAtom (App (FloatIte knownRepr c (AtomExpr x) (AtomExpr y)))

iteVals c (StackF64 x) (StackF64 y) =
  StackF64 <$> mkAtom (App (FloatIte knownRepr c (AtomExpr x) (AtomExpr y)))

iteVals _ _ _ = panic "iteVals" ["Type mismatch in iteVals"]


pushStackByType :: HasCallStack => TypeRepr t -> Expr WasmExt s t -> WasmGenerator s reg ()
pushStackByType t x = pushStack =<< stackValueByType t x

stackValueByType :: HasCallStack => TypeRepr t -> Expr WasmExt s t -> WasmGenerator s reg (StackVal s)
stackValueByType (BVRepr w) x
  | Just Refl <- testEquality w (knownNat @32)  = StackI32 <$> mkAtom x
  | Just Refl <- testEquality w (knownNat @64)  = StackI64 <$> mkAtom x
stackValueByType (FloatRepr SingleFloatRepr) x  = StackF32 <$> mkAtom x
stackValueByType (FloatRepr DoubleFloatRepr) x  = StackF64 <$> mkAtom x
stackValueByType t _ = panic "stackValueByType" ["invalid type " ++ show t]

checkStackVal :: TypeRepr ty -> StackVal s -> WasmGenerator s ret (Expr WasmExt s ty)
checkStackVal (BVRepr w) (StackI32 x)
   | Just Refl <- testEquality w (knownNat @32) = pure (AtomExpr x)
checkStackVal (BVRepr w) (StackI64 x)
   | Just Refl <- testEquality w (knownNat @64) = pure (AtomExpr x)
checkStackVal (BVRepr w) (StackBool b)
   | Just Refl <- testEquality w (knownNat @32) = pure (App (BoolToBV knownNat (AtomExpr b)))
   | Just Refl <- testEquality w (knownNat @64) = pure (App (BoolToBV knownNat (AtomExpr b)))
checkStackVal (FloatRepr SingleFloatRepr) (StackF32 x) = pure (AtomExpr x)
checkStackVal (FloatRepr DoubleFloatRepr) (StackF64 x) = pure (AtomExpr x)
checkStackVal _ _ = panic "checkStackVal" ["Type mismatch!"]


pushInteger :: NatRepr w -> Expr WasmExt s (BVType w) -> WasmGenerator s reg ()
pushInteger w x
  | Just Refl <- testEquality w (knownNat @32) = pushStack . StackI32 =<< mkAtom x
  | Just Refl <- testEquality w (knownNat @64) = pushStack . StackI64 =<< mkAtom x
  | otherwise = panic "pushInteger" ["invalid size " ++ show w]

peekStack :: HasCallStack => WasmGenerator s ret (StackVal s)
peekStack =
  do st <- get
     case genStack st of
       Seq.Empty -> panic "peekStack" ["empty stack"]
       _stk' Seq.:|> x -> pure x

popStack :: HasCallStack => WasmGenerator s ret (StackVal s)
popStack =
  do st <- get
     case genStack st of
       Seq.Empty -> panic "popStack" ["empty stack"]
       stk' Seq.:|> x -> put st{ genStack = stk' } >> pure x

popFloat :: HasCallStack => WasmGenerator s ret (Expr WasmExt s (FloatType SingleFloat))
popFloat = popStack >>= \case
  StackF32 f -> pure (AtomExpr f)
  _ -> panic "popFloat" ["unexpected type"]

popDouble :: HasCallStack => WasmGenerator s ret (Expr WasmExt s (FloatType DoubleFloat))
popDouble = popStack >>= \case
  StackF64 d -> pure (AtomExpr d)
  _ -> panic "popDouble" ["unexpected type"]

popInteger :: (1 <= w, HasCallStack) => NatRepr w -> WasmGenerator s ret (Expr WasmExt s (BVType w))
popInteger w = popStack >>= \case
  StackBool b -> pure (App (BoolToBV w (AtomExpr b)))
  StackI32 x
    | Just Refl <- testEquality w (knownNat @32) -> pure (AtomExpr x)
  StackI64 x
    | Just Refl <- testEquality w (knownNat @64) -> pure (AtomExpr x)
  _ -> panic "popInteger"  ["unexpected type"]

popInteger32 :: HasCallStack => WasmGenerator s ret (Expr WasmExt s (BVType 32))
popInteger32 = popStack >>= \case
  StackBool b -> pure (App (BoolToBV knownNat (AtomExpr b)))
  StackI32 x -> pure (AtomExpr x)
  _ -> panic "popInteger32" ["unexpected type"]

popInteger64 :: HasCallStack => WasmGenerator s ret (Expr WasmExt s (BVType 64))
popInteger64 = popStack >>= \case
  StackBool b -> pure (App (BoolToBV knownNat (AtomExpr b)))
  StackI64 x -> pure (AtomExpr x)
  _ -> panic "popInteger64" ["unexpected type"]

popPointer :: HasCallStack => Wasm.MemArg -> WasmGenerator s ret (Expr WasmExt s (BVType 32))
popPointer Wasm.MemArg{ offset = o }
  | o == 0 = popInteger32
  | otherwise =
  do x <- popInteger32
     let off = (App (BVLit knownNat (BV.mkBV knownNat (toInteger o))))
     forceEvaluation (App (BVAdd knownNat x off))

popTest :: HasCallStack => WasmGenerator s reg (Expr WasmExt s BoolType)
popTest = popStack >>= \case
  StackBool b -> pure (AtomExpr b)
  StackI32 x  -> pure (App (BVNonzero knownNat (AtomExpr x)))
  _ -> panic "popTest" ["unexpected type"]


pushStackN :: Seq.Seq (StackVal s) -> WasmGenerator s ret ()
pushStackN vals = modify (\st -> st{ genStack = genStack st <> vals })

popStackN :: HasCallStack => Int -> WasmGenerator s ret (Seq.Seq (StackVal s))
popStackN n =
  do st <- get
     let toDrop = Seq.length (genStack st) - n
     if toDrop >= 0 then
       do let (stk',xs) = Seq.splitAt toDrop (genStack st)
          put st{ genStack = stk' }
          return xs
     else
       panic "popStackN" ["too many values to pop:" ++ show n, "Stack height:" ++ show (Seq.length (genStack st))]

restoreStack :: WasmGenerator s ret a -> WasmGenerator s ret a
restoreStack m =
  do stk <- genStack <$> get
     x <- m
     modify (\st -> st{ genStack = stk })
     pure x

translateFunction :: forall p sym args ret.
  Wasm.FuncType ->
  Wasm.Function ->
  ModuleInstance ->
  Store ->
  FnHandle args ret ->
  IO (Sim.FnBinding p sym WasmExt)
translateFunction fty fn@Wasm.Function{ .. } im st hdl =
  do debug $ unlines ["Translating function", show fn]
     (SomeCFG g, []) <- defineFunction InternalPos (Some globalNonceGenerator) hdl defn
     case toSSA g of
       C.SomeCFG g' ->
         do debug (show g')
            pure (Sim.FnBinding hdl (Sim.UseCFG g' (postdomInfo g')))

  where
  defn :: FunctionDef WasmExt WasmGenState args ret IO
  defn args = (emptyGenState, setupLocals args >> genBody)

  setupLocals :: Assignment (Atom s) args -> WasmGenerator s ret ()
  setupLocals args =
    do traverseWithIndex_ setupArgument args
       mapM_ setupLocal localTypes

  setupArgument :: Index ctx tp -> Atom s tp -> WasmGenerator s ret ()
  setupArgument _idx inputArg =
    do r <- newReg (AtomExpr inputArg)
       modify (addLocal r)

  setupLocal :: Wasm.ValueType -> WasmGenerator s ret ()
  setupLocal Wasm.I32 =
    do r <- newReg (App (BVLit (knownNat @32) (BV.zero knownNat)))
       modify (addLocal r)
  setupLocal Wasm.I64 =
    do r <- newReg (App (BVLit (knownNat @64) (BV.zero knownNat)))
       modify (addLocal r)
  setupLocal Wasm.F32 =
    do r <- newReg (App (FloatLit 0.0))
       modify (addLocal r)
  setupLocal Wasm.F64 =
    do r <- newReg (App (DoubleLit 0.0))
       modify (addLocal r)

  genReturn :: WasmGenerator s ret (Expr WasmExt s ret)
  genReturn = computeReturn (handleReturnType hdl) (Wasm.results fty)

  genBody :: WasmGenerator s ret (Expr WasmExt s ret)
  genBody =
    do let body' = Wasm.Block (Wasm.results fty) body
       genInstruction (genReturn >>= returnFromFunction) im st [] body'
       genReturn

-- | Control-flow labels, together with registers that
--   are used for passing stack values between labels.
--   Note: front/left end of the sequence is the working
--   end of the stack so relative indexing works as expected.
type ControlStack s = [ControlLabel s]

type ControlLabel s = (Label s, Seq.Seq (Some (Reg s)))

setupWasmLabel :: [Wasm.ValueType] -> WasmGenerator s ret (ControlLabel s)
setupWasmLabel vts = do
    regs <- Seq.fromList <$> mapM allocReg vts
    l    <- newLabel
    pure (l, regs)
  where
    allocReg = traverseSome newUnassignedReg . valueTypeToType

jumpToWasmLabel :: ControlLabel s -> Seq.Seq (StackVal s) -> WasmGenerator s ret a
jumpToWasmLabel (l, regs) vals =
  do assignLabelRegs (l,regs) vals
     jump l

assignLabelRegs :: ControlLabel s -> Seq.Seq (StackVal s) -> WasmGenerator s ret ()
assignLabelRegs (_,regs) vals = mapM_ asgn (Seq.zip regs vals)
 where
   asgn :: (Some (Reg s), StackVal s) -> WasmGenerator s ret ()
   asgn (Some r, a) = assignReg r =<< checkStackVal (typeOfReg r) a

setupLabelStack :: Seq.Seq (Some (Reg s)) -> WasmGenerator s ret ()
setupLabelStack regs =
    do vals <- traverse rd regs
       pushStackN vals
 where
  rd :: Some (Reg s) -> WasmGenerator s reg (StackVal s)
  rd (Some r) = stackValueByType (typeOfReg r) =<< readReg r

popControlStack :: Natural -> ControlStack s -> WasmGenerator s reg (ControlLabel s)
popControlStack n stk =
  case genericDrop n stk of
    []    -> panic "popControlStack" ["control stack too short:" ++ show n, "control stack height: " ++ show (length stk)]
    (x:_) -> pure x

computeArgs ::
  Assignment TypeRepr ctx ->
  [Wasm.ValueType] ->
  WasmGenerator s ret (Assignment (Expr WasmExt s) ctx)
computeArgs ctx ts =
  do xs <- popStackN (length ts)
     traverseWithIndex (checkArgVal xs) ctx

computeReturn :: forall s ret. HasCallStack => TypeRepr ret -> [Wasm.ValueType] -> WasmGenerator s ret (Expr WasmExt s ret)
computeReturn UnitRepr [] =
    pure (App EmptyApp)
computeReturn r [_] =
    checkStackVal r =<< popStack
computeReturn (StructRepr rtys) ts | length ts >= 2 =
    do xs <- popStackN (length ts)
       rets <- traverseWithIndex (checkArgVal xs) rtys
       pure (App (MkStruct rtys rets))
computeReturn _ _ = panic "computeReturn" ["Type mismatch at return!"]

checkArgVal :: HasCallStack => Seq.Seq (StackVal s) -> Index ctx ty -> TypeRepr ty -> WasmGenerator s ret (Expr WasmExt s ty)
checkArgVal xs idx ty =
  case Seq.lookup (indexVal idx) xs of
    Just a -> checkStackVal ty a
    _ -> panic "checkArgVal" ["Type mismatch!"]

getMemVar :: HasCallStack => ModuleInstance -> Store -> WasmGenerator s ret (GlobalVar WasmMem)
getMemVar im st =
   -- memory index hardcoded to 0
   case resolveMemIndex 0 im of
     Nothing -> panic "getMemVar" ["Could not load memory index 0"]
     Just (_gty, _, addr) ->
       case Seq.lookup addr (storeMemories st) of
         Nothing -> panic "getMemVar" ["Could not resolve memory address", show addr]
         Just gv -> pure gv

genInstruction ::
  WasmGenerator s ret () ->
  ModuleInstance ->
  Store ->
  ControlStack s ->
  Wasm.Instruction Natural ->
  WasmGenerator s ret ()
genInstruction genReturn im st ctrlStack instr =
  case instr of
    Wasm.Nop ->
      return ()

    Wasm.Unreachable ->
      reportError (App (StringLit (UnicodeLiteral "unreachable")))

    Wasm.Block{ resultType = vts, body = is } ->
      do let n = length vts
         blockEnd <- setupWasmLabel vts

         -- Translate the body of the block, jumping
         -- to the block end label at the end of the body.
         -- Then, continue translating in the context of
         -- the block continuation label.
         restoreStack $ continue (fst blockEnd) $
           do mapM_ (genInstruction genReturn im st (blockEnd:ctrlStack)) is
              jumpToWasmLabel blockEnd =<< popStackN n

         -- Grab our stack values out of the block registers
         -- and continue translation
         setupLabelStack (snd blockEnd)

    Wasm.Loop{ resultType = _vts, body = is } ->
      do -- NB in WebAssembly 1.0, loop-carried dependencies cannot
         -- be on the stack, so we just need a standard label
         loopHead <- newLabel

         -- jump to the loop head, and start translating there
         continue loopHead (jump loopHead)

         -- Define the body of the loop
         mapM_ (genInstruction genReturn im st ((loopHead,mempty):ctrlStack)) is

    Wasm.If{ resultType = vts, true = true_is, false = false_is } ->
      do let n = length vts
         blockEnd <- setupWasmLabel vts
         trueLab  <- newLabel
         falseLab <- newLabel

         c <- popTest

         restoreStack $ defineBlock trueLab
           do mapM_ (genInstruction genReturn im st (blockEnd:ctrlStack)) true_is
              jumpToWasmLabel blockEnd =<< popStackN n

         restoreStack $ defineBlock falseLab
           do mapM_ (genInstruction genReturn im st (blockEnd:ctrlStack)) false_is
              jumpToWasmLabel blockEnd =<< popStackN n

         -- terminate our current block by branching, and continue
         -- translation in the continuation label
         continue (fst blockEnd) (branch c trueLab falseLab)

         -- Grab our stack values out of the block registers
         -- and continue translation
         setupLabelStack (snd blockEnd)

    Wasm.Br idx ->
      do cl <- popControlStack idx ctrlStack
         jumpToWasmLabel cl =<< popStackN (Seq.length (snd cl))

    Wasm.BrIf idx ->
      do falseLab <- newLabel
         cl <- popControlStack idx ctrlStack
         c <- popTest
         topVals <- popStackN (Seq.length (snd cl))
         assignLabelRegs cl topVals
         continue falseLab (branch c (fst cl) falseLab)
         pushStackN topVals

    Wasm.BrTable ls def ->
      do cls   <- mapM (\i -> popControlStack i ctrlStack) ls
         cldef <- popControlStack def ctrlStack
         c <- popInteger32
         topVals <- popStackN (Seq.length (snd (cldef)))
         buildBrTable c cls cldef topVals

    Wasm.Return -> genReturn

    Wasm.Call idx ->
      case resolveFuncIndex idx im of
        Nothing -> panic "genInstruction: Call" ["Could not resolve function index " ++ show idx]
        Just (fty,_,addr) ->
          case Seq.lookup addr (storeFuncs st) of
            Nothing -> panic "genInstruction: Call" ["Could not resolve function address " ++ show addr]
            Just (SomeHandle h) -> invokeFn fty (handleType h) (App (HandleLit h))

    Wasm.CallIndirect tidx ->
      case resolveTypeIndex tidx im of
        Nothing -> panic "genInstruction: CallIndirect" ["Could not resolve type index " ++ show tidx]
        Just fty ->
          -- NB, table index hard-coded to 0 in Wasm 1.0
          case resolveTableIndex 0 im of
            Nothing -> panic "genInstruction: CallIndirect" ["Could not resolve table index 0"]
            Just (_tty, tbladdr) ->
              case Seq.lookup tbladdr (storeTables st) of
                Nothing -> panic "genInstruction: CallIndirect" ["Could not resolve table address " ++ show tbladdr]
                Just ftab ->
                  do Some argTys <- pure (valueTypesToContext (Wasm.params fty))
                     Some retTys <- pure (valueTypesToContext (Wasm.results fty))
                     Some retTy  <- pure (returnContextToType retTys)
                     let tpr = FunctionHandleRepr argTys retTy
                     x  <- popInteger32
                     fn <- extensionStmt (Wasm_IndirectFunction fty ftab tpr x)
                     invokeFn fty tpr fn

    Wasm.Drop ->
      void $ popStack

    Wasm.Select ->
      do c <- popTest
         y <- popStack
         x <- popStack
         pushStack =<< iteVals c x y

    Wasm.GetLocal idx ->
      do locals <- genLocals <$> get
         case resolveSeq idx locals of
           Nothing -> panic "genInstruction: GetLocal" ["Could not find local " ++ show idx]
           Just (Some r) -> pushStackByType (typeOfReg r) =<< readReg r

    Wasm.SetLocal idx ->
      do locals <- genLocals <$> get
         case resolveSeq idx locals of
           Nothing -> panic "genInstruction: SetLocal" ["Could not find local " ++ show idx]
           Just (Some r) ->
             assignReg r =<< checkStackVal (typeOfReg r) =<< popStack

    Wasm.TeeLocal idx ->
      do locals <- genLocals <$> get
         case resolveSeq idx locals of
           Nothing -> panic "genInstruction: TeeLocal" ["Could not find local " ++ show idx]
           Just (Some r) ->
             assignReg r =<< checkStackVal (typeOfReg r) =<< peekStack

    Wasm.GetGlobal idx ->
      case resolveGlobalIndex idx im of
        Nothing -> panic "getInstruction: GetGlobal" ["Could not find global " ++ show idx]
        Just (_gty, _, addr) ->
          case Seq.lookup addr (storeGlobals st) of
            Nothing -> panic "genInstruction: GetGlobal" ["Could not resolve global address " ++ show addr]
            Just (ConstantGlobal cv) -> pushStack cv
            Just (MutableGlobal gv)  -> pushStackByType (globalType gv) =<< readGlobal gv

    Wasm.SetGlobal idx ->
      case resolveGlobalIndex idx im of
        Nothing -> panic "genInstruction: SetGlobal" ["Could not find global " ++ show idx]
        Just (_gty, _, addr) ->
          case Seq.lookup addr (storeGlobals st) of
            Nothing -> panic "genInstruction: SetGlobal" ["Could not resolve global address " ++ show addr]
            Just (ConstantGlobal _) -> panic "genInstruction: SetGlobal" ["setGlobal of constant global"]
            Just (MutableGlobal gv) -> writeGlobal gv =<< checkStackVal (globalType gv) =<< popStack

    Wasm.CurrentMemory ->
      do gv <- getMemVar im st
         pushStack =<< extensionStmt (Wasm_MemSize gv)

    Wasm.GrowMemory ->
      do gv <- getMemVar im st
         n <- popInteger32
         void $ extensionStmt (Wasm_MemGrow gv n)

    Wasm.I32Store8 ma ->
      do gv <- getMemVar im st
         v <- popInteger32
         p <- popPointer ma
         v' <- forceEvaluation (App (BVTrunc (knownNat @8) (knownNat @32) v))
         void $ extensionStmt (Wasm_StoreInt8 gv p v')

    Wasm.I32Store16 ma ->
      do gv <- getMemVar im st
         v <- popInteger32
         p <- popPointer ma
         v' <- forceEvaluation (App (BVTrunc (knownNat @16) (knownNat @32) v))
         void $ extensionStmt (Wasm_StoreInt16 gv p v')

    Wasm.I32Store ma ->
      do gv <- getMemVar im st
         v <- popInteger32
         p <- popPointer ma
         void $ extensionStmt (Wasm_StoreInt32 gv p v)

    Wasm.I64Store8 ma ->
      do gv <- getMemVar im st
         v <- popInteger64
         p <- popPointer ma
         v' <- forceEvaluation (App (BVTrunc (knownNat @8) (knownNat @64) v))
         void $ extensionStmt (Wasm_StoreInt8 gv p v')

    Wasm.I64Store16 ma ->
      do gv <- getMemVar im st
         v <- popInteger64
         p <- popPointer ma
         v' <- forceEvaluation (App (BVTrunc (knownNat @16) (knownNat @64) v))
         void $ extensionStmt (Wasm_StoreInt16 gv p v')

    Wasm.I64Store32 ma ->
      do gv <- getMemVar im st
         v <- popInteger64
         p <- popPointer ma
         v' <- forceEvaluation (App (BVTrunc (knownNat @32) (knownNat @64) v))
         void $ extensionStmt (Wasm_StoreInt32 gv p v')

    Wasm.I64Store ma ->
      do gv <- getMemVar im st
         v <- popInteger64
         p <- popPointer ma
         void $ extensionStmt (Wasm_StoreInt64 gv p v)

    Wasm.F32Store ma ->
      do gv <- getMemVar im st
         v  <- popFloat
         p  <- popPointer ma
         void $ extensionStmt (Wasm_StoreFloat gv p v)

    Wasm.F64Store ma ->
      do gv <- getMemVar im st
         v  <- popDouble
         p  <- popPointer ma
         void $ extensionStmt (Wasm_StoreDouble gv p v)

    Wasm.I32Load8S ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt8 gv p)
         pushStack (App (BVSext (knownNat @32) (knownNat @8) v))

    Wasm.I32Load8U ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt8 gv p)
         pushStack (App (BVZext (knownNat @32) (knownNat @8) v))

    Wasm.I32Load16S ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt16 gv p)
         pushStack (App (BVSext (knownNat @32) (knownNat @16) v))

    Wasm.I32Load16U ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt16 gv p)
         pushStack (App (BVZext (knownNat @32) (knownNat @16) v))

    Wasm.I32Load ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt32 gv p)
         pushStack v

    Wasm.I64Load8S ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt8 gv p)
         pushStack (App (BVSext (knownNat @64) (knownNat @8) v))

    Wasm.I64Load8U ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt8 gv p)
         pushStack (App (BVZext (knownNat @64) (knownNat @8) v))

    Wasm.I64Load16S ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt16 gv p)
         pushStack (App (BVSext (knownNat @64) (knownNat @16) v))

    Wasm.I64Load16U ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt16 gv p)
         pushStack (App (BVZext (knownNat @64) (knownNat @16) v))

    Wasm.I64Load32S ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt32 gv p)
         pushStack (App (BVSext (knownNat @64) (knownNat @32) v))

    Wasm.I64Load32U ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt32 gv p)
         pushStack (App (BVZext (knownNat @64) (knownNat @32) v))

    Wasm.I64Load ma ->
      do gv <- getMemVar im st
         p <- popPointer ma
         v <- extensionStmt (Wasm_LoadInt64 gv p)
         pushStack v

    Wasm.F32Load ma ->
      do gv <- getMemVar im st
         p  <- popPointer ma
         v  <- extensionStmt (Wasm_LoadFloat gv p)
         pushStack v

    Wasm.F64Load ma ->
      do gv <- getMemVar im st
         p  <- popPointer ma
         v  <- extensionStmt (Wasm_LoadDouble gv p)
         pushStack v

    Wasm.I32Const w -> pushStack w
    Wasm.I64Const w -> pushStack w
    Wasm.F32Const f -> pushStack f
    Wasm.F64Const d -> pushStack d

    Wasm.IUnOp  sz op -> withBitSize sz \w -> genIUnOp w op
    Wasm.IBinOp sz op -> withBitSize sz \w -> genIBinOp w op
    Wasm.IRelOp sz op -> withBitSize sz \w -> genIRelOp w op

    Wasm.I32Eqz ->
      do v <- popInteger32
         t <- mkAtom . App . Not . App . BVNonzero knownNat $ v
         pushStack t

    Wasm.I64Eqz ->
      do v <- popInteger64
         t <- mkAtom . App . Not . App . BVNonzero knownNat $ v
         pushStack t


    -- FUnOp TODO
    -- FBinOp TODO
    -- FRelOp TODO

    -- I32WrapI64
    -- ITruncFU
    -- ITruncFS
    -- I64ExtendSI32
    -- I64ExtendUI32
    -- FConvertIU {- Float Size -} BitSize {- Int Size -} BitSize
    -- FConvertIS {- Float Size -} BitSize {- Int Size -} BitSize
    -- F32DemoteF64
    -- F64PromoteF32
    -- IReinterpretF BitSize
    -- FReinterpretI BitSize

    _ -> unimplemented $ unwords ["Instruction not implemented", show instr]

invokeFn ::
  Wasm.FuncType ->
  TypeRepr (FunctionHandleType i o) ->
  Expr WasmExt s (FunctionHandleType i o) ->
  WasmGenerator s ret ()
invokeFn fty (FunctionHandleRepr argTys retTy) fn =
  do args <- computeArgs argTys (Wasm.params fty)
     ret <- call fn args
     case (Wasm.results fty) of
       []  -> return ()
       [_] -> pushStackByType retTy ret
       _   -> panic "invokeFn" [ "Multi-return functions not supported in Wasm 1.0"
                               , "This function should not have passed validation"
                               ]

buildBrTable ::
  Expr WasmExt s (BVType 32) ->
  [ControlLabel s] ->
  ControlLabel s ->
  Seq.Seq (StackVal s) ->
  WasmGenerator s ret a
buildBrTable c cls0 cldef vals = loop 0 cls0
  where
    loop _  [] = jumpToWasmLabel cldef vals
    loop !i (cl:cls) =
      do falseLab <- newLabel
         let ilit = App (BVLit knownNat (BV.word32 i))
         let test = App (BVEq knownNat c ilit)
         assignLabelRegs cl vals
         continue falseLab (branch test (fst cl) falseLab)
         loop (i+1) cls

withBitSize :: Wasm.BitSize -> (forall w. (1 <= w) => NatRepr w -> a) -> a
withBitSize Wasm.BS32 f = f (knownNat @32)
withBitSize Wasm.BS64 f = f (knownNat @64)

genIUnOp :: (1 <= w) => NatRepr w -> Wasm.IUnOp -> WasmGenerator s ret ()
genIUnOp w op =
  do v <- popInteger w
     pushInteger w case op of
       Wasm.IClz    -> App (BVCountLeadingZeros w v)
       Wasm.ICtz    -> App (BVCountTrailingZeros w v)
       Wasm.IPopcnt -> App (BVPopcount w v)

genIBinOp :: (1 <= w) => NatRepr w -> Wasm.IBinOp -> WasmGenerator s ret ()
genIBinOp w op =
  do v2 <- popInteger w
     v1 <- popInteger w
     let v2mod = App (BVUrem w v2 (App (BVLit w (BV.width w))))
     pushInteger w case op of
       Wasm.IAdd    -> App (BVAdd w v1 v2)
       Wasm.ISub    -> App (BVSub w v1 v2)
       Wasm.IMul    -> App (BVMul w v1 v2)
       Wasm.IDivU   -> App (BVUdiv w v1 v2)
       Wasm.IDivS   -> App (BVSdiv w v1 v2)
       Wasm.IRemU   -> App (BVUrem w v1 v2)
       Wasm.IRemS   -> App (BVSrem w v1 v2)
       Wasm.IAnd    -> App (BVAnd w v1 v2)
       Wasm.IOr     -> App (BVOr w v1 v2)
       Wasm.IXor    -> App (BVXor w v1 v2)
       Wasm.IRotl   -> App (BVRol w v1 v2)
       Wasm.IRotr   -> App (BVRor w v1 v2)

       -- Wasm defines shift amounts modulo w.
       -- This differs from What4's semantics for
       -- overshift, which saturate instead.
       Wasm.IShl    -> App (BVShl w v1 v2mod)
       Wasm.IShrU   -> App (BVLshr w v1 v2mod)
       Wasm.IShrS   -> App (BVAshr w v1 v2mod)

genIRelOp :: (1 <= w) => NatRepr w -> Wasm.IRelOp -> WasmGenerator s ret ()
genIRelOp w op =
  do v2 <- popInteger w
     v1 <- popInteger w
     pushStack case op of
       Wasm.IEq  -> App (BVEq w v1 v2)
       Wasm.INe  -> App (Not (App (BVEq w v1 v2)))

       Wasm.ILtU -> App (BVUlt w v1 v2)
       Wasm.ILtS -> App (BVSlt w v1 v2)
       Wasm.IGtU -> App (BVUlt w v2 v1)
       Wasm.IGtS -> App (BVSlt w v2 v1)

       Wasm.ILeU -> App (BVUle w v1 v2)
       Wasm.ILeS -> App (BVSle w v1 v2)
       Wasm.IGeU -> App (BVUle w v2 v1)
       Wasm.IGeS -> App (BVSle w v2 v1)
