{-# LANGUAGE FlexibleContexts #-}
{-# Language ConstraintKinds #-}
{-# Language DataKinds #-}
{-# Language ImplicitParams #-}
{-# Language LambdaCase #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
module Crux.LLVM.Overrides where

import Data.String(fromString)
import qualified Data.Map as Map
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Control.Lens((^.),(%=))
import Control.Monad.IO.Class(liftIO)
import System.IO (hPutStrLn)

import Data.Parameterized.Classes(showF)
import Data.Parameterized.Context.Unsafe (Assignment)
import Data.Parameterized.Context(pattern Empty, pattern (:>), singleton)


import What4.FunctionName(functionNameFromText)
import What4.Symbol(userSymbol, emptySymbol)
import What4.Interface
          (freshConstant, bvLit, bvEq, bvAdd, asUnsignedBV,notPred
          , getCurrentProgramLoc, printSymExpr, arrayUpdate)
import What4.InterpretedFloatingPoint (freshFloatConstant, iFloatBaseTypeRepr)

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(GlobalVar)
import Lang.Crucible.FunctionHandle (handleArgTypes,handleReturnType)
import Lang.Crucible.Simulator.RegMap(RegMap(..),regValue,RegValue,RegEntry)
import Lang.Crucible.Simulator.ExecutionTree
        ( FnState(..)
        , cruciblePersonality
        , stateContext
        , printHandle
        )
import Lang.Crucible.Simulator.OverrideSim
        ( mkOverride'
        , getSymInterface
        , getContext
        , FnBinding(..)
        , registerFnBinding
        , getOverrideArgs
        , readGlobal
        , writeGlobal
        )
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))
import Lang.Crucible.Backend
          (IsSymInterface,addFailedAssertion,assert
          , addAssumption, LabeledPred(..), AssumptionReason(..))
import Lang.Crucible.LLVM.Translation
        ( LLVMContext, LLVMHandleInfo(..)
        , symbolMap
        , llvmMemVar
        )
import Lang.Crucible.LLVM.DataLayout
  (noAlignment)
import Lang.Crucible.LLVM.MemModel
  (Mem, LLVMPointerType, pattern LLVMPointerRepr,loadString,HasPtrWidth, doMalloc, AllocType(HeapAlloc), Mutability(Mutable),
   llvmPointer_bv, projectLLVM_bv, doArrayStore, doArrayConstStore)

import Lang.Crucible.LLVM.Extension(LLVM)
import Lang.Crucible.LLVM.Extension(ArchWidth)

import Crux.Types
import Crux.Model

-- | This happens quite a lot, so just a shorter name
type ArchOk arch    = HasPtrWidth (ArchWidth arch)
type TPtr arch      = LLVMPointerType (ArchWidth arch)
type TBits n        = LLVMPointerType n


tPtr :: HasPtrWidth w => TypeRepr (LLVMPointerType w)
tPtr = LLVMPointerRepr ?ptrWidth

tBVPtrWidth :: (HasPtrWidth w) => TypeRepr (TBits w)
tBVPtrWidth = LLVMPointerRepr ?ptrWidth

setupOverrides ::
  (ArchOk arch, IsSymInterface b) =>
  LLVMContext arch -> OverM b (LLVM arch) ()
setupOverrides ctxt =
  do let mvar = llvmMemVar ctxt
     regOver ctxt "crucible_int8_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i8 mvar)
     regOver ctxt "crucible_int16_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i16 mvar)
     regOver ctxt "crucible_int32_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i32 mvar)
     regOver ctxt "crucible_int64_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i64 mvar)

     regOver ctxt "crucible_uint8_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i8 mvar)
     regOver ctxt "crucible_uint16_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i16 mvar)
     regOver ctxt "crucible_uint32_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i32 mvar)
     regOver ctxt "crucible_uint64_t"
        (Empty :> tPtr) knownRepr (lib_fresh_i64 mvar)

     regOver ctxt "crucible_float"
        (Empty :> tPtr) knownRepr (lib_fresh_cfloat mvar)
     regOver ctxt "crucible_double"
        (Empty :> tPtr) knownRepr (lib_fresh_cdouble mvar)

     regOver ctxt "crucible_string"
        (Empty :> tPtr :> tBVPtrWidth) tPtr (lib_fresh_str mvar)

     regOver ctxt "crucible_assume"
        (Empty :> knownRepr :> tPtr :> knownRepr) knownRepr lib_assume
     regOver ctxt "crucible_assert"
        (Empty :> knownRepr :> tPtr :> knownRepr) knownRepr (lib_assert mvar)

     regOver ctxt "crucible_print_uint32"
        (Empty :> knownRepr) knownRepr lib_print32

     regOver ctxt "crucible_havoc_memory"
        (Empty :> tPtr :> tPtr) knownRepr (lib_havoc_memory mvar)

     isVarargs ctxt "__VERIFIER_nondet_ulong" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i64
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i64
     isVarargs ctxt "__VERIFIER_nondet_long" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i64
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i64
     isVarargs ctxt "__VERIFIER_nondet_uint" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i32
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i32
     isVarargs ctxt "__VERIFIER_nondet_int" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i32
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i32
     isVarargs ctxt "__VERIFIER_nondet_ushort" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i16
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i16
     isVarargs ctxt "__VERIFIER_nondet_short" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i16
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i16
     isVarargs ctxt "__VERIFIER_nondet_float" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_float
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_float
     isVarargs ctxt "__VERIFIER_nondet_double" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_double
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_double
     isVarargs ctxt "__VERIFIER_nondet_char" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i8
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i8
     isVarargs ctxt "__VERIFIER_nondet_uchar" >>= \case
        (False, s) -> regOver ctxt s Empty knownRepr sv_comp_fresh_i8
        (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i8

     regOver ctxt "__VERIFIER_assert"
        (Empty :> knownRepr) knownRepr sv_comp_assert
     regOver ctxt "__VERIFIER_assume"
        (Empty :> knownRepr) knownRepr sv_comp_assume
     isVarargs ctxt "__VERIFIER_error" >>= \case
       (False, s) -> regOver ctxt s Empty knownRepr sv_comp_error
       (True, s) -> regOver ctxt s (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_error

isVarargs ::
  (ArchOk arch, IsSymInterface b) =>
  LLVMContext arch ->
  String ->
  OverM b (LLVM arch) (Bool, String)
isVarargs ctxt nm =
  case Map.lookup (fromString nm) (ctxt ^. symbolMap) of
    Just (LLVMHandleInfo _ h) ->
      case testEquality (Empty :> VectorRepr AnyRepr) (handleArgTypes h) of
        Just Refl -> return (True, nm)
        Nothing -> return (False, nm)
    Nothing -> return (False, nm)

regOver ::
  (ArchOk arch, IsSymInterface b) =>
  LLVMContext arch ->
  String ->
  Assignment TypeRepr args ->
  TypeRepr ret ->
  Fun b (LLVM arch) args ret ->
  OverM b (LLVM arch) ()
regOver ctxt n argT retT x =
  do let lnm = fromString n
         nm  = functionNameFromText (fromString n)
     case Map.lookup lnm (ctxt ^. symbolMap) of
       Nothing -> return () -- Function not used in this proof.
                            -- (let's hope we didn't misspell its name :-)

       Just (LLVMHandleInfo _ h) ->
         case ( testEquality retT (handleReturnType h)
              , testEquality argT (handleArgTypes h) ) of
           (Just Refl, Just Refl) ->
              do let over = mkOverride' nm retT x
                 registerFnBinding (FnBinding h (UseOverride over))
           _ ->
             error $ unlines
                [ "[bug] Invalid type for implementation of " ++ show n
                , "*** Expected: " ++ showF (handleArgTypes h) ++
                            " -> " ++ showF (handleReturnType h)
                , "*** Actual:   " ++ showF argT ++
                            " -> " ++ showF retT
                ]

--------------------------------------------------------------------------------

mkFresh ::
  (IsSymInterface sym) =>
  String ->
  BaseTypeRepr ty ->
  OverM sym (LLVM arch) (RegValue sym (BaseToType ty))
mkFresh nm ty =
  do sym  <- getSymInterface
     name <- case userSymbol nm of
               Left err -> fail (show err) -- XXX
               Right a  -> return a
     elt <- liftIO (freshConstant sym name ty)
     loc   <- liftIO $ getCurrentProgramLoc sym
     stateContext.cruciblePersonality %= addVar loc nm ty elt
     return elt

mkFreshFloat
  ::(IsSymInterface sym)
  => String
  -> FloatInfoRepr fi
  -> OverM sym (LLVM arch) (RegValue sym (FloatType fi))
mkFreshFloat nm fi = do
  sym  <- getSymInterface
  name <- case userSymbol nm of
            Left err -> fail (show err) -- XXX
            Right a  -> return a
  elt  <- liftIO $ freshFloatConstant sym name fi
  loc  <- liftIO $ getCurrentProgramLoc sym
  stateContext.cruciblePersonality %=
    addVar loc nm (iFloatBaseTypeRepr sym fi) elt
  return elt

lookupString ::
  (IsSymInterface sym, ArchOk arch) =>
  GlobalVar Mem -> RegEntry sym (TPtr arch) -> OverM sym (LLVM arch) String
lookupString mvar ptr =
  do sym <- getSymInterface
     mem <- readGlobal mvar
     bytes <- liftIO (loadString sym mem (regValue ptr) Nothing)
     return (BS8.unpack (BS.pack bytes))

lib_fresh_bits ::
  (ArchOk arch, IsSymInterface sym, 1 <= n) =>
  GlobalVar Mem -> NatRepr n -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (TBits n)
lib_fresh_bits mvar w =
  do RegMap args <- getOverrideArgs
     pName <- case args of Empty :> pName -> pure pName
     name <- lookupString mvar pName
     x    <- mkFresh name (BaseBVRepr w)
     sym  <- getSymInterface
     liftIO (llvmPointer_bv sym x)


lib_fresh_i8 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (TBits 8)
lib_fresh_i8 mem = lib_fresh_bits mem knownNat

lib_fresh_i16 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (TBits 16)
lib_fresh_i16 mem = lib_fresh_bits mem knownNat

lib_fresh_i32 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (TBits 32)
lib_fresh_i32 mem = lib_fresh_bits mem knownNat

lib_fresh_i64 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (TBits 64)
lib_fresh_i64 mem = lib_fresh_bits mem knownNat

lib_fresh_float ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> FloatInfoRepr fi -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (FloatType fi)
lib_fresh_float mvar fi =
  do RegMap args <- getOverrideArgs
     pName <- case args of Empty :> pName -> pure pName
     name <- lookupString mvar pName
     mkFreshFloat name fi

lib_fresh_cfloat ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (FloatType SingleFloat)
lib_fresh_cfloat mvar = lib_fresh_float mvar SingleFloatRepr

lib_fresh_cdouble ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch) (FloatType DoubleFloat)
lib_fresh_cdouble mvar = lib_fresh_float mvar DoubleFloatRepr

lib_fresh_str ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch ::> TBits (ArchWidth arch)) (TPtr arch)
lib_fresh_str mvar = do
  RegMap args <- getOverrideArgs
  case args of
    Empty :> pName :> maxLen -> do
      name <- lookupString mvar pName
      sym <- getSymInterface

      -- Compute the allocation length, which is the requested length plus one
      -- to hold the NUL terminator
      one <- liftIO $ bvLit sym ?ptrWidth 1
      maxLenBV <- liftIO $ projectLLVM_bv sym (regValue maxLen)
      len <- liftIO $ bvAdd sym maxLenBV one
      mem0 <- readGlobal mvar

      -- Allocate memory to hold the string
      (ptr, mem1) <- liftIO $ doMalloc sym HeapAlloc Mutable name mem0 len noAlignment

      -- Allocate contents for the string - we want to make each byte symbolic,
      -- so we allocate a fresh array (which has unbounded length) with symbolic
      -- contents and write it into our allocation.  This write does not cover
      -- the NUL terminator.
      contentsName <- case userSymbol (name ++ "_contents") of
        Left err -> fail (show err)
        Right nm -> return nm
      let arrayRep = BaseArrayRepr (Empty :> BaseBVRepr ?ptrWidth) (BaseBVRepr (knownNat @8))
      initContents <- liftIO $ freshConstant sym contentsName arrayRep
      zeroByte <- liftIO $ bvLit sym (knownNat @8) 0
      -- Put the NUL terminator in place
      initContentsZ <- liftIO $ arrayUpdate sym initContents (singleton maxLenBV) zeroByte
      mem2 <- liftIO $ doArrayConstStore sym mem1 ptr noAlignment initContentsZ len

      writeGlobal mvar mem2
      return ptr

lib_assume ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32)
               UnitType
lib_assume =
  do RegMap args <- getOverrideArgs
     p <- case args of Empty :> p :> _file :> _line -> pure p
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 asmpP <- notPred sym =<< bvEq sym cond zero
                 loc   <- getCurrentProgramLoc sym
                 let msg = AssumptionReason loc "(assumption)"
                 addAssumption sym (LabeledPred asmpP msg)

lib_havoc_memory ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  Fun sym (LLVM arch) (EmptyCtx ::> TPtr arch ::> TBits (ArchWidth arch)) UnitType
lib_havoc_memory mvar =
  do RegMap args <- getOverrideArgs
     (ptr, len) <- case args of Empty :> ptr :> len -> pure (ptr, len)
     let tp = BaseArrayRepr (Empty :> BaseBVRepr ?ptrWidth) (BaseBVRepr (knownNat @8))
     sym <- getSymInterface
     mem <- readGlobal mvar
     mem' <- liftIO $ do
               len' <- projectLLVM_bv sym (regValue len)
               arr <- freshConstant sym emptySymbol tp
               doArrayStore sym mem (regValue ptr) noAlignment arr len'
     writeGlobal mvar mem'

lib_assert ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  Fun sym (LLVM arch) (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) UnitType
lib_assert mvar =
  do RegMap args <- getOverrideArgs
     (p,pFile,line) <- case args of Empty :> a :> b :> c -> pure (a,b,c)
     sym  <- getSymInterface
     file <- BS8.pack <$> lookupString mvar pFile
     liftIO $ do ln   <- projectLLVM_bv sym (regValue line)
                 let lnMsg = case asUnsignedBV ln of
                               Nothing -> ""
                               Just x  -> ":" ++ show x
                     msg = BS8.unpack file ++ lnMsg ++ ": user assertion."
                 cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 let rsn = AssertFailureSimError msg
                 check <- notPred sym =<< bvEq sym cond zero
                 assert sym check rsn

lib_print32 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) (EmptyCtx ::> TBits 32) UnitType
lib_print32 =
  getOverrideArgs >>= \case
    RegMap (Empty :> x) -> do
     sym <- getSymInterface
     h <- printHandle <$> getContext
     liftIO $
       do x' <- projectLLVM_bv sym (regValue x)
          hPutStrLn h (show (printSymExpr x'))

--------------------------------------------------------------------------------

sv_comp_fresh_i8 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) args (TBits 8)
sv_comp_fresh_i8 =
  do x <- mkFresh "X" (BaseBVRepr (knownNat @8))
     sym <- getSymInterface
     liftIO (llvmPointer_bv sym x)

sv_comp_fresh_i16 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) args (TBits 16)
sv_comp_fresh_i16 =
  do x <- mkFresh "X" (BaseBVRepr (knownNat @16))
     sym <- getSymInterface
     liftIO (llvmPointer_bv sym x)

sv_comp_fresh_i32 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) args (TBits 32)
sv_comp_fresh_i32 =
  do x <- mkFresh "X" (BaseBVRepr (knownNat @32))
     sym <- getSymInterface
     liftIO (llvmPointer_bv sym x)

sv_comp_fresh_i64 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) args (TBits 64)
sv_comp_fresh_i64 =
  do x <- mkFresh "X" (BaseBVRepr (knownNat @64))
     sym <- getSymInterface
     liftIO (llvmPointer_bv sym x)

sv_comp_fresh_float
  :: (ArchOk arch, IsSymInterface sym)
  => Fun sym (LLVM arch) args (FloatType SingleFloat)
sv_comp_fresh_float = mkFreshFloat "X" SingleFloatRepr

sv_comp_fresh_double
  :: (ArchOk arch, IsSymInterface sym)
  => Fun sym (LLVM arch) args (FloatType DoubleFloat)
sv_comp_fresh_double = mkFreshFloat "X" DoubleFloatRepr

sv_comp_assume ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) (EmptyCtx ::> TBits 32) UnitType
sv_comp_assume =
  do RegMap args <- getOverrideArgs
     p           <- case args of Empty :> p -> pure p
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 loc  <- getCurrentProgramLoc sym
                 let msg = AssumptionReason loc "XXX"
                 check <- notPred sym =<< bvEq sym cond zero
                 addAssumption sym (LabeledPred check msg)

sv_comp_assert ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) (EmptyCtx ::> TBits 32) UnitType
sv_comp_assert =
  do RegMap args <- getOverrideArgs
     p <- case args of Empty :> p -> pure p
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 let msg = "call to __VERIFIER_assert"
                     rsn = AssertFailureSimError msg
                 check <- notPred sym =<< bvEq sym cond zero
                 assert sym check rsn

sv_comp_error ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym (LLVM arch) args UnitType
sv_comp_error =
  do sym  <- getSymInterface
     let rsn = AssertFailureSimError "call to __VERIFIER_error"
     liftIO $ addFailedAssertion sym rsn
