{-# Language ImplicitParams #-}
{-# Language RankNTypes #-}
{-# Language TypeFamilies #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
{-# Language DataKinds #-}
{-# Language PatternSynonyms #-}
module Overrides where

import Data.String(fromString)
import qualified Data.Map as Map
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Control.Lens((^.),(%=))
import Control.Monad.IO.Class(liftIO)

import Data.Parameterized.Classes(showF)
import Data.Parameterized.Context.Unsafe (Assignment)
import Data.Parameterized.Context(pattern Empty, pattern (:>))


import What4.FunctionName(functionNameFromText)
import What4.Symbol(userSymbol)
import What4.Interface
          (freshConstant, bvLit, bvEq, asUnsignedBV,notPred
          , getCurrentProgramLoc)

import Lang.Crucible.Types
import Lang.Crucible.CFG.Core(GlobalVar)
import Lang.Crucible.FunctionHandle (handleArgTypes,handleReturnType)
import Lang.Crucible.Simulator.RegMap(RegMap(..),regValue,RegValue,RegEntry)
import Lang.Crucible.Simulator.ExecutionTree
        ( FnState(..)
        , cruciblePersonality
        , stateContext
        )
import Lang.Crucible.Simulator.OverrideSim
        ( mkOverride'
        , getSymInterface
        , FnBinding(..)
        , registerFnBinding
        , getOverrideArgs
        , readGlobal
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
import Lang.Crucible.LLVM.Types(HasPtrWidth)

import Lang.Crucible.LLVM.MemModel
  (Mem, LLVMPointerType, pattern LLVMPointerRepr,loadString)
import Lang.Crucible.LLVM.MemModel.Pointer(llvmPointer_bv, projectLLVM_bv)

import Error
import Types
import Model



tPtr :: HasPtrWidth w => TypeRepr (LLVMPointerType w)
tPtr = LLVMPointerRepr ?ptrWidth

setupOverrides ::
  (ArchOk arch, IsSymInterface b) =>
  LLVMContext arch -> OverM b arch ()
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

     regOver ctxt "crucible_assume"
        (Empty :> knownRepr :> tPtr :> knownRepr) knownRepr lib_assume
     regOver ctxt "crucible_assert"
        (Empty :> knownRepr :> tPtr :> knownRepr) knownRepr (lib_assert mvar)

     regOver ctxt "__VERIFIER_nondet_uint"
        Empty knownRepr sv_comp_fresh_i32
     regOver ctxt "__VERIFIER_nondet_int"
        Empty knownRepr sv_comp_fresh_i32
     regOver ctxt "__VERIFIER_nondet_char"
        (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_fresh_i8
{-
     regOver ctxt "__VERIFIER_assert"
        (Empty :> knownRepr) knownRepr sv_comp_assert
-}
     regOver ctxt "__VERIFIER_assume"
        (Empty :> knownRepr) knownRepr sv_comp_assume
     regOver ctxt "__VERIFIER_error"
        (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_error

regOver ::
  (ArchOk arch, IsSymInterface b) =>
  LLVMContext arch ->
  String ->
  Assignment TypeRepr args ->
  TypeRepr ret ->
  Fun b arch args ret ->
  OverM b arch ()
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
             throwError $ Bug $ unlines
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
  OverM sym arch (RegValue sym (BaseToType ty))
mkFresh nm ty =
  do sym  <- getSymInterface
     name <- case userSymbol nm of
               Left err -> fail (show err) -- XXX
               Right a  -> return a
     elt <- liftIO (freshConstant sym name ty)
     loc   <- liftIO $ getCurrentProgramLoc sym
     stateContext.cruciblePersonality %= addVar loc nm ty elt
     return elt

lookupString ::
  (IsSymInterface sym, ArchOk arch) =>
  GlobalVar Mem -> RegEntry sym (TPtr arch) -> OverM sym arch String
lookupString mvar ptr =
  do sym <- getSymInterface
     mem <- readGlobal mvar
     bytes <- liftIO (loadString sym mem (regValue ptr) Nothing)
     return (BS8.unpack (BS.pack bytes))

lib_fresh_bits ::
  (ArchOk arch, IsSymInterface sym, 1 <= n) =>
  GlobalVar Mem -> NatRepr n -> Fun sym arch (EmptyCtx ::> TPtr arch) (TBits n)
lib_fresh_bits mvar w =
  do RegMap (Empty :> pName) <- getOverrideArgs
     name <- lookupString mvar pName
     x    <- mkFresh name (BaseBVRepr w)
     sym  <- getSymInterface
     liftIO (llvmPointer_bv sym x)


lib_fresh_i8 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym arch (EmptyCtx ::> TPtr arch) (TBits 8)
lib_fresh_i8 mem = lib_fresh_bits mem knownNat

lib_fresh_i16 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym arch (EmptyCtx ::> TPtr arch) (TBits 16)
lib_fresh_i16 mem = lib_fresh_bits mem knownNat

lib_fresh_i32 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym arch (EmptyCtx ::> TPtr arch) (TBits 32)
lib_fresh_i32 mem = lib_fresh_bits mem knownNat

lib_fresh_i64 ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem -> Fun sym arch (EmptyCtx ::> TPtr arch) (TBits 64)
lib_fresh_i64 mem = lib_fresh_bits mem knownNat


lib_assume ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym arch (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32)
               UnitType
lib_assume =
  do RegMap (Empty :> p :> _file :> _line) <- getOverrideArgs
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 asmpP <- notPred sym =<< bvEq sym cond zero
                 loc   <- getCurrentProgramLoc sym
                 let msg = AssumptionReason loc "(assumption)"
                 addAssumption sym (LabeledPred asmpP msg)


lib_assert ::
  (ArchOk arch, IsSymInterface sym) =>
  GlobalVar Mem ->
  Fun sym arch (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) UnitType
lib_assert mvar =
  do RegMap (Empty :> p :> pFile :> line) <- getOverrideArgs
     sym  <- getSymInterface
     file <- BS8.pack <$> lookupString mvar pFile
     liftIO $ do ln   <- projectLLVM_bv sym (regValue line)
                 let lnMsg = case asUnsignedBV ln of
                               Nothing -> ""
                               Just x  -> ":" ++ show x
                     msg = BS8.unpack file ++ lnMsg ++ ": Assertion failed."
                 cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 let rsn = AssertFailureSimError msg
                 check <- notPred sym =<< bvEq sym cond zero
                 assert sym check rsn



--------------------------------------------------------------------------------

sv_comp_fresh_i8 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym arch (EmptyCtx ::> VectorType AnyType)  (TBits 8)
sv_comp_fresh_i8 =
  do x <- mkFresh "X" (BaseBVRepr (knownNat @8))
     sym <- getSymInterface
     liftIO (llvmPointer_bv sym x)



sv_comp_fresh_i32 ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym arch EmptyCtx (TBits 32)
sv_comp_fresh_i32 =
  do x <- mkFresh "X" (BaseBVRepr (knownNat @32))
     sym <- getSymInterface
     liftIO (llvmPointer_bv sym x)

sv_comp_assume ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym arch (EmptyCtx ::> TBits 32) UnitType
sv_comp_assume =
  do RegMap (Empty :> p) <- getOverrideArgs
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 loc  <- getCurrentProgramLoc sym
                 let msg = AssumptionReason loc "XXX"
                 check <- notPred sym =<< bvEq sym cond zero
                 addAssumption sym (LabeledPred check msg)

{-
sv_comp_assert ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym arch (EmptyCtx ::> TBits 32) UnitType
sv_comp_assert =
  do RegMap (Empty :> p) <- getOverrideArgs
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 let msg = "Assertion failed."
                     rsn = AssertFailureSimError msg
                 check <- notPred sym =<< bvEq sym cond zero
                 addAssertion sym check rsn
-}

sv_comp_error ::
  (ArchOk arch, IsSymInterface sym) =>
  Fun sym arch (EmptyCtx ::> VectorType AnyType) UnitType
sv_comp_error =
  do sym  <- getSymInterface
     let rsn = AssertFailureSimError "Called __VERIFIER_error"
     liftIO $ addFailedAssertion sym rsn
