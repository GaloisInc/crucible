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
import Control.Lens((^.))
import Control.Monad.IO.Class(liftIO)

import Data.Parameterized.Classes(showF)
import Data.Parameterized.Context.Unsafe (Assignment)
import Data.Parameterized.Context(pattern Empty, pattern (:>))


import Lang.Crucible.Types
import Lang.Crucible.FunctionName(functionNameFromText)
import Lang.Crucible.CFG.Core(GlobalVar)
import Lang.Crucible.FunctionHandle (handleArgTypes,handleReturnType)
import Lang.Crucible.Simulator.RegMap(RegMap(..),regValue)
import Lang.Crucible.Simulator.ExecutionTree(FnState(..))
import Lang.Crucible.Simulator.OverrideSim
        ( mkOverride'
        , getSymInterface
        , FnBinding(..)
        , registerFnBinding
        , getOverrideArgs
        , readGlobal
        )
import Lang.Crucible.Simulator.SimError (SimErrorReason(..))


import Lang.Crucible.Solver.Symbol(userSymbol)
import Lang.Crucible.Solver.Interface
          (freshConstant, bvLit, bvEq, asUnsignedBV)
import Lang.Crucible.Solver.BoolInterface (addAssertion,addAssumption,notPred,falsePred)

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



tPtr :: HasPtrWidth w => TypeRepr (LLVMPointerType w)
tPtr = LLVMPointerRepr ?ptrWidth

setupOverrides ::
  ArchOk arch => LLVMContext arch -> Code scope arch
setupOverrides ctxt =
  do let mvar = llvmMemVar ctxt
     regOver ctxt "crucible_int8_t"
        (Empty :> tPtr) knownRepr lib_fresh_i8
     regOver ctxt "crucible_assume"
        (Empty :> knownRepr :> tPtr :> knownRepr) knownRepr lib_assume
     regOver ctxt "crucible_assert"
        (Empty :> knownRepr :> tPtr :> knownRepr) knownRepr (lib_assert mvar)
     regOver ctxt "__VERIFIER_nondet_uint"
        Empty knownRepr sv_comp_fresh_i32
     regOver ctxt "__VERIFIER_assume"
        (Empty :> knownRepr) knownRepr sv_comp_assume
     regOver ctxt "__VERIFIER_error"
        (Empty :> VectorRepr AnyRepr) knownRepr sv_comp_error

regOver ::
  LLVMContext arch ->
  String ->
  Assignment TypeRepr args ->
  TypeRepr ret ->
  Fun scope arch args ret ->
  Code scope arch
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

lib_fresh_i8 :: ArchOk arch => Fun scope arch (EmptyCtx ::> TPtr arch) (TBits 8)
lib_fresh_i8 =
  do sym <- getSymInterface
     name <- case userSymbol "X" of
               Left err -> fail (show err)
               Right a  -> return a
     liftIO (llvmPointer_bv sym =<<
                freshConstant sym name (BaseBVRepr (knownNat @8)))

lib_assume ::
  ArchOk arch => Fun scope arch
                   (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32)
                   UnitType
lib_assume =
  do RegMap (Empty :> p :> _file :> _line) <- getOverrideArgs
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 addAssumption sym =<< notPred sym =<< bvEq sym cond zero


lib_assert ::
  ArchOk arch =>
  GlobalVar Mem ->
  Fun scope arch (EmptyCtx ::> TBits 8 ::> TPtr arch ::> TBits 32) UnitType
lib_assert mvar =
  do RegMap (Empty :> p :> pFile :> line) <- getOverrideArgs
     sym  <- getSymInterface
     mem  <- readGlobal mvar
     liftIO $ do file <- BS.pack <$> loadString sym mem (regValue pFile) Nothing
                 ln   <- projectLLVM_bv sym (regValue line)
                 let lnMsg = case asUnsignedBV ln of
                               Nothing -> ""
                               Just x  -> ":" ++ show x
                     msg = BS8.unpack file ++ lnMsg ++ ": Assertion failed."
                 cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 let rsn = AssertFailureSimError msg
                 check <- notPred sym =<< bvEq sym cond zero
                 addAssertion sym check rsn


sv_comp_fresh_i32 :: ArchOk arch => Fun scope arch EmptyCtx (TBits 32)
sv_comp_fresh_i32 =
  do sym <- getSymInterface
     name <- case userSymbol "X" of
               Left err -> fail (show err)
               Right a  -> return a
     liftIO (llvmPointer_bv sym =<<
                freshConstant sym name (BaseBVRepr (knownNat @32)))

sv_comp_assume ::
  ArchOk arch => Fun scope arch
                   (EmptyCtx ::> TBits 32)
                   UnitType
sv_comp_assume =
  do RegMap (Empty :> p) <- getOverrideArgs
     sym  <- getSymInterface
     liftIO $ do cond <- projectLLVM_bv sym (regValue p)
                 zero <- bvLit sym knownRepr 0
                 addAssumption sym =<< notPred sym =<< bvEq sym cond zero

sv_comp_error ::
  ArchOk arch =>
  Fun scope arch (EmptyCtx ::> VectorType AnyType) UnitType
sv_comp_error =
  do sym  <- getSymInterface
     let rsn = AssertFailureSimError "Called __VERIFIER_error"
     liftIO $ addAssertion sym (falsePred sym) rsn
