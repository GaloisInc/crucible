{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module MemSetup
  (
    withInitializedMemory
  )
  where

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import qualified Text.LLVM.AST as L

import qualified What4.Expr as WE

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Simple as CBS
import           Lang.Crucible.FunctionHandle ( withHandleAllocator, HandleAllocator )

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.TypeContext

import qualified Lang.Crucible.LLVM.Extension as LLVME
import qualified Lang.Crucible.LLVM.Globals as LLVMG
import qualified Lang.Crucible.LLVM.MemModel as LLVMM
import qualified Lang.Crucible.LLVM.Translation as LLVMTr


-- | Call 'initializeMemory' and get the result
withInitializedMemory :: forall a. L.Module
                      -> (forall wptr sym. ( ?lc :: TypeContext
                                           , LLVMMem.HasPtrWidth wptr
                                           , CB.IsSymInterface sym
                                           , LLVMMem.HasLLVMAnn sym
                                           , ?memOpts :: LLVMMem.MemOptions
                                           )
                          => LLVMMem.MemImpl sym
                          -> IO a)
                      -> IO a
withInitializedMemory mod' action =
  withLLVMCtx mod' $ \(ctx :: LLVMTr.LLVMContext arch) sym ->
    action @(LLVME.ArchWidth arch) =<< LLVMG.initializeAllMemory sym ctx mod'


-- | Create an LLVM context from a module and make some assertions about it.
withLLVMCtx :: forall a. L.Module
            -> (forall arch sym bak.
                   ( ?lc :: TypeContext
                   , LLVMM.HasPtrWidth (LLVME.ArchWidth arch)
                   , CB.IsSymBackend sym bak
                   , LLVMMem.HasLLVMAnn sym
                   , ?memOpts :: LLVMMem.MemOptions
                   )
                => LLVMTr.LLVMContext arch
                -> bak
                -> IO a)
            -> IO a
withLLVMCtx mod' action =
  let -- This is a separate function because we need to use the scoped type variable
      -- @s@ in the binding of @sym@, which is difficult to do inline.
      with :: forall s. NonceGenerator IO s -> HandleAllocator -> IO a
      with nonceGen halloc = do
        sym <- WE.newExprBuilder WE.FloatRealRepr WE.EmptyExprBuilderState nonceGen
        bak <- CBS.newSimpleBackend sym
        let ?memOpts = LLVMMem.defaultMemOptions
        let ?transOpts = LLVMTr.defaultTranslationOptions
        memVar <- LLVMM.mkMemVar "test_llvm_memory" halloc
        (Some (LLVMTr.ModuleTranslation _ ctx _ _), _warns) <- LLVMTr.translateModule halloc memVar mod'
        case LLVMTr.llvmArch ctx            of { LLVME.X86Repr width ->
        case assertLeq (knownNat @1)  width of { LeqProof      ->
        case assertLeq (knownNat @16) width of { LeqProof      -> do
          let ?ptrWidth = width
          let ?lc = LLVMTr._llvmTypeCtx ctx
          let ?recordLLVMAnnotation = \_ _ _ -> pure ()
          action ctx bak
        }}}
  in withIONonceGenerator $ \nonceGen ->
     withHandleAllocator  $ \halloc   -> with nonceGen halloc


assertLeq :: forall m n . NatRepr m -> NatRepr n -> LeqProof m n
assertLeq m n =
  case testLeq m n of
    Just LeqProof -> LeqProof
    Nothing       -> error $ "No LeqProof for " ++ show m ++ " and " ++ show n
