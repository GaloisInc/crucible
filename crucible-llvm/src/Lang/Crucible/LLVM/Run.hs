{-# Language RankNTypes, ExistentialQuantification #-}
{-# Language ImplicitParams #-}
{-# Language RecordWildCards #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}

{- | Utilities for running Crucible on a bit-code file. -}
module Lang.Crucible.LLVM.Run
  ( Crux(..), Setup(..)
  , runCrux
  , Module
  , LLVM
  , IsSyntaxExtension
  ) where

import Control.Lens((^.))
import Control.Monad.ST(stToIO,RealWorld)
import System.IO(Handle)


import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(EmptyCtx)

import Lang.Crucible.Types(TypeRepr)
import Lang.Crucible.Simulator
  ( RegEntry, RegValue
  , fnBindingsFromList, runOverrideSim
  , initSimContext
  , ExecState( InitialState ), defaultAbortHandler
  , OverrideSim
  )
import Lang.Crucible.FunctionHandle(HandleAllocator,newHandleAllocator)

import Text.LLVM.AST (Module)
import Lang.Crucible.CFG.Extension(IsSyntaxExtension)

import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, llvmPtrWidth, llvmTypeCtx , LLVM)
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals)
import Lang.Crucible.LLVM.Translation
        (globalInitMap,transContext,translateModule,ModuleTranslation)
import Lang.Crucible.LLVM.Globals(populateAllGlobals,initializeMemory)

import Lang.Crucible.LLVM.MemModel(withPtrWidth)


import Lang.Crucible.Backend(IsSymInterface)



{-| Curcible initialization.  This is just a wrapper that ensure that
the initialization code does not make assumptions about the extension
being used.  -}
newtype Crux res = Crux (forall ext. Setup ext res)

-- | Generic Crucible initialization.
data Setup ext res =
  forall p t sym. IsSymInterface sym =>
  Setup
  { cruxOutput :: Handle
    -- ^ Print stuff here.

  , cruxBackend :: sym
    -- ^ Use this backend.

  , cruxInitState :: p
    -- ^ Initial value for the user state.

  , cruxInitCode ::
      OverrideSim p sym ext (RegEntry sym t) EmptyCtx t (RegValue sym t)
    -- ^ Initialization code to run at the start of simulation.

  , cruxInitCodeReturns :: TypeRepr t
    -- ^ Type of value returned by initialization code.

  , cruxGo :: IsSyntaxExtension ext =>
              ExecState p sym ext (RegEntry sym t) ->
              IO res
    -- ^ Do something with the simulator's initial state.

  }

-- | Run Crucible with the given initialization, on the given LLVM module.
runCrux :: Crux res -> Module -> IO res
runCrux (Crux setup) llvm_mod =
  do halloc     <- newHandleAllocator
     Some trans <- stToIO (translateModule halloc llvm_mod)
     withTranslated halloc llvm_mod trans setup

-- | This is split off from 'runCrux' for the type signutre, and also
-- we only use the initialization bits in here.
withTranslated ::
  HandleAllocator RealWorld ->
  Module ->
  ModuleTranslation arch ->
  Setup (LLVM arch) res ->
  IO res
withTranslated halloc llvm_mod trans Setup { .. } =
  do let llvmCtxt = trans    ^. transContext
     let ?lc      = llvmCtxt ^. llvmTypeCtx  -- used by 'populateAllGlobals'

     llvmPtrWidth llvmCtxt $ \ptrW -> withPtrWidth ptrW $

       do mem <- do mem0 <- initializeMemory cruxBackend llvmCtxt llvm_mod
                    populateAllGlobals cruxBackend (globalInitMap trans) mem0

          let globSt = llvmGlobals llvmCtxt mem
          let simctx = initSimContext
                          cruxBackend
                          llvmIntrinsicTypes
                          halloc
                          cruxOutput
                          (fnBindingsFromList [])
                          llvmExtensionImpl
                          cruxInitState

          cruxGo $ InitialState simctx globSt defaultAbortHandler
                 $ runOverrideSim cruxInitCodeReturns cruxInitCode





