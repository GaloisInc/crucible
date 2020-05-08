{-# Language RankNTypes, ExistentialQuantification #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
{-# Language RecordWildCards #-}
{-# Language DataKinds #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}

{- | Utilities for running Crucible on a bit-code file. -}
module Lang.Crucible.LLVM.Run
  ( CruxLLVM(..), Setup(..)
  , runCruxLLVM
  , Module
  , LLVM
  , ModuleTranslation
  , HasPtrWidth
  , ArchWidth
  , withPtrWidthOf
  , findCFG
  ) where

import Control.Lens((^.))
import System.IO(Handle)
import Data.String(fromString)
import qualified Data.Map as Map


import Data.Parameterized.Some(Some(..))
import Data.Parameterized.Context(EmptyCtx)

import Lang.Crucible.Types(TypeRepr(..))
import Lang.Crucible.CFG.Core(AnyCFG)
import Lang.Crucible.Simulator
  ( RegEntry, RegValue
  , fnBindingsFromList, runOverrideSim
  , initSimContext
  , ExecState( InitialState ), defaultAbortHandler
  , OverrideSim
  )
import Lang.Crucible.FunctionHandle(newHandleAllocator)

import Text.LLVM.AST (Module)

import Lang.Crucible.LLVM.Intrinsics
        (llvmIntrinsicTypes, LLVM)
import Lang.Crucible.LLVM(llvmExtensionImpl, llvmGlobals)
import Lang.Crucible.LLVM.Translation
        (globalInitMap,transContext,translateModule,ModuleTranslation,cfgMap,llvmPtrWidth,llvmTypeCtx)
import Lang.Crucible.LLVM.Globals(populateAllGlobals,initializeAllMemory)

import Lang.Crucible.LLVM.MemModel(withPtrWidth,HasPtrWidth,MemOptions,HasLLVMAnn)

import Lang.Crucible.LLVM.Extension(ArchWidth)

import Lang.Crucible.Backend(IsSymInterface)


-- | LLVM specific crucible initialization.
newtype CruxLLVM res =
  CruxLLVM (forall arch. ModuleTranslation arch -> IO (Setup (LLVM arch) res))


-- | Generic Crucible initialization.
data Setup ext res =
  forall p t sym. (IsSymInterface sym, HasLLVMAnn sym) =>
  Setup
  { cruxOutput :: Handle
    -- ^ Print stuff here.

  , cruxBackend :: sym
    -- ^ Use this backend.

  , cruxUserState :: p
    -- ^ Initial value for the user state.

  , cruxInitCode ::
      OverrideSim p sym ext (RegEntry sym t) EmptyCtx t (RegValue sym t)
    -- ^ Initialization code to run at the start of simulation.

  , cruxInitCodeReturns :: TypeRepr t
    -- ^ Type of value returned by initialization code.

  , cruxGo :: ExecState p sym ext (RegEntry sym t) -> IO res
    -- ^ Do something with the simulator's initial state.

  }

-- | Run Crucible with the given initialization, on the given LLVM module.
runCruxLLVM ::
  Module ->
  MemOptions ->
  Bool {- ^ Should we turn on lax arithmetic rules? -}->
  CruxLLVM res ->
  IO res
runCruxLLVM llvm_mod memOpts laxArith (CruxLLVM setup) =
  do let ?laxArith = laxArith
     halloc <- newHandleAllocator
     Some trans <- translateModule halloc llvm_mod
     res <- setup trans
     case res of
       Setup { .. } ->
         withPtrWidthOf trans (
           do let llvmCtxt = trans ^. transContext
              mem <-
                do mem0 <- initializeAllMemory cruxBackend llvmCtxt llvm_mod
                   let ?lc = llvmCtxt ^. llvmTypeCtx
                   populateAllGlobals cruxBackend (globalInitMap trans) mem0

              let globSt = llvmGlobals llvmCtxt mem
              let simctx = initSimContext
                              cruxBackend
                              llvmIntrinsicTypes
                              halloc
                              cruxOutput
                              (fnBindingsFromList [])
                              (llvmExtensionImpl memOpts)
                              cruxUserState

              cruxGo $ InitialState simctx globSt defaultAbortHandler cruxInitCodeReturns
                     $ runOverrideSim cruxInitCodeReturns cruxInitCode
           )





withPtrWidthOf :: ModuleTranslation arch ->
                  (HasPtrWidth (ArchWidth arch) => b) -> b
withPtrWidthOf trans k =
  llvmPtrWidth (trans^.transContext) (\ptrW -> withPtrWidth ptrW k)


findCFG :: ModuleTranslation arch -> String -> Maybe (AnyCFG (LLVM arch))
findCFG trans fun = snd <$> Map.lookup (fromString fun) (cfgMap trans)

