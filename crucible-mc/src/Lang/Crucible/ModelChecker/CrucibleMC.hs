{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.CrucibleMC
-- Description      : Symbolic simulation of Crucible blocks
-- Copyright        : (c) Galois, Inc 2020
-- License          : BSD3
-- Maintainer       : Valentin Robert <valentin.robert.42@gmail.com>
-- Stability        : provisional
-- |
module Lang.Crucible.ModelChecker.CrucibleMC
  ( runCrucibleMC,
  )
where

import Control.Exception (Exception (..), throwIO)
import qualified Control.Lens as L
import Control.Monad.IO.Class (liftIO)
import Crux.Model (emptyModel)
import Data.IORef (newIORef)
import qualified Data.LLVM.BitCode as BC
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.LLVM
import Lang.Crucible.LLVM.Extension (ArchWidth)
import Lang.Crucible.LLVM.Globals (initializeAllMemory)
import Lang.Crucible.LLVM.Intrinsics (llvmIntrinsicTypes)
import Lang.Crucible.LLVM.MemModel hiding (nextBlock)
import Lang.Crucible.LLVM.Run (Module, findCFG)
import Lang.Crucible.LLVM.Translation
import Lang.Crucible.ModelChecker.Fresh (freshGlobals)
import Lang.Crucible.ModelChecker.GlobalInfo
import Lang.Crucible.ModelChecker.SymbolicExecution.Driver
import Lang.Crucible.ModelChecker.TransitionSystem.Builder
import Lang.Crucible.ModelChecker.TransitionSystem.Namespacer
import Lang.Crucible.Simulator (fnBindingsFromList, initSimContext)
import Language.Sally
import System.IO (stdout)
import What4.Expr.Builder (Flags, FloatIEEE)
import What4.Protocol.Online (OnlineSolver)
import qualified What4.TransitionSystem as TS

-- | This exception is thrown when we fail to parse a bit-code file.
data Err
  = BitcodeError BC.Error
  | UnknownFunction String
  | UnsupportedFunType String
  deriving (Show)

instance Exception Err

runCrucibleMC ::
  forall arch scope solver.
  OnlineSolver scope solver =>
  HasPtrWidth (ArchWidth arch) =>
  Online.OnlineBackend scope solver (Flags FloatIEEE) ->
  Module ->
  HandleAllocator ->
  ModuleTranslation arch ->
  String ->
  IO ()
runCrucibleMC sym llvmModule hAlloc moduleTranslation functionToSimulate =
  do
    bbMapRef <- liftIO $ newIORef Map.empty
    let ?badBehaviorMap = bbMapRef
    let llvmCtxt = L.view transContext moduleTranslation
    let extensionImpl = llvmExtensionImpl @arch defaultMemOptions
    -- crucially, here, we do **not** populate global variables, so as to obtain
    -- symbolic values
    mem <-
      do
        mem0 <- initializeAllMemory sym llvmCtxt llvmModule
        let ?lc = L.view llvmTypeCtx llvmCtxt
        -- populateAllGlobals sym (globalInitMap moduleTranslation) mem0
        -- return mem0
        mem1 <- freshGlobals sym (globalInitMap moduleTranslation) mem0
        -- NOTE: this is quite ugly.
        -- Supposedly, the very first block pushes a frame called "llvm_memory",
        -- and the very last block pops it before returning.
        -- Since we are executing blocks independently, the frame would be
        -- missing for all blocks, and in particular, the last block will fail
        -- when trying to pop it.
        -- This bit pushes a frame before running any block.  This is incorrect, as,
        -- in particular, the first block will now push its frame on top of the
        -- pre-existing frame, but this analysis does not care about such frames.
        return $ mem1 {memImplHeap = pushStackFrameMem (memImplHeap mem1)}
    let globSt = llvmGlobals llvmCtxt mem
    let simCtx =
          initSimContext
            sym
            llvmIntrinsicTypes
            hAlloc
            stdout
            (fnBindingsFromList [])
            extensionImpl
            emptyModel
    case findCFG moduleTranslation functionToSimulate of
      Nothing -> throwIO (UnknownFunction functionToSimulate)
      Just (Core.AnyCFG cfg) ->
        do
          let llvmCtx = L.view transContext moduleTranslation
              globInit = globalInitMap moduleTranslation
          let ?lc = L.view llvmTypeCtx llvmCtx
          -- TODO: check that @analyzeBlocks@ actually uses this, otherwise, delay it inside @makeTransitionSystem@
          Core.Some globInfos <-
            liftIO $
              Ctx.fromList
                <$> mapM (getGlobalInfo (llvmArch llvmCtx) sym mem) (Map.toList globInit)
          let ?lc = L.view llvmTypeCtx llvmCtx
          blockInfos <- analyzeBlocks llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos
          ts <- makeTransitionSystem sym cfg (sallyNamespacer sym) globInfos blockInfos
          sts <- TS.transitionSystemToSally sym TS.mySallyNames ts
          sexp <- sexpOfSally sym sts
          print . sexpToDoc $ sexp
          return ()
