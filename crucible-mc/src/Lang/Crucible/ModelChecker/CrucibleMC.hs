{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
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
import Crux.LLVM.Overrides (ArchOk)
import Crux.Model (emptyModel)
import Data.IORef (newIORef)
import qualified Data.LLVM.BitCode as BC
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import Data.String (fromString)
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.LLVM
  ( LLVM,
    llvmExtensionImpl,
    llvmGlobalsToCtx,
  )
import Lang.Crucible.LLVM.Globals (initializeAllMemory)
import Lang.Crucible.LLVM.Intrinsics (llvmIntrinsicTypes)
import qualified Lang.Crucible.LLVM.MemModel as MemModel
import qualified Lang.Crucible.LLVM.Translation as Translation
import Lang.Crucible.ModelChecker.Fresh (freshGlobals)
import Lang.Crucible.ModelChecker.GlobalInfo (getGlobalInfo)
import Lang.Crucible.ModelChecker.SymbolicExecution.Driver
  ( analyzeBlocks,
  )
import Lang.Crucible.ModelChecker.TransitionSystem.Builder
  ( makeTransitionSystem,
  )
import Lang.Crucible.ModelChecker.TransitionSystem.Namespacer
  ( sallyNamespacer,
  )
import Lang.Crucible.Simulator (fnBindingsFromList, initSimContext)
import Language.Sally (sexpOfSally, sexpToDoc)
import System.IO (stdout)
import qualified Text.LLVM as LLVM
import What4.Expr.Builder (Flags, FloatIEEE)
import What4.Protocol.Online (OnlineSolver)
import qualified What4.TransitionSystem.Exporter.Sally as Sally

-- | This exception is thrown when we fail to parse a bit-code file.
data Err
  = BitcodeError BC.Error
  | UnknownFunction String
  | UnsupportedFunType String
  deriving (Show)

instance Exception Err

findCFG :: Translation.ModuleTranslation arch -> String -> Maybe (Core.AnyCFG LLVM)
findCFG trans fun = snd <$> Map.lookup (fromString fun) (Translation.cfgMap trans)

runCrucibleMC ::
  forall arch scope solver sym.
  sym ~ Online.OnlineBackend scope solver (Flags FloatIEEE) =>
  OnlineSolver solver =>
  MemModel.HasLLVMAnn sym =>
  ArchOk arch =>
  sym ->
  LLVM.Module ->
  HandleAllocator ->
  Translation.ModuleTranslation arch ->
  String ->
  IO ()
runCrucibleMC sym llvmModule hAlloc moduleTranslation functionToSimulate =
  do
    bbMapRef <- liftIO $ newIORef Map.empty
    let ?badBehaviorMap = bbMapRef
    let llvmCtxt = L.view Translation.transContext moduleTranslation
    let extensionImpl = llvmExtensionImpl MemModel.defaultMemOptions
    -- crucially, here, we do **not** populate global variables, so as to obtain
    -- symbolic values
    mem <-
      do
        mem0 <- initializeAllMemory sym llvmCtxt llvmModule
        let ?lc = L.view Translation.llvmTypeCtx llvmCtxt
        -- populateAllGlobals sym (globalInitMap moduleTranslation) mem0
        -- return mem0
        mem1 <- freshGlobals sym (Translation.globalInitMap moduleTranslation) mem0
        -- NOTE: this is quite ugly.
        -- Supposedly, the very first block pushes a frame called "llvm_memory",
        -- and the very last block pops it before returning.
        -- Since we are executing blocks independently, the frame would be
        -- missing for all blocks, and in particular, the last block will fail
        -- when trying to pop it.
        -- This bit pushes a frame before running any block.  This is incorrect, as,
        -- in particular, the first block will now push its frame on top of the
        -- pre-existing frame, but this analysis does not care about such frames.
        return $
          mem1
            { MemModel.memImplHeap =
                MemModel.pushStackFrameMem "padding_frame" (MemModel.memImplHeap mem1)
            }
    let globSt = llvmGlobalsToCtx llvmCtxt mem
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
          let llvmCtx = L.view Translation.transContext moduleTranslation
              globInit = Translation.globalInitMap moduleTranslation
          let ?lc = L.view Translation.llvmTypeCtx llvmCtx
          -- TODO: check that @analyzeBlocks@ actually uses this, otherwise, delay it inside @makeTransitionSystem@
          Core.Some globInfos <-
            liftIO $
              Ctx.fromList
                <$> mapM (getGlobalInfo (Translation.llvmArch llvmCtx) sym mem) (Map.toList globInit)
          let ?lc = L.view Translation.llvmTypeCtx llvmCtx
          blockInfos <- analyzeBlocks llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos
          ts <- makeTransitionSystem sym cfg (sallyNamespacer sym) globInfos blockInfos
          sts <- Sally.exportTransitionSystem sym Sally.mySallyNames ts
          sexp <- sexpOfSally sym sts
          print . sexpToDoc $ sexp
          return ()
