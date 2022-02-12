{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module           : Lang.Crucible.ModelChecker.CrucibleMC
-- Description      : Symbolic simulation of Crucible blocks
-- Copyright        : (c) Galois, Inc 2020-2022
-- License          : BSD3
-- Maintainer       : Valentin Robert <val@galois.com>
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
import Crux.Types (Crux (CruxPersonality))
import Data.IORef (newIORef)
import qualified Data.LLVM.BitCode as BC
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import Data.String (fromString)
import Lang.Crucible.Backend (HasSymInterface (backendGetSym))
import qualified Lang.Crucible.Backend.Online as Online
import qualified Lang.Crucible.CFG.Core as Core
import Lang.Crucible.FunctionHandle (HandleAllocator)
import Lang.Crucible.LLVM
  ( LLVM,
    llvmExtensionImpl,
    llvmGlobalsToCtx,
  )
import Lang.Crucible.LLVM.Globals (initializeAllMemory)
import Lang.Crucible.LLVM.Intrinsics (defaultIntrinsicsOptions, llvmIntrinsicTypes)
import Lang.Crucible.LLVM.MemModel (defaultMemOptions)
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
import Language.Sally.SExp (sexpOfSally, sexpToDoc)
import qualified Language.Sally.TransitionSystem as Sally
import System.IO (stdout)
import qualified Text.LLVM as LLVM
import What4.Expr.Builder (ExprBuilder, Flags, FloatIEEE)
import What4.Protocol.Online (OnlineSolver)

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
  forall arch solver scope st sym bak.
  sym ~ ExprBuilder scope st (Flags FloatIEEE) =>
  bak ~ Online.OnlineBackend solver scope st (Flags FloatIEEE) =>
  OnlineSolver solver =>
  MemModel.HasLLVMAnn sym =>
  ArchOk arch =>
  bak ->
  LLVM.Module ->
  HandleAllocator ->
  Translation.ModuleTranslation arch ->
  String ->
  IO ()
runCrucibleMC bak llvmModule hAlloc moduleTranslation functionToSimulate =
  do
    let sym = backendGetSym bak
    bbMapRef <- liftIO $ newIORef Map.empty
    let ?badBehaviorMap = bbMapRef
    let llvmCtxt = L.view Translation.transContext moduleTranslation
    let extensionImpl = llvmExtensionImpl MemModel.defaultMemOptions
    -- crucially, here, we do **not** populate global variables, so as to obtain
    -- symbolic values
    mem <-
      do
        let ?memOpts = defaultMemOptions
        mem0 <- initializeAllMemory bak llvmCtxt llvmModule
        let ?lc = L.view Translation.llvmTypeCtx llvmCtxt
        -- populateAllGlobals sym (globalInitMap moduleTranslation) mem0
        -- return mem0
        mem1 <- freshGlobals bak (Translation.globalInitMap moduleTranslation) mem0
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
            bak
            llvmIntrinsicTypes
            hAlloc
            stdout
            (fnBindingsFromList [])
            extensionImpl
            CruxPersonality
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
                <$> mapM (getGlobalInfo (Translation.llvmArch llvmCtx) sym bak mem) (Map.toList globInit)
          let ?lc = L.view Translation.llvmTypeCtx llvmCtx
          let ?memOpts = defaultMemOptions
          let ?intrinsicsOpts = defaultIntrinsicsOptions
          blockInfos <- analyzeBlocks llvmModule moduleTranslation cfg llvmCtx simCtx globSt globInfos
          ts <- makeTransitionSystem sym cfg (sallyNamespacer sym) globInfos blockInfos
          sts <- Sally.exportTransitionSystem sym Sally.mySallyNames ts
          sexp <- sexpOfSally sym sts
          print . sexpToDoc $ sexp
          return ()
