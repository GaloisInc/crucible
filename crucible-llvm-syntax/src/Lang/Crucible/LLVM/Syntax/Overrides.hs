{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Lang.Crucible.LLVM.Syntax.Overrides
  ( registerLLVMOverrides
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable qualified as F
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text qualified as Text

import Text.LLVM.AST qualified as L

import Lang.Crucible.Backend qualified as C
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.FunctionHandle qualified as C
import Lang.Crucible.Types qualified as C

import Lang.Crucible.LLVM.Extension qualified as CLLVM
import Lang.Crucible.LLVM.Functions qualified as CLLVM
import Lang.Crucible.LLVM.Intrinsics qualified as CLLVM
import Lang.Crucible.LLVM.Intrinsics.Declare qualified as CLLVM
import Lang.Crucible.LLVM.MemModel qualified as CLLVM
import Lang.Crucible.LLVM.Translation qualified as CLLVM
import Lang.Crucible.LLVM.TypeContext qualified as CLLVM

import What4.FunctionName (FunctionName)
import What4.FunctionName qualified as WFN

-- | Register overrides for libc functions and LLVM intrinsics
registerLLVMOverrides ::
  ( C.IsSymBackend sym bak
  , CLLVM.HasLLVMAnn sym
  , CLLVM.HasPtrWidth wptr
  , ?lc :: CLLVM.TypeContext
  , ?intrinsicsOpts :: CLLVM.IntrinsicsOptions
  , ?memOpts :: CLLVM.MemOptions
  , ext ~ CLLVM.LLVM
  , CLLVM.ArchWidth arch ~ wptr
  ) =>
  bak ->
  CLLVM.LLVMContext arch ->
  Map FunctionName C.SomeHandle ->
  C.OverrideSim p sym ext rtp a r [CLLVM.SomeLLVMOverride p sym ext]
registerLLVMOverrides bak llvmCtx fwdDecs = do
  let mvar = CLLVM.llvmMemVar llvmCtx
  let decls = List.map CLLVM.fromSomeHandle (Map.elems fwdDecs)

  F.forM_ decls $ \(CLLVM.SomeDeclare decl) -> do
    let symb@(L.Symbol name) = CLLVM.decName decl
    let aliases = []
    -- See the module comment on "Lang.Crucible.LLVM.Functions" for why this
    -- part is necessary.
    C.modifyGlobal mvar $ \mem ->
      liftIO (CLLVM.registerFunPtr bak mem name symb aliases)

  ovs <- CLLVM.register_llvm_overrides_ llvmCtx CLLVM.declare_overrides decls

  -- Forward all of the `declare`d handles to the actual override
  F.forM_ ovs $ \(CLLVM.SomeLLVMOverride llOv) -> do
    let symb@(L.Symbol nm) = CLLVM.llvmOverride_name llOv
    let fnm = WFN.functionNameFromText (Text.pack nm)
    case Map.lookup fnm fwdDecs of
      Nothing -> pure ()
      Just (C.SomeHandle hdl) -> do
        let hdlArgs = C.handleArgTypes hdl
        let hdlRet = C.handleReturnType hdl
        let llArgs = CLLVM.llvmOverride_args llOv
        let llRet = CLLVM.llvmOverride_ret llOv
        case (C.testEquality llArgs hdlArgs, C.testEquality llRet hdlRet) of
          (Just C.Refl, Just C.Refl) -> do
            let typedOv = CLLVM.llvmOverrideToTypedOverride mvar llOv
            let ov = C.runTypedOverride fnm typedOv
            CLLVM.bindLLVMHandle mvar symb hdl (C.UseOverride ov)
          _ ->
            fail $ unlines $
              [ "Bad signature in `declare`"
              , " *** name: " ++ nm
              , " *** `declare` args: " ++ show hdlArgs
              , " *** override args:  " ++ show llArgs
              , " *** `declare` ret:  " ++ show hdlRet
              , " *** override ret:   " ++ show llRet
              , ""
              ]

  pure ovs
