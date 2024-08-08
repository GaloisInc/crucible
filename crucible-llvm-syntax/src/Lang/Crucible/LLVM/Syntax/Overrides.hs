{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ImplicitParams #-}

module Lang.Crucible.LLVM.Syntax.Overrides
  ( registerLLVMOverrides
  ) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable qualified as F
import Data.List qualified as List

import Text.LLVM.AST qualified as L

import Lang.Crucible.Backend qualified as C
import Lang.Crucible.Simulator qualified as C

import Lang.Crucible.LLVM.Functions qualified as CLLVM
import Lang.Crucible.LLVM.Intrinsics.Libc qualified as Libc
import Lang.Crucible.LLVM.Intrinsics.LLVM qualified as LLVM
import Lang.Crucible.LLVM.Intrinsics qualified as CLLVM
import Lang.Crucible.LLVM.MemModel qualified as CLLVM
import Lang.Crucible.LLVM.Translation qualified as CLLVM
import Lang.Crucible.LLVM.TypeContext qualified as CLLVM

-- | Register overrides for libc functions and LLVM intrinsics
registerLLVMOverrides ::
  ( C.IsSymBackend sym bak
  , CLLVM.HasLLVMAnn sym
  , CLLVM.HasPtrWidth wptr
  , ?lc :: CLLVM.TypeContext
  , ?intrinsicsOpts :: CLLVM.IntrinsicsOptions
  , ?memOpts :: CLLVM.MemOptions
  ) =>
  bak ->
  CLLVM.LLVMContext arch ->
  C.OverrideSim p sym ext rtp a r [CLLVM.SomeLLVMOverride p sym ext]
registerLLVMOverrides bak llvmCtx = do
  let ovs =  List.concat [Libc.libc_overrides, LLVM.basic_llvm_overrides]
  let decls =
        List.map (\(CLLVM.SomeLLVMOverride ov) -> CLLVM.llvmOverride_declare ov) (F.toList ovs)

  let mvar = CLLVM.llvmMemVar llvmCtx
  F.forM_ decls $ \decl -> do
    let L.Symbol name = L.decName decl
    let aliases = []
    -- See the module comment on "Lang.Crucible.LLVM.Functions" for why this
    -- part is necessary.
    C.modifyGlobal mvar $ \mem ->
      liftIO (CLLVM.registerFunPtr bak mem name (L.decName decl) aliases)

  let tmpls = map (\(CLLVM.SomeLLVMOverride ov) -> CLLVM.basic_llvm_override ov) ovs
  CLLVM.register_llvm_overrides_ llvmCtx tmpls decls
