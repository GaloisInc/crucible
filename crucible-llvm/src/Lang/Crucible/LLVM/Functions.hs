-- |
-- Module           : Lang.Crucible.LLVM.Functions
-- Description      : Register functions (CFGs and overrides)
-- Copyright        : (c) Galois, Inc 2024
-- License          : BSD3
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Stability        : provisional
--
-- Registering functions to be used with the LLVM memory model is somewhat more
-- complex than for other Crucible frontends, as LLVM has a notion of function
-- pointers. Each function to be registered has to go through a few steps (the
-- first two are common to all Crucible frontends):
--
-- * Create a 'FnHandle' and a 'FnState' (a translated CFG or an override)
-- * Bind the 'FnHandle' to the 'FnState' ('OverrideSim.bindFnHandle')
-- * Create a (global, immutable, zero-sized) allocation corresponding to the
--   function in the 'MemImpl' ('allocFunPtr')
-- * Register the correspondence between the function\'s name (and any aliases)
--   and its global allocation ('registerGlobal', or via 'registerFunPtr')
-- * Register the correspondence between the function\'s allocation and its
--   handle ('doInstallHandle', or via 'bindLLVMHandle', 'bindLLVMCFG', or
--   'bindLLVMFunc')
--
-- This module provides helpers to accomplish all of this. They\'re ordered
-- roughly low-level/customizable to high-level/automated.
--
-- Perhaps surprisingly, there\'s no function that does all of the above at
-- once. This is because there are two main places where binding functions
-- happens:
--
-- * "Lang.Crucible.LLVM" registers translated CFGs, but does so lazily. In
--   particular, this means that it initially binds the handle and allocation to
--   a \"stub\" that, when called, will translate the actual CFG and then
--   re-bind the handle and allocation to it.
-- * "Lang.Crucible.LLVM.Intrinsics.Common" registers overrides, which generally
--   apply to functions that are @declare@d but not @define@d. Thus, they
--   already have corresponding allocations, which just need to be associated
--   with the override.
--
-- Prior to these, function allocation happens in
-- 'Lang.Crucible.LLVM.Globals.initializeMemory'.
------------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}

module Lang.Crucible.LLVM.Functions
  ( allocFunPtr
  , allocLLVMFunPtr
  , allocLLVMFunPtrs
  , registerFunPtr
  , someFnHandle
  , bindLLVMHandle
  , bindLLVMCFG
  , bindLLVMFunc
  ) where

import           Control.Lens (use)
import           Control.Monad (foldM)
import           Control.Monad.IO.Class (liftIO)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           qualified Data.Text as Text

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx

import           What4.FunctionName (functionNameFromText)
import qualified What4.Interface as W4

import           Lang.Crucible.Analysis.Postdom (postdomInfo)
import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.CFG.Core (CFG)
import           Lang.Crucible.CFG.Core (TypeRepr(..), cfgHandle)
import           Lang.Crucible.FunctionHandle (FnHandle(handleArgTypes), mkHandle')
import           Lang.Crucible.Simulator.ExecutionTree (stateContext)
import           Lang.Crucible.Simulator (FnState(..), SimContext(..))
import           Lang.Crucible.Simulator.OverrideSim (OverrideSim)
import qualified Lang.Crucible.Simulator.OverrideSim as OverrideSim

import           Lang.Crucible.LLVM.DataLayout
import           Lang.Crucible.LLVM.MemModel
import qualified Lang.Crucible.LLVM.MemModel as G
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Extension (LLVM)

-- | Create a global allocation to be assocated with a function.
--
-- The returned allocation is global ('G.GlobalAlloc'), immutable
-- ('G.Immutable'), and has a size and alignment of zero.
allocFunPtr ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  -- | Function Name
  String ->
  IO (LLVMPtr sym wptr, MemImpl sym)
allocFunPtr bak mem nm = do
  let sym = backendGetSym bak
  z <- W4.bvZero sym ?ptrWidth
  doMalloc bak G.GlobalAlloc G.Immutable nm mem z noAlignment

-- | Create a global allocation assocated with a function (see 'allocFunPtr'),
-- and register the function\'s primary symbol and its aliases as associated
-- with that allocation.
registerFunPtr ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  MemImpl sym ->
  -- | Display name
  String ->
  -- | Function name
  L.Symbol ->
  -- | Aliases
  [L.Symbol] ->
  IO (LLVMPtr sym wptr, MemImpl sym)
registerFunPtr bak mem displayName nm aliases = do
  (ptr, mem') <- allocFunPtr bak mem displayName
  return $ (ptr, registerGlobal mem' (nm:aliases) ptr)

-- Not exported
funAliases ::
  LLVMContext arch ->
  L.Symbol ->
  [L.Symbol]
funAliases llvmCtx symbol =
  let aliases = llvmFunctionAliases llvmCtx
  in map L.aliasName $ maybe [] Set.toList $ Map.lookup symbol aliases

-- | Create a global allocation assocated with a function (see 'allocFunPtr'),
-- register the function\'s primary symbol and its aliases as associated with
-- that allocation (see 'registerFunPtr'), looking up the aliases from the
-- 'LLVMContext'.
allocLLVMFunPtr ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  LLVMContext arch ->
  MemImpl sym ->
  Either L.Declare L.Define ->
  IO (LLVMPtr sym wptr, MemImpl sym)
allocLLVMFunPtr bak llvm_ctx mem decl = do
  let (symbol, displayString) =
        case decl of
          Left d ->
            let s@(L.Symbol nm) = L.decName d
             in ( s, "[external function] " ++ nm )
          Right d ->
            let s@(L.Symbol nm) = L.defName d
             in ( s, "[defined function ] " ++ nm)
  let aliases = funAliases llvm_ctx symbol
  registerFunPtr bak mem displayString symbol aliases

-- | Create global allocations associated with each function in a module (see
-- 'allocLLVMFunPtr').
allocLLVMFunPtrs ::
  ( IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym
  , ?memOpts :: MemOptions ) =>
  bak ->
  LLVMContext arch ->
  MemImpl sym ->
  L.Module ->
  IO (MemImpl sym)
allocLLVMFunPtrs bak llvmCtx mem0 llvmMod = do
   -- allocate pointers values for function symbols, but do not
   -- yet bind them to function handles
   let decls = map Left (L.modDeclares llvmMod) ++ map Right (L.modDefines llvmMod)

   let allocLLVMFunPtr' bak' lctx mem decl = snd <$> allocLLVMFunPtr bak' lctx mem decl
   foldM (allocLLVMFunPtr' bak llvmCtx) mem0 decls

-- | Turn a 'FnHandle' into a 'SomeFnHandle', for use with 'doInstallHandle'.
someFnHandle :: FnHandle args ret -> SomeFnHandle
someFnHandle h =
  case handleArgTypes h of
    (_ Ctx.:> VectorRepr AnyRepr) -> VarargsFnHandle h
    _ -> SomeFnHandle h

-- | Look up an existing global function allocation by name and bind a handle
-- to it.
--
-- This can overwrite existing allocation/handle associations, and is used to do
-- so when registering lazily-translated CFGs.
bindLLVMHandle ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  GlobalVar Mem ->
  -- | Function name
  L.Symbol ->
  -- | Function handle
  FnHandle args ret ->
  -- | Function implementation (CFG or override)
  FnState p sym ext args ret ->
  OverrideSim p sym ext rtp l a ()
bindLLVMHandle mvar nm hdl impl = do
  OverrideSim.bindFnHandle hdl impl
  mem <- OverrideSim.readGlobal mvar
  mem' <- OverrideSim.ovrWithBackend $ \bak -> do
    ptr <- liftIO (doResolveGlobal bak mem nm)
    liftIO $ doInstallHandle bak ptr (someFnHandle hdl) mem
  OverrideSim.writeGlobal mvar mem'

-- | Look up an existing global function allocation by name and bind a CFG to
-- it.
--
-- This can overwrite existing allocation/handle associations, and is used to do
-- so when registering lazily-translated CFGs.
bindLLVMCFG ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  GlobalVar Mem ->
  -- | Function name
  L.Symbol ->
  -- | Function CFG
  CFG LLVM blocks init ret ->
  OverrideSim p sym LLVM rtp l a ()
bindLLVMCFG mvar name cfg = do
  let h = cfgHandle cfg
      s = UseCFG cfg (postdomInfo cfg)
  bindLLVMHandle mvar name h s

-- Private helper to make function handles
mkHandle ::
  -- | Function name
  L.Symbol ->
  -- | Argument types
  Ctx.Assignment TypeRepr args ->
  -- | Return type
  TypeRepr ret ->
  OverrideSim p sym ext rtp l a (FnHandle args ret)
mkHandle nm args ret = do
  let L.Symbol strNm = nm
  let fnm  = functionNameFromText (Text.pack strNm)
  ctx <- use stateContext
  let ha = simHandleAllocator ctx
  liftIO $ mkHandle' ha fnm args ret

-- | Create a function handle, then call 'bindLLVMHandle' on it.
bindLLVMFunc ::
  (IsSymInterface sym, HasPtrWidth wptr) =>
  GlobalVar Mem ->
  -- | Function name
  L.Symbol ->
  -- | Argument types
  Ctx.Assignment TypeRepr args ->
  -- | Return type
  TypeRepr ret ->
  -- | Function implementation (CFG or override)
  FnState p sym ext args ret ->
  OverrideSim p sym ext rtp l a ()
bindLLVMFunc mvar nm args ret impl = do
  hdl <- mkHandle nm args ret
  bindLLVMHandle mvar nm hdl impl
