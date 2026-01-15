-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Common
-- Description      : Types used in override definitions
-- Copyright        : (c) Galois, Inc 2015-2026
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
------------------------------------------------------------------------

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Lang.Crucible.LLVM.Intrinsics.Common
  ( LLVMOverride(..)
  , SomeLLVMOverride(..)
  , llvmOverrideDeclare
  , someLlvmOverrideDeclare
  , MakeOverride(..)
  , llvmSizeT
  , llvmSSizeT
  , OverrideTemplate(..)
  , callStackFromMemVar'
    -- ** register_llvm_override
  , basic_llvm_override
  , polymorphic1_llvm_override
  , polymorphic1_vec_llvm_override

  , llvmOverrideToTypedOverride
  , lower_llvm_override
  , register_llvm_override
  , register_1arg_polymorphic_override
  , register_1arg_vec_polymorphic_override
  , do_register_llvm_override
  , alloc_and_register_override
  ) where

import qualified Text.LLVM.AST as L

import           Control.Monad (when)
import           Control.Monad.IO.Class (liftIO)
import           Control.Lens
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.Text as Text
import           Numeric (readDec)
import qualified System.Info as Info

import qualified ABI.Itanium as ABI
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.ExecutionTree (FnState(UseOverride))
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Utils.MonadVerbosity (getLogFunction)
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           What4.FunctionName

import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Eval (callStackFromMemVar)
import           Lang.Crucible.LLVM.Functions (registerFunPtr, bindLLVMFunc)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack)
import qualified Lang.Crucible.LLVM.Intrinsics.Cast as Cast
import qualified Lang.Crucible.LLVM.Intrinsics.Declare as Decl
import qualified Lang.Crucible.LLVM.Intrinsics.Match as Match
import           Lang.Crucible.LLVM.Translation.Monad

-- | This type represents an implementation of an LLVM intrinsic function in
-- Crucible.
--
-- This is parameterized over @ext@ so that 'LLVMOverride's can more easily be
-- reused in the context of other language extensions that are also based on the
-- LLVM memory model, such as Macaw.
data LLVMOverride p sym ext args ret =
  LLVMOverride
  { llvmOverride_name :: L.Symbol
  , llvmOverride_args :: CtxRepr args -- ^ A representation of the argument types
  , llvmOverride_ret :: TypeRepr ret -- ^ A representation of the return type
  , llvmOverride_def ::
      IsSymInterface sym =>
      GlobalVar Mem ->
      Ctx.Assignment (RegEntry sym) args ->
      forall rtp args' ret'.
      OverrideSim p sym ext rtp args' ret' (RegValue sym ret)
    -- ^ The implementation of the intrinsic in the simulator monad
    -- (@OverrideSim@).
  }

data SomeLLVMOverride p sym ext =
  forall args ret. SomeLLVMOverride (LLVMOverride p sym ext args ret)

llvmOverrideDeclare :: LLVMOverride p sym ext args ret -> Decl.Declare args ret
llvmOverrideDeclare ov =
  Decl.Declare
  { Decl.decName = llvmOverride_name ov
  , Decl.decArgs = llvmOverride_args ov
  , Decl.decRet = llvmOverride_ret ov
  }

-- | Map 'llvmOverrideDeclare' inside a 'SomeLLVMOverride'.
someLlvmOverrideDeclare :: SomeLLVMOverride p sym ext -> Decl.SomeDeclare
someLlvmOverrideDeclare (SomeLLVMOverride ov) =
  Decl.SomeDeclare (llvmOverrideDeclare ov)

-- | Convenient LLVM representation of the @size_t@ type.
llvmSizeT :: HasPtrWidth wptr => L.Type
llvmSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

-- | Convenient LLVM representation of the @ssize_t@ type.
llvmSSizeT :: HasPtrWidth wptr => L.Type
llvmSSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

-- | A funcion that inspects an LLVM declaration (along with some other data),
-- and constructs an override for the declaration if it can.
newtype MakeOverride p sym ext arch =
  MakeOverride
    { runMakeOverride ::
        Decl.SomeDeclare ->
        -- Decoded version of the name in the declaration
        Maybe ABI.DecodedName ->
        LLVMContext arch ->
        Maybe (SomeLLVMOverride p sym ext)
    }

-- | Checking if an override applies to a given declaration happens in two
-- \"phases\", corresponding to the fields of this struct.
data OverrideTemplate p sym ext arch =
  OverrideTemplate
  { -- | An initial, quick, string-based check if an override might apply to a
    -- given declaration, based on its name
    overrideTemplateMatcher :: Match.TemplateMatcher
    -- | If the 'Match.TemplateMatcher' does indeed match, this slower
    -- 'MakeOverride' performs additional checks and potentially constructs
    -- a 'SomeLLVMOverride'.
  , overrideTemplateAction :: MakeOverride p sym ext arch
  }

callStackFromMemVar' ::
  GlobalVar Mem ->
  OverrideSim p sym ext r args ret CallStack
callStackFromMemVar' mvar = use (to (flip callStackFromMemVar mvar))

------------------------------------------------------------------------
-- ** register_llvm_override


llvmOverrideToTypedOverride ::
  IsSymInterface sym =>
  HasLLVMAnn sym =>
  GlobalVar Mem ->
  LLVMOverride p sym ext args ret ->
  TypedOverride p sym ext args ret
llvmOverrideToTypedOverride mvar ov =
  TypedOverride
  { typedOverrideArgs = llvmOverride_args ov
  , typedOverrideRet = llvmOverride_ret ov
  , typedOverrideHandler =
      \args -> do
        let argEntries =
              Ctx.zipWith
                (\t (RV v) -> RegEntry t v)
                (llvmOverride_args ov)
                args
        llvmOverride_def ov mvar argEntries
  }

lower_llvm_override ::
  forall p sym ext args ret.
  HasLLVMAnn sym =>
  GlobalVar Mem ->
  LLVMOverride p sym ext args ret ->
  TypedOverride p sym ext (Cast.CtxToLLVMType args) (Cast.ToLLVMType ret)
lower_llvm_override mvar ov =
  TypedOverride
  { typedOverrideArgs = argTys'
  , typedOverrideRet = retTy'
  , typedOverrideHandler =
    \args ->
      ovrWithBackend $ \bak -> do
        let argEntries = Ctx.zipWith (\t (RV v) -> RegEntry @sym t v) argTys' args
        args' <- liftIO (Cast.regEntriesFromLLVM fNm argTys argTys' bak argEntries)
        ret <- llvmOverride_def ov mvar args'
        liftIO (Cast.regValueToLLVM (backendGetSym bak) retTy ret)
  }
  where
    argTys = llvmOverride_args ov
    argTys' = Cast.ctxToLLVMType argTys
    retTy = llvmOverride_ret ov
    retTy' = Cast.toLLVMType retTy

    L.Symbol nm = llvmOverride_name ov
    fNm  = functionNameFromText (Text.pack nm)

polymorphic1_llvm_override :: forall p sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym ext) ->
  OverrideTemplate p sym ext arch
polymorphic1_llvm_override prefix fn =
  OverrideTemplate (Match.PrefixMatch prefix) (register_1arg_polymorphic_override prefix fn)

-- | Create an 'OverrideTemplate' for a polymorphic LLVM override involving
-- a vector type. For example, the @llvm.vector.reduce.add.*@ intrinsic can be
-- instantiated at multiple types, including:
--
-- * @i32 \@llvm.vector.reduce.add.v4i32(<4 x i32>)@
--
-- * @i64 \@llvm.vector.reduce.add.v2i64(<2 x i64>)@
--
-- * etc.
--
-- Note that the intrinsic can vary both by the size of the vector type (@4@,
-- @2@, etc.) and the size of the integer type used as the vector element type
-- (@i32@, @i64@, etc.) Therefore, the @fn@ argument that this function accepts
-- is parameterized by both the vector size (@vecSz@) and the integer size
-- (@intSz@).
polymorphic1_vec_llvm_override :: forall p sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall vecSz intSz.
    (1 <= intSz) =>
    NatRepr vecSz ->
    NatRepr intSz ->
    SomeLLVMOverride p sym ext) ->
  OverrideTemplate p sym ext arch
polymorphic1_vec_llvm_override prefix fn =
  OverrideTemplate (Match.PrefixMatch prefix) (register_1arg_vec_polymorphic_override prefix fn)

register_1arg_polymorphic_override :: forall p sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym ext) ->
  MakeOverride p sym ext arch
register_1arg_polymorphic_override prefix overrideFn =
  MakeOverride $ \(Decl.SomeDeclare (Decl.Declare{ Decl.decName = L.Symbol nm })) _ _ ->
    case List.stripPrefix prefix nm of
      Just ('.':'i': (readDec -> (sz,[]):_))
        | Some w <- mkNatRepr sz
        , Just LeqProof <- isPosNat w
        -> Just (overrideFn w)
      _ -> Nothing

-- | Register a polymorphic LLVM override involving a vector type. (See the
-- Haddocks for 'polymorphic1_vec_llvm_override' for details on what this
-- means.) This function is responsible for parsing the suffix in the
-- intrinsic's name, which encodes the sizes of the vector and integer types.
-- As some examples:
--
-- * @.v4i32@ (vector size @4@, integer size @32@)
--
-- * @.v2i64@ (vector size @2@, integer size @64@)
register_1arg_vec_polymorphic_override :: forall p sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall vecSz intSz.
    (1 <= intSz) =>
    NatRepr vecSz ->
    NatRepr intSz ->
    SomeLLVMOverride p sym ext) ->
  MakeOverride p sym ext arch
register_1arg_vec_polymorphic_override prefix overrideFn =
  MakeOverride $ \(Decl.SomeDeclare (Decl.Declare{ Decl.decName = L.Symbol nm })) _ _ ->
    case List.stripPrefix prefix nm of
      Just ('.':'v':suffix1)
        | (vecSzStr, 'i':intSzStr) <- break (== 'i') suffix1
        , (vecSzNat, []):_ <- readDec vecSzStr
        , (intSzNat, []):_ <- readDec intSzStr
        , Some vecSzRepr <- mkNatRepr vecSzNat
        , Some intSzRepr <- mkNatRepr intSzNat
        , Just LeqProof <- isPosNat intSzRepr
        -> Just (overrideFn vecSzRepr intSzRepr)
      _ -> Nothing

basic_llvm_override :: forall p args ret sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  LLVMOverride p sym ext args ret ->
  OverrideTemplate p sym ext arch
basic_llvm_override ovr = OverrideTemplate matcher regOvr
  where
    L.Symbol ovrNm = llvmOverride_name ovr
    isDarwin = Info.os == "darwin"

    matcher :: Match.TemplateMatcher
    matcher | isDarwin  = Match.DarwinAliasMatch ovrNm
            | otherwise = Match.ExactMatch ovrNm

    regOvr :: MakeOverride p sym ext arch
    regOvr = do
      MakeOverride $ \(Decl.SomeDeclare requestedDecl) _ _ -> do
        let L.Symbol requestedNm = Decl.decName requestedDecl
        -- If we are on Darwin and the function name contains Darwin-specific
        -- prefixes or suffixes, change the name of the override to the
        -- name containing prefixes/suffixes. See Note [Darwin aliases] in
        -- Lang.Crucible.LLVM.Intrinsics.Match for an explanation of why we
        -- do this.
        let ovr' | isDarwin
                 , ovrNm == Match.stripDarwinAliases requestedNm
                 = ovr { llvmOverride_name = L.Symbol requestedNm }

                 | otherwise
                 = ovr
        Just (SomeLLVMOverride ovr')

-- | Check that the requested declaration matches the provided declaration. In
-- this context, \"matching\" means that both declarations have identical names,
-- as well as equal argument and result types. When checking types for equality,
-- we consider opaque pointer types to be equal to non-opaque pointer types so
-- that we do not have to define quite so many overrides with different
-- combinations of pointer types.
isMatchingDeclaration ::
  Decl.Declare args' ret' {- ^ Requested declaration -} ->
  LLVMOverride p sym ext args ret ->
  Bool
isMatchingDeclaration requested provided =
  let args = Decl.decArgs requested in
  let ret = Decl.decRet requested in
  and
  [ Decl.decName requested == llvmOverride_name provided
  , matchingArgList args (Cast.ctxToLLVMType (llvmOverride_args provided))
  , Maybe.isJust (testEquality ret (Cast.toLLVMType (llvmOverride_ret provided)))
  ]

  where
  matchingArgList ::
    Ctx.Assignment TypeRepr ctx1 ->
    Ctx.Assignment TypeRepr ctx2 ->
    Bool
  -- Ignore varargs as long as the rest of the arguments match
  matchingArgList (rest Ctx.:> VectorRepr AnyRepr) ys = matchingArgList rest ys
  matchingArgList xs (rest Ctx.:> VectorRepr AnyRepr) = matchingArgList xs rest
  matchingArgList Ctx.Empty Ctx.Empty = True
  matchingArgList Ctx.Empty _ = False
  matchingArgList _ Ctx.Empty = False
  matchingArgList (xs Ctx.:> x) (ys Ctx.:> y) =
    Maybe.isJust (testEquality x y) && matchingArgList xs ys

register_llvm_override ::
  forall p args ret args' ret' sym ext arch wptr rtp l a.
  (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym) =>
  LLVMOverride p sym ext args ret ->
  Decl.Declare args' ret' ->
  LLVMContext arch ->
  OverrideSim p sym ext rtp l a ()
register_llvm_override llvmOverride requestedDecl llvmctx = do
  let ?lc = llvmctx^.llvmTypeCtx
  if not (isMatchingDeclaration requestedDecl llvmOverride) then
    do when (Decl.decName requestedDecl == llvmOverride_name llvmOverride) $
         do logFn <- getLogFunction
            liftIO $ logFn 3 $ unlines
              [ "Mismatched declaration signatures"
              , " *** requested: " ++ show requestedDecl
              , " *** found args: " ++ show (llvmOverride_args llvmOverride)
              , " *** found ret: " ++ show (llvmOverride_ret llvmOverride)
              ]
  else do_register_llvm_override llvmctx llvmOverride

-- | Low-level function to register LLVM overrides.
--
-- TODO Type-checks the LLVM override against the 'L.Declare' it contains, adapting
-- its arguments and return values as necessary. Then creates and binds
-- a function handle, and also binds the function to the global function
-- allocation in the LLVM memory.
--
-- Useful when you don\'t have access to a full LLVM AST, e.g., when parsing
-- Crucible CFGs written in crucible-syntax. For more usual cases, use
-- 'Lang.Crucible.LLVM.Intrinsics.register_llvm_overrides'.
do_register_llvm_override :: forall p args ret sym ext arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym) =>
  LLVMContext arch ->
  LLVMOverride p sym ext args ret ->
  OverrideSim p sym ext rtp l a ()
do_register_llvm_override llvmctx llvmOverride = do
  let nm@(L.Symbol str_nm) = llvmOverride_name llvmOverride
  let fnm  = functionNameFromText (Text.pack str_nm)

  let mvar = llvmMemVar llvmctx
  let ?lc = llvmctx^.llvmTypeCtx

  let typedOv = lower_llvm_override mvar llvmOverride
  let o = runTypedOverride fnm typedOv
  let args = typedOverrideArgs typedOv
  let ret = typedOverrideRet typedOv
  bindLLVMFunc mvar nm args ret (UseOverride o)

-- | Create an allocation for an override and register it.
--
-- Useful when registering an override for a function in an LLVM memory that
-- wasn't initialized with the functions in "Lang.Crucible.LLVM.Globals", e.g.,
-- when parsing Crucible CFGs written in crucible-syntax. For more usual cases,
-- use 'Lang.Crucible.LLVM.Intrinsics.register_llvm_overrides'.
--
-- c.f. 'Lang.Crucible.LLVM.Globals.allocLLVMFunPtr'
alloc_and_register_override ::
  (IsSymBackend sym bak, HasPtrWidth wptr, HasLLVMAnn sym, ?memOpts :: MemOptions) =>
  bak ->
  LLVMContext arch ->
  LLVMOverride p sym LLVM args ret ->
  -- | Aliases
  [L.Symbol] ->
  OverrideSim p sym LLVM rtp l a ()
alloc_and_register_override bak llvmctx llvmOverride aliases = do
  let symb@(L.Symbol nm) = llvmOverride_name llvmOverride
  let mvar = llvmMemVar llvmctx
  mem <- readGlobal mvar
  (_ptr, mem') <- liftIO (registerFunPtr bak mem nm symb aliases)
  writeGlobal mvar mem'
  do_register_llvm_override llvmctx llvmOverride
