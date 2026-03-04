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
  , llvmOvSymbol
  , llvmOvName
  , llvmOvArgs
  , llvmOvRet
  , SomeLLVMOverride(..)
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
  , polymorphic_cmp_llvm_override

  , llvmOverrideToTypedOverride
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
  { llvmOvDecl :: Decl.Declare args ret
  , llvmOvDefn ::
      IsSymInterface sym =>
      GlobalVar Mem ->
      Ctx.Assignment (RegEntry sym) args ->
      forall rtp args' ret'.
      OverrideSim p sym ext rtp args' ret' (RegValue sym ret)
    -- ^ The implementation of the intrinsic in the simulator monad
    -- (@OverrideSim@).
  }

llvmOvSymbol :: LLVMOverride p sym ext args ret -> L.Symbol
llvmOvSymbol = Decl.decName . llvmOvDecl

llvmOvName :: LLVMOverride p sym ext args ret -> FunctionName
llvmOvName ov =
  let L.Symbol nm = llvmOvSymbol ov in
  functionNameFromText (Text.pack nm)

llvmOvArgs :: LLVMOverride p sym ext args ret -> CtxRepr args
llvmOvArgs = Decl.decArgs . llvmOvDecl

llvmOvRet :: LLVMOverride p sym ext args ret -> TypeRepr ret
llvmOvRet = Decl.decRet . llvmOvDecl

data SomeLLVMOverride p sym ext =
  forall args ret. SomeLLVMOverride (LLVMOverride p sym ext args ret)

-- | Map 'llvmOverride_decl' inside a 'SomeLLVMOverride'.
someLlvmOverrideDeclare :: SomeLLVMOverride p sym ext -> Decl.SomeDeclare
someLlvmOverrideDeclare (SomeLLVMOverride ov) =
  Decl.SomeDeclare (llvmOvDecl ov)

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
  { typedOverrideArgs = llvmOvArgs ov
  , typedOverrideRet = llvmOvRet ov
  , typedOverrideHandler =
      \args -> do
        let argEntries =
              Ctx.zipWith (\t (RV v) -> RegEntry t v) (llvmOvArgs ov) args
        llvmOvDefn ov mvar argEntries
  }

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

-- | Create an 'OverrideTemplate' for an intrinsic in the @llvm.{s,u}cmp.*@
-- family. These can be instantiated at multiple types, including:
--
-- * @i2 \@llvm.scmp.i2.i32(i32, i32)@

-- * @i8 \@llvm.scmp.i8.i8(i8, i8)@
--
-- * etc.
--
-- Note that the argument and result types are allowed to be different, so the
-- @fn@ argument is parameterized by two separate 'NatRepr's.
polymorphic_cmp_llvm_override :: forall p sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall argSz resSz.
    (1 <= argSz, 2 <= resSz) =>
    NatRepr argSz ->
    NatRepr resSz ->
    SomeLLVMOverride p sym ext) ->
  OverrideTemplate p sym ext arch
polymorphic_cmp_llvm_override prefix fn =
  OverrideTemplate (Match.PrefixMatch prefix) (register_cmp_polymorphic_override prefix fn)

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

-- | Register an override for an intrinsic in the @llvm.{s,u}cmp.*@ family.
-- (See the Haddocks for 'polymorphic_cmp_llvm_override' for details on what
-- this means.) This function is responsible for parsing the suffixes in the
-- intrinsic's name, which encodes the sizes of the argument and result types.
-- As some examples:
--
-- * @.i2.i32@ (argument size @32@, result size @2@)
--
-- * @.i8.i64@ (argument size @64@, result size @8@)
register_cmp_polymorphic_override :: forall p sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall argSz resSz.
    (1 <= argSz, 2 <= resSz) =>
    NatRepr argSz ->
    NatRepr resSz ->
    SomeLLVMOverride p sym ext) ->
  MakeOverride p sym ext arch
register_cmp_polymorphic_override prefix overrideFn =
  MakeOverride $ \(Decl.SomeDeclare (Decl.Declare{ Decl.decName = L.Symbol nm })) _ _ ->
    case List.stripPrefix prefix nm of
      Just ('.':'i': (readDec -> (resSz,rest):_))
        | '.':'i': (readDec -> (argSz,[]):_) <- rest
        , Some argW <- mkNatRepr argSz
        , Some resW <- mkNatRepr resSz
        , Just LeqProof <- testLeq (knownNat @1) argW
        , Just LeqProof <- testLeq (knownNat @2) resW
        -> Just (overrideFn argW resW)
      _ -> Nothing

basic_llvm_override :: forall p args ret sym ext arch wptr.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  LLVMOverride p sym ext args ret ->
  OverrideTemplate p sym ext arch
basic_llvm_override ovr = OverrideTemplate matcher regOvr
  where
    L.Symbol ovrNm = llvmOvSymbol ovr
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
                 = let decl = (llvmOvDecl ovr) { Decl.decName = L.Symbol requestedNm } in
                   ovr { llvmOvDecl = decl }

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
  [ Decl.decName requested == llvmOvSymbol provided
  , matchingArgList args (llvmOvArgs provided)
  , Maybe.isJust (testEquality ret (llvmOvRet provided))
  ]

  where
  matchingArgList ::
    Ctx.Assignment TypeRepr ctx1 ->
    Ctx.Assignment TypeRepr ctx2 ->
    Bool
  -- Ignore varargs as long as the rest of the arguments match (VectorRepr
  -- AnyRepr is how Crucible-LLVM represents varargs).
  matchingArgList (rest Ctx.:> VectorRepr AnyRepr) ys = matchingArgList rest ys
  matchingArgList xs (rest Ctx.:> VectorRepr AnyRepr) = matchingArgList xs rest
  matchingArgList xs ys = Maybe.isJust (testEquality xs ys)

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
    do when (Decl.decName requestedDecl == llvmOvSymbol llvmOverride) $
         do logFn <- getLogFunction
            liftIO $ logFn 3 $ unlines
              [ "Mismatched declaration signatures"
              , " *** requested: " ++ show requestedDecl
              , " *** found args: " ++ show (llvmOvArgs llvmOverride)
              , " *** found ret: " ++ show (llvmOvRet llvmOverride)
              ]
  else do_register_llvm_override llvmctx llvmOverride

-- | Low-level function to register LLVM overrides.
--
-- Creates and binds a function handle, and also binds the function to the
-- global function allocation in the LLVM memory.
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
  let nm@(L.Symbol str_nm) = llvmOvSymbol llvmOverride
  let fnm  = functionNameFromText (Text.pack str_nm)

  let mvar = llvmMemVar llvmctx
  let ?lc = llvmctx^.llvmTypeCtx

  let typedOv = llvmOverrideToTypedOverride mvar llvmOverride
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
  let symb@(L.Symbol nm) = llvmOvSymbol llvmOverride
  let mvar = llvmMemVar llvmctx
  mem <- readGlobal mvar
  (_ptr, mem') <- liftIO (registerFunPtr bak mem nm symb aliases)
  writeGlobal mvar mem'
  do_register_llvm_override llvmctx llvmOverride
