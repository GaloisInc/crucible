-- |
-- Module           : Lang.Crucible.LLVM.Intrinsics.Common
-- Description      : Types used in override definitions
-- Copyright        : (c) Galois, Inc 2015-2019
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
  , RegOverrideM
  , llvmSizeT
  , llvmSSizeT
  , OverrideTemplate(..)
  , TemplateMatcher(..)
  , stripDarwinAliases
  , callStackFromMemVar'
    -- ** register_llvm_override
  , basic_llvm_override
  , polymorphic1_llvm_override

  , build_llvm_override
  , register_llvm_override
  , register_1arg_polymorphic_override
  ) where

import qualified Text.LLVM.AST as L

import           Control.Applicative (empty)
import           Control.Monad (when)
import           Control.Monad.IO.Class (liftIO)
import           Control.Lens
import           Control.Monad.Reader (ReaderT, ask, lift)
import           Control.Monad.Trans.Maybe (MaybeT)
import qualified Data.List as List
import qualified Data.List.Extra as List (stripInfix)
import           Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import           Numeric (readDec)
import qualified System.Info as Info

import qualified ABI.Itanium as ABI
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC (fmapFC)

import           Lang.Crucible.Backend
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.ExecutionTree (FnState(UseOverride))
import           Lang.Crucible.FunctionHandle ( mkHandle' )
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Simulator (stateContext, simHandleAllocator)
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Utils.MonadVerbosity (getLogFunction)
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           What4.FunctionName

import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.Eval (callStackFromMemVar)
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.MemModel.CallStack (CallStack)
import           Lang.Crucible.LLVM.Translation.Monad
import           Lang.Crucible.LLVM.Translation.Types

-- | This type represents an implementation of an LLVM intrinsic function in
-- Crucible.
data LLVMOverride p sym args ret =
  LLVMOverride
  { llvmOverride_declare :: L.Declare    -- ^ An LLVM name and signature for this intrinsic
  , llvmOverride_args    :: CtxRepr args -- ^ A representation of the argument types
  , llvmOverride_ret     :: TypeRepr ret -- ^ A representation of the return type
  , llvmOverride_def ::
       forall bak.
         IsSymBackend sym bak =>
         GlobalVar Mem ->
         bak ->
         Ctx.Assignment (RegEntry sym) args ->
         forall rtp args' ret'.
         OverrideSim p sym LLVM rtp args' ret' (RegValue sym ret)
    -- ^ The implementation of the intrinsic in the simulator monad
    -- (@OverrideSim@).
  }

data SomeLLVMOverride p sym =
  forall args ret. SomeLLVMOverride (LLVMOverride p sym args ret)

-- | Convenient LLVM representation of the @size_t@ type.
llvmSizeT :: HasPtrWidth wptr => L.Type
llvmSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

-- | Convenient LLVM representation of the @ssize_t@ type.
llvmSSizeT :: HasPtrWidth wptr => L.Type
llvmSSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

data OverrideTemplate p sym arch rtp l a =
  OverrideTemplate
  { overrideTemplateMatcher :: TemplateMatcher
  , overrideTemplateAction :: RegOverrideM p sym arch rtp l a ()
  }

-- | This type controls whether an override is installed for a given name found in a module.
--  See 'filterTemplates'.
data TemplateMatcher
  = ExactMatch String
  | PrefixMatch String
  | SubstringsMatch [String]
  | DarwinAliasMatch String
    -- ^ Match a name up to some number of Darwin aliases.
    -- See @Note [Darwin aliases]@.

-- | Remove all prefixes and suffixes that might occur in a Darwin alias for
-- a function name. See @Note [Darwin aliases]@.
stripDarwinAliases :: String -> String
stripDarwinAliases str =
  -- Remove the \01_ prefix, if it exists...
  let strNoPrefix = fromMaybe str (List.stripPrefix "\01_" str) in
  -- ...and remove any suffixes as well. Because there can be multiple suffixes
  -- in an alias, we use `stripInfix` in case one of the prefixes does not
  -- appear at the very end of the name.
  foldr (\suf s ->
          case List.stripInfix suf s of
            Just (before, after) -> before ++ after
            Nothing              -> s)
        strNoPrefix
        suffixes
  where
    suffixes :: [String]
    suffixes = [ "$UNIX2003"
               , "$INODE64"
               , "$1050"
               , "$NOCANCEL"
               , "$DARWIN_EXTSN"
               ]

type RegOverrideM p sym arch rtp l a =
  ReaderT (L.Declare, Maybe ABI.DecodedName, LLVMContext arch)
    (MaybeT (OverrideSim p sym LLVM rtp l a))

callStackFromMemVar' ::
  GlobalVar Mem ->
  OverrideSim p sym ext r args ret CallStack
callStackFromMemVar' mvar = use (to (flip callStackFromMemVar mvar))

{-
Note [Darwin aliases]
~~~~~~~~~~~~~~~~~~~~~
Operating systems derived from Darwin, such as macOS, define several aliases
for common libc functions for versioning purposes. These aliases are defined
using __asm, so when Clang compiles these aliases, the name that appears in the
resulting bitcode will look slightly different from what appears in the source
C file. For example, compiling the write() function with Clang on macOS will
produce LLVM bitcode with the name \01_write(), where \01 represents a leading
ASCII character with code 0x01.

Aside from the \01_ prefix, there also a number of suffixes that can be used
in alias names (see `stripDarwinAliases` for the complete list). There are
enough possible combinations that it is not wise to try and write them all out
by hand. Instead, we take the approach that when using crucible-llvm on Darwin,
we treat any C function as possibly containing Darwin aliases. That is:

* In `basic_llvm_override`, we use a special DarwinAliasMatch template matcher
  on Darwin. When matching against possible overrides, DarwinAliasMatch
  indicates that function should be match the underlying name after removing
  any possible Darwin-related prefixes or suffixes (see the
  `stripDarwinAliases` function, which implements this).
* If a function name in a program matches an override name after stripping
  Darwin aliases, then we proceed to use the override, but with the override's
  name switched out for the name of the function from the program. This way,
  we write overrides for the "normalized" name (e.g., write) but have them work
  seamlessly for aliases names (e.g., \01_write) as well.

Currently, we only apply this special treatment in `basic_llvm_override`, as
we have only observed the aliases being used on libc functions. We may need to
apply this special case to other override functions (e.g.,
`register_cpp_override`) if that proves insufficient.
-}

------------------------------------------------------------------------
-- ** register_llvm_override

newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym LLVM rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall rtp l a.
    RegValue sym tp ->
    OverrideSim p sym LLVM rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall m p sym bak args args'.
  (IsSymBackend sym bak, Monad m, HasLLVMAnn sym) =>
  bak ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym args args')
transformLLVMArgs _ Ctx.Empty Ctx.Empty =
  return (ArgTransformer (\_ -> return Ctx.Empty))
transformLLVMArgs bak (rest' Ctx.:> tp') (rest Ctx.:> tp) = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformLLVMRet bak tp tp'
                 (ArgTransformer fs) <- transformLLVMArgs bak rest' rest
                 xs' <- fs xs
                 x'  <- RegEntry tp' <$> f (regValue x)
                 pure (xs' Ctx.:> x')))
transformLLVMArgs _ _ _ =
  panic "Intrinsics.transformLLVMArgs"
    [ "transformLLVMArgs: argument shape mismatch!" ]

transformLLVMRet ::
  (IsSymBackend sym bak, Monad m, HasLLVMAnn sym) =>
  bak ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ret ret')
transformLLVMRet bak (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . llvmPointer_bv (backendGetSym bak)))
transformLLVMRet bak (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . projectLLVM_bv bak))
transformLLVMRet bak (VectorRepr tp) (VectorRepr tp')
  = do ValTransformer f <- transformLLVMRet bak tp tp'
       return (ValTransformer (traverse f))
transformLLVMRet bak (StructRepr ctx) (StructRepr ctx')
  = do ArgTransformer tf <- transformLLVMArgs bak ctx' ctx
       return (ValTransformer (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

transformLLVMRet _bak ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformLLVMRet _bak ret ret'
  = panic "Intrinsics.transformLLVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the LLVM calling convention.  This basically just coerces
--   between values of @BVType w@ and values of @LLVMPointerType w@.
build_llvm_override ::
  HasLLVMAnn sym =>
  FunctionName ->
  CtxRepr args ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall bak rtp' l' a'. IsSymBackend sym bak =>
   bak ->
   Ctx.Assignment (RegEntry sym) args ->
   OverrideSim p sym LLVM rtp' l' a' (RegValue sym ret)) ->
  OverrideSim p sym LLVM rtp l a (Override p sym LLVM args' ret')
build_llvm_override fnm args ret args' ret' llvmOverride =
  ovrWithBackend $ \bak ->
  do fargs <- transformLLVMArgs bak args args'
     fret  <- transformLLVMRet  bak ret  ret'
     return $ mkOverride' fnm ret' $
            do RegMap xs <- getOverrideArgs
               ovrWithBackend $ \bak' ->
                 applyValTransformer fret =<< llvmOverride bak' =<< applyArgTransformer fargs xs

polymorphic1_llvm_override :: forall p sym arch wptr l a rtp.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym) ->
  OverrideTemplate p sym arch rtp l a
polymorphic1_llvm_override prefix fn =
  OverrideTemplate (PrefixMatch prefix) (register_1arg_polymorphic_override prefix fn)

register_1arg_polymorphic_override :: forall p sym arch wptr l a rtp.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym) ->
  RegOverrideM p sym arch rtp l a ()
register_1arg_polymorphic_override prefix overrideFn =
  do (L.Declare{ L.decName = L.Symbol nm },_,_) <- ask
     case List.stripPrefix prefix nm of
       Just ('.':'i': (readDec -> (sz,[]):_))
         | Some w <- mkNatRepr sz
         , Just LeqProof <- isPosNat w
         -> case overrideFn w of SomeLLVMOverride ovr -> register_llvm_override ovr
       _ -> empty

basic_llvm_override :: forall p args ret sym arch wptr l a rtp.
  (IsSymInterface sym, HasLLVMAnn sym, HasPtrWidth wptr) =>
  LLVMOverride p sym args ret ->
  OverrideTemplate p sym arch rtp l a
basic_llvm_override ovr = OverrideTemplate matcher regOvr
  where
    ovrDecl = llvmOverride_declare ovr
    L.Symbol ovrNm = L.decName ovrDecl
    isDarwin = Info.os == "darwin"

    matcher :: TemplateMatcher
    matcher | isDarwin  = DarwinAliasMatch ovrNm
            | otherwise = ExactMatch ovrNm

    regOvr :: RegOverrideM p sym arch rtp l a ()
    regOvr = do
      (requestedDecl, _ ,_) <- ask
      let L.Symbol requestedNm = L.decName requestedDecl
      -- If we are on Darwin and the function name contains Darwin-specific
      -- prefixes or suffixes, change the name of the override to the name
      -- containing prefixes/suffixes. See Note [Darwin aliases] for an
      -- explanation of why we do this.
      let ovr' | isDarwin
               , ovrNm == stripDarwinAliases requestedNm
               = ovr { llvmOverride_declare =
                         ovrDecl { L.decName = L.Symbol requestedNm }}

               | otherwise
               = ovr
      register_llvm_override ovr'

isMatchingDeclaration ::
  L.Declare {- ^ Requested declaration -} ->
  L.Declare {- ^ Provided declaration for intrinsic -} ->
  Bool
isMatchingDeclaration requested provided = and
  [ L.decName requested == L.decName provided
  , matchingArgList (L.decArgs requested) (L.decArgs provided)
  , L.decRetType requested == L.decRetType provided
  -- TODO? do we need to pay attention to various attributes?
  ]

 where
 matchingArgList [] [] = True
 matchingArgList [] _  = L.decVarArgs requested
 matchingArgList _  [] = L.decVarArgs provided
 matchingArgList (x:xs) (y:ys) = x == y && matchingArgList xs ys

register_llvm_override :: forall p args ret sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, HasLLVMAnn sym) =>
  LLVMOverride p sym args ret ->
  RegOverrideM p sym arch rtp l a ()
register_llvm_override llvmOverride = do
  (requestedDecl,_,llvmctx) <- ask
  let decl = llvmOverride_declare llvmOverride

  if not (isMatchingDeclaration requestedDecl decl) then
    do when (L.decName requestedDecl == L.decName decl) $
         do logFn <- lift $ lift $ getLogFunction
            liftIO $ logFn 3 $ unlines
              [ "Mismatched declaration signatures"
              , " *** requested: " ++ show requestedDecl
              , " *** found: "     ++ show decl
              , ""
              ]
       empty
  else
   do let (L.Symbol str_nm) = L.decName decl
      let fnm  = functionNameFromText (Text.pack str_nm)

      let mvar = llvmMemVar llvmctx
      let overrideArgs = llvmOverride_args llvmOverride
      let overrideRet  = llvmOverride_ret llvmOverride

      let ?lc = llvmctx^.llvmTypeCtx

      llvmDeclToFunHandleRepr' decl $ \args ret -> do
        o <- lift $ lift $
                build_llvm_override fnm overrideArgs overrideRet args ret
                (\bak asgn -> llvmOverride_def llvmOverride mvar bak asgn)
        ctx <- lift $ lift $ use stateContext
        let ha = simHandleAllocator ctx
        h <- lift $ liftIO $ mkHandle' ha fnm args ret

        lift $ lift $ do
           bindFnHandle h (UseOverride o)
           mem <- readGlobal mvar
           mem' <- ovrWithBackend $ \bak ->
                     liftIO $ bindLLVMFunPtr bak decl h mem
           writeGlobal mvar mem'
