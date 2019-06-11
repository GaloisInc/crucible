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
  , OverrideTemplate(..)
  , TemplateMatcher(..)
    -- ** LLVMContext
  , LLVMHandleInfo(..)
  , LLVMContext(..)
  , SymbolHandleMap
  , llvmTypeCtx
  , symbolMap
  , mkLLVMContext
    -- ** register_llvm_override
  , basic_llvm_override
  , polymorphic1_llvm_override

  , build_llvm_override
  , register_llvm_override
  , register_1arg_polymorphic_override
  ) where

import qualified Text.LLVM.AST as L

import           Control.Applicative (empty)
import           Control.Monad (when, unless)
import           Control.Monad.IO.Class (liftIO)
import           Control.Lens
import           Control.Monad.Reader (ReaderT, ask, lift)
import           Control.Monad.ST
import           Control.Monad.State (StateT, get, put)
import           Control.Monad.Trans.Maybe (MaybeT)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.List as List
import qualified Data.Text as Text
import           Numeric (readDec)

import qualified ABI.Itanium as ABI
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(..))
import           Data.Parameterized.TraversableFC (fmapFC)

import           Lang.Crucible.Backend (IsSymInterface)
import           Lang.Crucible.CFG.Common (GlobalVar)
import           Lang.Crucible.Simulator.ExecutionTree (FnState(UseOverride))
import           Lang.Crucible.FunctionHandle (FnHandle(..), mkHandle')
import           Lang.Crucible.FunctionHandle (HandleAllocator)
import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.Simulator (stateContext, simHandleAllocator)
import           Lang.Crucible.Simulator.OverrideSim
import           Lang.Crucible.Utils.MonadVerbosity (getLogFunction)
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Types

import           What4.FunctionName
import           What4.Utils.MonadST

import           Lang.Crucible.LLVM.DataLayout (ptrBitwidth, ptrSize)
import           Lang.Crucible.LLVM.Extension
import           Lang.Crucible.LLVM.MemModel
import           Lang.Crucible.LLVM.TypeContext
import           Lang.Crucible.LLVM.Translation.Types

-- | This type represents an implementation of an LLVM intrinsic function in
-- Crucible.
data LLVMOverride p sym arch args ret =
  LLVMOverride
  { llvmOverride_declare :: L.Declare    -- ^ An LLVM name and signature for this intrinsic
  , llvmOverride_args    :: CtxRepr args -- ^ A representation of the argument types
  , llvmOverride_ret     :: TypeRepr ret -- ^ A representation of the return type
  , llvmOverride_def ::
       forall rtp args' ret'.
         GlobalVar Mem ->
         sym ->
         Ctx.Assignment (RegEntry sym) args ->
         OverrideSim p sym (LLVM arch) rtp args' ret' (RegValue sym ret)
    -- ^ The implementation of the intrinsic in the simulator monad
    -- (@OverrideSim@).
  }

data SomeLLVMOverride p sym arch =
  forall args ret. SomeLLVMOverride (LLVMOverride p sym arch args ret)

-- | Convenient LLVM representation of the @size_t@ type.
llvmSizeT :: HasPtrWidth wptr => L.Type
llvmSizeT = L.PrimType $ L.Integer $ fromIntegral $ natValue $ PtrWidth

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

type RegOverrideM p sym arch rtp l a =
  ReaderT (L.Declare, Maybe ABI.DecodedName)
    (MaybeT (StateT (LLVMContext arch) (OverrideSim p sym (LLVM arch) rtp l a)))

------------------------------------------------------------------------
-- ** LLVMHandleInfo

-- | Information about an LLVM handle, including both its
--   LLVM and Crucible type information as well as the Crucible
--   handle allocated to this symbol.
data LLVMHandleInfo where
  LLVMHandleInfo :: L.Declare
                 -> FnHandle init ret
                 -> LLVMHandleInfo

------------------------------------------------------------------------
-- ** LLVMContext

-- | Maps symbol to information about associated handle.
type SymbolHandleMap = Map L.Symbol LLVMHandleInfo

-- | Information about the LLVM module.
data LLVMContext arch
   = LLVMContext
   { -- | Map LLVM symbols to their associated state.
     _symbolMap     :: !SymbolHandleMap
   , llvmArch       :: ArchRepr arch
   , llvmPtrWidth   :: forall a. (16 <= (ArchWidth arch) => NatRepr (ArchWidth arch) -> a) -> a
   , llvmMemVar     :: GlobalVar Mem
   , _llvmTypeCtx   :: TypeContext
   }

symbolMap :: Simple Lens (LLVMContext arch) SymbolHandleMap
symbolMap = lens _symbolMap (\s v -> s { _symbolMap = v })

llvmTypeCtx :: Simple Lens (LLVMContext arch) TypeContext
llvmTypeCtx = lens _llvmTypeCtx (\s v -> s{ _llvmTypeCtx = v })

mkLLVMContext :: HandleAllocator s
              -> L.Module
              -> ST s (Some LLVMContext)
mkLLVMContext halloc m = do
  let (errs, typeCtx) = typeContextFromModule m
  unless (null errs) $
    fail $ unlines
         $ [ "Failed to construct LLVM type context:" ] ++ map show errs
  let dl = llvmDataLayout typeCtx

  case mkNatRepr (ptrBitwidth dl) of
    Some (wptr :: NatRepr wptr) | Just LeqProof <- testLeq (knownNat @16) wptr ->
      withPtrWidth wptr $
        do mvar <- mkMemVar halloc
           let archRepr = X86Repr wptr -- FIXME! we should select the architecture based on
                                       -- the target triple, but llvm-pretty doesn't capture this
                                       -- currently.
           let ctx :: LLVMContext (X86 wptr)
               ctx = LLVMContext
                     { _symbolMap = Map.empty
                     , llvmArch     = archRepr
                     , llvmMemVar   = mvar
                     , llvmPtrWidth = \x -> x wptr
                     , _llvmTypeCtx = typeCtx
                     }
           return (Some ctx)
    _ ->
      fail ("Cannot load LLVM bitcode file with illegal pointer width: " ++ show (dl^.ptrSize))

------------------------------------------------------------------------
-- ** register_llvm_override

newtype ArgTransformer p sym args args' =
  ArgTransformer { applyArgTransformer :: (forall arch rtp l a.
    Ctx.Assignment (RegEntry sym) args ->
    OverrideSim p sym (LLVM arch) rtp l a (Ctx.Assignment (RegEntry sym) args')) }

newtype ValTransformer p sym tp tp' =
  ValTransformer { applyValTransformer :: (forall arch rtp l a.
    RegValue sym tp ->
    OverrideSim p sym (LLVM arch) rtp l a (RegValue sym tp')) }

transformLLVMArgs :: forall m p sym args args'.
  (IsSymInterface sym, Monad m) =>
  sym ->
  CtxRepr args' ->
  CtxRepr args ->
  m (ArgTransformer p sym args args')
transformLLVMArgs _ Ctx.Empty Ctx.Empty =
  return (ArgTransformer (\_ -> return Ctx.Empty))
transformLLVMArgs sym (rest' Ctx.:> tp') (rest Ctx.:> tp) = do
  return (ArgTransformer
           (\(xs Ctx.:> x) ->
              do (ValTransformer f)  <- transformLLVMRet sym tp tp'
                 (ArgTransformer fs) <- transformLLVMArgs sym rest' rest
                 xs' <- fs xs
                 x'  <- RegEntry tp' <$> f (regValue x)
                 pure (xs' Ctx.:> x')))
transformLLVMArgs _ _ _ =
  panic "Intrinsics.transformLLVMArgs"
    [ "transformLLVMArgs: argument shape mismatch!" ]

transformLLVMRet ::
  (IsSymInterface sym, Monad m) =>
  sym ->
  TypeRepr ret  ->
  TypeRepr ret' ->
  m (ValTransformer p sym ret ret')
transformLLVMRet sym (BVRepr w) (LLVMPointerRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . llvmPointer_bv sym))
transformLLVMRet sym (LLVMPointerRepr w) (BVRepr w')
  | Just Refl <- testEquality w w'
  = return (ValTransformer (liftIO . projectLLVM_bv sym))
transformLLVMRet sym (VectorRepr tp) (VectorRepr tp')
  = do ValTransformer f <- transformLLVMRet sym tp tp'
       return (ValTransformer (traverse f))
transformLLVMRet sym (StructRepr ctx) (StructRepr ctx')
  = do ArgTransformer tf <- transformLLVMArgs sym ctx' ctx
       return (ValTransformer (\vals ->
          let vals' = Ctx.zipWith (\tp (RV v) -> RegEntry tp v) ctx vals in
          fmapFC (\x -> RV (regValue x)) <$> tf vals'))

transformLLVMRet _sym ret ret'
  | Just Refl <- testEquality ret ret'
  = return (ValTransformer return)
transformLLVMRet _sym ret ret'
  = panic "Intrinsics.transformLLVMRet"
      [ "Cannot transform types"
      , "*** Source type: " ++ show ret
      , "*** Target type: " ++ show ret'
      ]

-- | Do some pipe-fitting to match a Crucible override function into the shape
--   expected by the LLVM calling convention.  This basically just coerces
--   between values of @BVType w@ and values of @LLVMPointerType w@.
build_llvm_override ::
  IsSymInterface sym =>
  sym ->
  FunctionName ->
  CtxRepr args ->
  TypeRepr ret ->
  CtxRepr args' ->
  TypeRepr ret' ->
  (forall rtp' l' a'. Ctx.Assignment (RegEntry sym) args ->
   OverrideSim p sym (LLVM arch) rtp' l' a' (RegValue sym ret)) ->
  OverrideSim p sym (LLVM arch) rtp l a (Override p sym (LLVM arch) args' ret')
build_llvm_override sym fnm args ret args' ret' llvmOverride =
  do fargs <- transformLLVMArgs sym args args'
     fret  <- transformLLVMRet  sym ret  ret'
     return $ mkOverride' fnm ret' $
            do RegMap xs <- getOverrideArgs
               applyValTransformer fret =<< llvmOverride =<< applyArgTransformer fargs xs

polymorphic1_llvm_override :: forall p sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym arch) ->
  OverrideTemplate p sym arch rtp l a
polymorphic1_llvm_override prefix fn =
  OverrideTemplate (PrefixMatch prefix) (register_1arg_polymorphic_override prefix fn)

register_1arg_polymorphic_override :: forall p sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  String ->
  (forall w. (1 <= w) => NatRepr w -> SomeLLVMOverride p sym arch) ->
  RegOverrideM p sym arch rtp l a ()
register_1arg_polymorphic_override prefix overrideFn =
  do L.Symbol nm <- L.decName . fst <$> ask
     case List.stripPrefix prefix nm of
       Just ('.':'i': (readDec -> (sz,[]):_))
         | Some w <- mkNatRepr sz
         , Just LeqProof <- isPosNat w
         -> case overrideFn w of SomeLLVMOverride ovr -> register_llvm_override ovr
       _ -> empty

basic_llvm_override :: forall p args ret sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMOverride p sym arch args ret ->
  OverrideTemplate p sym arch rtp l a
basic_llvm_override ovr = OverrideTemplate (ExactMatch nm) (register_llvm_override ovr)
 where L.Symbol nm = L.decName (llvmOverride_declare ovr)

register_llvm_override :: forall p args ret sym arch wptr l a rtp.
  (IsSymInterface sym, HasPtrWidth wptr, wptr ~ ArchWidth arch) =>
  LLVMOverride p sym arch args ret ->
  RegOverrideM p sym arch rtp l a ()
register_llvm_override llvmOverride = do
  requestedDecl <- fst <$> ask
  llvmctx <- get
  let decl = llvmOverride_declare llvmOverride

  if (requestedDecl /= decl) then
    do when (L.decName requestedDecl == L.decName decl) $
         do logFn <- lift $ lift $ lift $ getLogFunction
            liftIO $ logFn 3 $ unlines
              [ "Mismatched declaration signatures"
              , " *** requested: " ++ show requestedDecl
              , " *** found: "     ++ show decl
              , ""
              ]
       empty
  else
   do let nm@(L.Symbol str_nm) = L.decName decl
      let fnm  = functionNameFromText (Text.pack str_nm)

      sym <- lift $ lift $ lift $ getSymInterface

      let mvar = llvmMemVar llvmctx
      let overrideArgs = llvmOverride_args llvmOverride
      let overrideRet  = llvmOverride_ret llvmOverride

      let ?lc = llvmctx^.llvmTypeCtx

      decl' <- either fail return $ liftDeclare decl
      llvmDeclToFunHandleRepr decl' $ \derivedArgs derivedRet -> do
        o <- lift $ lift $ lift $ build_llvm_override sym fnm overrideArgs overrideRet derivedArgs derivedRet
                      (llvmOverride_def llvmOverride mvar sym)
        case Map.lookup nm (llvmctx^.symbolMap) of
          Just (LLVMHandleInfo _decl' h) -> do
            case testEquality (handleArgTypes h) derivedArgs of
               Nothing ->
                 panic "Intrinsics.register_llvm_override"
                   [ "Argument type mismatch when registering LLVM mss override."
                   , "*** Override name: " ++ show nm
                   , "*** Declared type: " ++ show (handleArgTypes h)
                   , "*** Expected type: " ++ show derivedArgs
                   ]
               Just Refl ->
                 case testEquality (handleReturnType h) derivedRet of
                   Nothing ->
                     panic "Intrinsics.register_llvm_override"
                       [ "return type mismatch when registering LLVM mss override"
                       , "*** Override name: " ++ show nm
                       ]
                   Just Refl -> lift $ lift $ lift $ bindFnHandle h (UseOverride o)
          Nothing ->
            do ctx <- lift $ lift $ lift $ use stateContext
               let ha = simHandleAllocator ctx
               h <- lift $ lift $ liftST $ mkHandle' ha fnm derivedArgs derivedRet
               lift $ lift $ lift $ bindFnHandle h (UseOverride o)
               put (llvmctx & symbolMap %~ Map.insert nm (LLVMHandleInfo decl h))
