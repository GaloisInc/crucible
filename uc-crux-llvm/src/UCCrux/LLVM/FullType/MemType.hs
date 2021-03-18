{-
Module           : UCCrux.LLVM.FullType.MemType
Description      : Interop between 'FullType' and 'MemType'
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module UCCrux.LLVM.FullType.MemType
  ( toMemType,
    toFullType,
    toFullTypeM,
    asFullType',
    asFullType,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Functor.Const (Const(Const))
import           Data.Functor.Identity (Identity(runIdentity))
import qualified Data.Vector as Vec
import           Control.Monad.Except (MonadError, runExceptT)
import           Control.Monad.State (MonadState, runStateT, get, modify)
import           Unsafe.Coerce (unsafeCoerce)

import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr (mkNatRepr, isPosNat, natValue, LeqProof(..))
import           Data.Parameterized.TraversableFC (toListFC)
import           Data.Parameterized.Some (Some(Some))

import qualified What4.InterpretedFloatingPoint as W4IFP

import           Lang.Crucible.LLVM.MemType (MemType(..), SymType(..), FunDecl(..))
import qualified Lang.Crucible.LLVM.MemType as MemType
import           Lang.Crucible.LLVM.TypeContext (TypeContext, asMemType, lookupAlias)

import           UCCrux.LLVM.Errors.Panic (panic)
import           UCCrux.LLVM.Errors.Unimplemented (unimplemented)
import qualified UCCrux.LLVM.Errors.Unimplemented as Unimplemented
import           UCCrux.LLVM.FullType.Type (FullTypeRepr(..), PartTypeRepr(..))
import           UCCrux.LLVM.FullType.ModuleTypes as MT
{- ORMOLU_ENABLE -}

toMemType :: FullTypeRepr m ft -> MemType
toMemType =
  \case
    FTIntRepr natRepr -> IntType (natValue natRepr)
    FTPtrRepr (PTAliasRepr (Const ident)) -> PtrType (Alias ident)
    FTPtrRepr (PTFullRepr ftRepr) -> PtrType (MemType (toMemType ftRepr))
    FTFloatRepr W4IFP.SingleFloatRepr -> FloatType
    FTFloatRepr W4IFP.DoubleFloatRepr -> DoubleType
    FTFloatRepr W4IFP.X86_80FloatRepr -> X86_FP80Type
    FTFloatRepr floatInfo -> panic "toMemType" ["Illegal float type: ", show floatInfo]
    FTVoidFuncPtrRepr argsRepr -> funType Nothing argsRepr
    FTNonVoidFuncPtrRepr retRepr argsRepr -> funType (Just retRepr) argsRepr
    FTOpaquePtrRepr _ident -> PtrType OpaqueType
    FTArrayRepr natRepr fullTypeRepr -> ArrayType (natValue natRepr) (toMemType fullTypeRepr)
    FTStructRepr structInfo _ -> StructType structInfo
  where
    funType :: Maybe (FullTypeRepr m ft) -> Ctx.Assignment (FullTypeRepr m) argTypes -> MemType
    funType maybeRetRepr argsRepr =
      PtrType
        ( FunType
            ( FunDecl
                (toMemType <$> maybeRetRepr)
                (toListFC toMemType argsRepr)
                False
            )
        )

data AsMemType
  = WasOpaque
  | WasFun
  | WasVoid
  | WasUnsupported
  | AsMemType MemType

asMemType' :: (?lc :: TypeContext) => String -> Either L.Ident MemType
asMemType' strIdent =
  case helper (Alias (L.Ident strIdent)) of
    Left _ ->
      panic
        "asMemType''"
        [ "Couldn't find declaration for type alias:",
          strIdent,
          "Possibly a bug in Clang?"
        ]
    Right WasOpaque -> Left (L.Ident strIdent)
    Right WasUnsupported -> unimplemented "toFullTypeM" Unimplemented.UnsupportedType
    Right WasVoid ->
      panic "toFullTypeM" ["Type alias was alias of void: ", strIdent]
    Right WasFun ->
      -- Is this possible in LLVM? Haven't run into it yet.
      panic "toFullTypeM" ["Type alias was alias of function type: ", strIdent]
    Right (AsMemType mt') -> Right mt'
  where
    -- c.f. 'asMemType'
    helper :: (?lc :: TypeContext, MonadError String m) => SymType -> m AsMemType
    helper (MemType mt) = return (AsMemType mt)
    helper (Alias i) = helper =<< lookupAlias i
    helper OpaqueType = return WasOpaque
    helper FunType {} = return WasFun
    helper VoidType = return WasVoid
    helper UnsupportedType {} = return WasUnsupported

toFullTypeM ::
  forall m f.
  ( MonadState (ModuleTypes m) f,
    MonadError L.Ident f
  ) =>
  MemType ->
  f (Some (FullTypeRepr m))
toFullTypeM memType =
  case memType of
    PtrType (MemType memType') ->
      do
        Some pointedTo <- toFullTypeM memType'
        pure $ Some (FTPtrRepr (PTFullRepr pointedTo))
    -- This case is crucial for safety: We have to store the resulting looked-up
    -- type in the ModuleTypes so that we can look it up in asFullType.
    PtrType (Alias ident@(L.Ident strIdent)) ->
      do
        mts <- get
        let result = Some (FTPtrRepr (PTAliasRepr (Const ident)))
        case lookupType mts ident of
          Found _ ->
            -- We've already processed this type, it's safe, move on.
            pure result
          Processing ->
            -- We're processing a recursive circle of types In this case, it's
            -- safe to *not* store the type because our caller will. In fact we
            -- must not try to calculate it for the sake of termination.
            pure result
          Missing ->
            -- We haven't yet encountered this type
            do
              modify (flip processingType ident)
              let ?lc = MT.typeContext mts
              Some ftRepr <-
                case asMemType' strIdent of
                  Left opaqueIdent -> pure $ Some (FTOpaquePtrRepr opaqueIdent)
                  Right mt -> toFullTypeM mt
              modify (\mts' -> MT.finishedType mts' ident (Some ftRepr))
              pure result
    IntType w ->
      case mkNatRepr w of
        Some w' | Just LeqProof <- isPosNat w' -> pure (Some (FTIntRepr w'))
        _ -> panic "toPartType" ["Invalid integer width " ++ show w]
    VecType n memType' ->
      do
        Some contained <- toFullTypeM memType'
        Some natRepr <- pure $ mkNatRepr n
        case isPosNat natRepr of
          Just LeqProof -> pure (Some (FTArrayRepr natRepr contained))
          Nothing -> panic "toPartType" ["Zero vector type size"]
    StructType structInfo ->
      do
        let structInfoFields = MemType.siFields structInfo
        Some fields <-
          Ctx.generateSomeM
            (length structInfoFields)
            ( \idx -> toFullTypeM (MemType.fiType (structInfoFields Vec.! idx))
            )
        pure (Some (FTStructRepr structInfo fields))
    PtrType (FunType (FunDecl retType argTypes False)) ->
      do
        Some argTypeReprs <-
          Ctx.generateSomeM
            (length argTypes)
            (\idx -> toFullTypeM (argTypes !! idx))
        case retType of
          Just retType' ->
            do
              Some retTypeRepr <- toFullTypeM retType'
              pure (Some (FTNonVoidFuncPtrRepr retTypeRepr argTypeReprs))
          Nothing -> pure (Some (FTVoidFuncPtrRepr argTypeReprs))
    FloatType -> pure (Some (FTFloatRepr W4IFP.SingleFloatRepr))
    DoubleType -> pure (Some (FTFloatRepr W4IFP.DoubleFloatRepr))
    X86_FP80Type -> pure (Some (FTFloatRepr W4IFP.X86_80FloatRepr))
    ArrayType size content ->
      do
        Some sizeRepr <- pure $ mkNatRepr size
        Some contentRepr <- toFullTypeM content
        case isPosNat sizeRepr of
          Just LeqProof -> pure (Some (FTArrayRepr sizeRepr contentRepr))
          Nothing -> panic "toPartType" ["Zero array type size"]
    PtrType FunType {} ->
      unimplemented "toFullType" Unimplemented.VarArgsFunctionType
    PtrType OpaqueType {} ->
      panic "toFullType" ["Pointer to opaque type without type alias?"]
    PtrType UnsupportedType {} -> unimplemented "toFullType" Unimplemented.UnsupportedType
    -- These ones should maybe cause a panic?
    PtrType VoidType {} -> unimplemented "toFullType" Unimplemented.VoidType
    MetadataType {} -> unimplemented "toFullType" Unimplemented.MetadataType

toFullType ::
  forall m.
  ModuleTypes m ->
  MemType ->
  (Either L.Ident (Some (FullTypeRepr m)), ModuleTypes m)
toFullType moduleTypes memType =
  runIdentity $ runStateT (runExceptT (toFullTypeM memType)) moduleTypes

-- | c.f. @asMemType@
asFullType' ::
  ModuleTypes m ->
  PartTypeRepr m ft ->
  Either L.Ident (FullTypeRepr m ft)
asFullType' mts =
  \case
    PTFullRepr fullRepr -> Right fullRepr
    PTAliasRepr (Const ident) ->
      let ?lc = MT.typeContext mts
       in case asMemType (Alias ident) of
            Left _err -> Left ident
            Right memType ->
              case toFullType mts memType of
                (Left err, _) -> Left err
                (Right (Some ft), _) ->
                  -- This is safe because of what happens in the Alias case of
                  -- toFullTypeM, namely we check that the alias was properly
                  -- translated in this module. See comment on
                  -- 'UCCrux.LLVM.FullType.CrucibleType.SomeAssign'.
                  Right (unsafeCoerce ft)

asFullType ::
  ModuleTypes m ->
  PartTypeRepr m ft ->
  FullTypeRepr m ft
asFullType mts ptRepr =
  case asFullType' mts ptRepr of
    Right ok -> ok
    Left _err ->
      -- See comment on 'UCCrux.LLVM.FullType.CrucibleType.SomeAssign'.
      panic
        "asFullType"
        [ "Found PartType not made with assignmentToFullType?",
          "Don't do that!"
        ]
