------------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.TypeContext
-- Description      : Provides simulator type information and conversions.
-- Copyright        : (c) Galois, Inc 2011-2018
-- License          : BSD3
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides functionality for querying simulator type
-- information in a module, and converting llvm-pretty types into
-- simulator types.
------------------------------------------------------------------------
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Lang.Crucible.LLVM.TypeContext
  ( -- * LLVMContext
    TypeContext
  , mkTypeContext
  , typeContextFromModule
  , llvmDataLayout
  , llvmMetadataMap
  , AliasMap
  , llvmAliasMap
    -- * LLVMContext query functions.
  , compatMemTypes
  , compatRetTypes
  , compatMemTypeLists
  , lookupAlias
  , lookupMetadata
  , liftType
  , liftMemType
  , liftRetType
  , liftDeclare
  , asMemType
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Except (MonadError(..))
import           Control.Monad.State (State, runState, modify, gets)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Text.LLVM as L
import qualified Text.LLVM.DebugUtils as L
import qualified Text.LLVM.PP as L
import           Prettyprinter
import           Data.IntMap (IntMap)

import           Lang.Crucible.LLVM.MemType
import           Lang.Crucible.LLVM.DataLayout

data IdentStatus
  = Resolved SymType
  | Active
  | Pending L.Type

data TCState = TCS { tcsDataLayout :: DataLayout
                   , tcsMap :: Map Ident IdentStatus
                     -- | Set of types encountered that are not supported by
                     -- the
                   , tcsUnsupported :: Set L.Type
                   , tcsUnresolvable :: Set Ident
                   }

runTC :: DataLayout
      -> Map Ident IdentStatus
      -> TC a
      -> ([Doc ann], a)
runTC pdl initMap m = over _1 tcsErrors . view swapped $ runState m tcs0
  where tcs0 = TCS { tcsDataLayout = pdl
                   , tcsMap =  initMap
                   , tcsUnsupported = Set.empty
                   , tcsUnresolvable = Set.empty
                   }

tcsErrors :: TCState -> [Doc ann]
tcsErrors tcs = (ppUnsupported <$> Set.toList (tcsUnsupported tcs))
             ++ (ppUnresolvable <$> Set.toList (tcsUnresolvable tcs))
  where ppUnsupported tp = pretty "Unsupported type:" <+> pretty (show (L.ppType tp))
        ppUnresolvable i = pretty "Could not resolve identifier:" <+> pretty (show (L.ppIdent i))
        -- TODO: update if llvm-pretty switches to prettyprinter

-- | Type lifter contains types that could not be parsed.
type TC = State TCState

recordUnsupported :: L.Type -> TC ()
recordUnsupported tp = modify fn
  where fn tcs = tcs { tcsUnsupported = Set.insert tp (tcsUnsupported tcs) }

-- | Returns the type bound to an identifier.
tcIdent :: Ident -> TC SymType
tcIdent i = do
  im <- gets tcsMap
  let retUnsupported = tp <$ modify fn
        where tp = UnsupportedType (L.Alias i)
              fn tcs = tcs { tcsUnresolvable = Set.insert i (tcsUnresolvable tcs) }
  case Map.lookup i im of
    Nothing -> retUnsupported
    Just (Resolved tp) -> return tp
    Just Active -> retUnsupported
    Just (Pending tp) -> do
        modify (ins Active)
        stp <- tcType tp
        stp <$ modify (ins (Resolved stp))
      where ins v tcs = tcs { tcsMap = Map.insert i v (tcsMap tcs) }

resolveMemType :: SymType -> TC (Maybe MemType)
resolveMemType = resolve
  where resolve (MemType mt) = return (Just mt)
        resolve (Alias i) = resolve =<< tcIdent i
        resolve _ = return Nothing

resolveRetType :: SymType -> TC (Maybe RetType)
resolveRetType = resolve
  where resolve (MemType mt) = return (Just (Just mt))
        resolve (Alias i) = resolve =<< tcIdent i
        resolve VoidType = return (Just Nothing)
        resolve _ = return Nothing

tcMemType :: L.Type -> TC (Maybe MemType)
tcMemType = resolveMemType <=< tcType

tcType :: L.Type -> TC SymType
tcType tp0 = do
  let badType = UnsupportedType tp0 <$ recordUnsupported tp0
  let maybeApp :: (a -> MemType) -> TC (Maybe a) -> TC SymType
      maybeApp f mmr = maybe badType (return . MemType . f) =<< mmr
  case tp0 of
    L.PrimType pt ->
      case pt of
        L.FloatType ft -> do
          case ft of
            L.Float -> return $ MemType FloatType
            L.Double -> return $ MemType DoubleType
            L.X86_fp80 -> return $ MemType X86_FP80Type
            _ -> badType
        L.Integer w -> return $ MemType $ IntType (fromIntegral w)
        L.Void -> return VoidType
        L.Metadata -> return $ MemType MetadataType
        _ -> badType
    L.Alias i -> return (Alias i)
    L.Array n etp -> maybeApp (ArrayType (fromIntegral n)) $ tcMemType etp
    L.FunTy res args va -> do
      mrt <- resolveRetType =<< tcType res
      margs <- traverse tcMemType args
      maybe badType (return . FunType) $
        FunDecl <$> mrt <*> sequence margs <*> pure va
    L.PtrTo tp ->  (MemType . PtrType) <$> tcType tp
    L.Struct tpl       -> maybeApp StructType $ tcStruct False tpl
    L.PackedStruct tpl -> maybeApp StructType $ tcStruct True  tpl
    L.Vector n etp -> maybeApp (VecType (fromIntegral n)) $ tcMemType etp
    L.Opaque -> return OpaqueType

-- | Constructs a function for obtaining target-specific size/alignment
-- information about structs.  The function produced corresponds to the
-- StructLayout object constructor in TargetData.cpp.
tcStruct :: Bool -> [L.Type] -> TC (Maybe StructInfo)
tcStruct packed fldTys = do
  pdl <- gets tcsDataLayout
  fieldMemTys <- traverse tcMemType fldTys
  return (mkStructInfo pdl packed <$> sequence fieldMemTys)


type AliasMap = Map Ident SymType
type MetadataMap = IntMap L.ValMd

-- | Provides information about the types in an LLVM bitcode file.
data TypeContext = TypeContext
  { llvmDataLayout :: DataLayout
  , llvmMetadataMap :: MetadataMap
  , llvmAliasMap  :: AliasMap
  }

instance Show TypeContext where
  show = show . ppTypeContext

ppTypeContext :: TypeContext -> Doc ann
ppTypeContext lc =
    vcat (ppAlias <$> Map.toList (llvmAliasMap lc))
  where ppAlias (i,tp) = ppIdent i <+> equals <+> ppSymType tp

lookupAlias :: (?lc :: TypeContext, MonadError String m) => Ident -> m SymType
lookupAlias i =
  case llvmAliasMap ?lc ^. at i of
    Just stp -> return stp
    Nothing  -> throwError $ unwords ["Unknown type alias", show i]

lookupMetadata :: (?lc :: TypeContext) => Int -> Maybe L.ValMd
lookupMetadata x = view (at x) (llvmMetadataMap ?lc)

-- | If argument corresponds to a @MemType@ possibly via aliases,
-- then return it.  Otherwise, returns @Nothing@.
asMemType :: (?lc :: TypeContext, MonadError String m) => SymType -> m MemType
asMemType (MemType mt) = return mt
asMemType (Alias i) = asMemType =<< lookupAlias i
asMemType stp = throwError (unlines $ ["Expected memory type", show stp])

-- | If argument corresponds to a @RetType@ possibly via aliases,
-- then return it.  Otherwise, returns @Nothing@.
asRetType :: (?lc :: TypeContext, MonadError String m) => SymType -> m RetType
asRetType (MemType mt) = return (Just mt)
asRetType VoidType     = return Nothing
asRetType (Alias i)    = asRetType =<< lookupAlias i
asRetType stp = throwError (unlines $ ["Expected return type", show stp])

-- | Creates an LLVMContext from a parsed data layout and lists of types.
--  Errors reported in first argument.
mkTypeContext :: DataLayout -> MetadataMap -> [L.TypeDecl]  -> ([Doc ann], TypeContext)
mkTypeContext dl mdMap decls =
    let tps = Map.fromList [ (L.typeName d, L.typeValue d) | d <- decls ] in
    runTC dl (Pending <$> tps) $
      do aliases <- traverse tcType tps
         pure (TypeContext dl mdMap aliases)

-- | Utility function to creates an LLVMContext directly from a model.
typeContextFromModule :: L.Module -> ([Doc ann], TypeContext)
typeContextFromModule mdl = mkTypeContext dl (L.mkMdMap mdl) (L.modTypes mdl)
  where dl = parseDataLayout $ L.modDataLayout mdl

liftType :: (?lc :: TypeContext, MonadError String m) => L.Type -> m SymType
liftType tp | null edocs = return stp
            | otherwise  = throwError $ unlines (map show edocs)
  where m0 = Resolved <$> llvmAliasMap ?lc
        (edocs,stp) = runTC (llvmDataLayout ?lc) m0 $ tcType tp

liftMemType :: (?lc :: TypeContext, MonadError String m) => L.Type -> m MemType
liftMemType tp = asMemType =<< liftType tp

liftRetType :: (?lc :: TypeContext, MonadError String m) => L.Type -> m RetType
liftRetType tp = asRetType =<< liftType tp

liftDeclare :: (?lc::TypeContext, MonadError String m) => L.Declare -> m FunDecl
liftDeclare decl =
  do args <- traverse liftMemType (L.decArgs decl)
     ret  <- liftRetType (L.decRetType decl)
     return $ FunDecl
              { fdRetType  = ret
              , fdArgTypes = args
              , fdVarArgs  = L.decVarArgs decl
              }

compatStructInfo :: StructInfo -> StructInfo -> Bool
compatStructInfo x y =
  siIsPacked x == siIsPacked y &&
    compatMemTypeVectors (siFieldTypes x) (siFieldTypes y)

-- | Returns true if types are bit-level compatible.
--
compatMemTypes :: MemType -> MemType -> Bool
compatMemTypes x0 y0 =
  case (x0, y0) of
    (IntType x, IntType y) -> x == y
    (FloatType, FloatType) -> True
    (DoubleType, DoubleType) -> True
    (PtrType{}, PtrType{})   -> True
    (ArrayType xn xt, ArrayType yn yt) ->
      xn == yn && xt `compatMemTypes` yt
    (VecType   xn xt, VecType   yn yt) ->
      xn == yn && xt `compatMemTypes` yt
    (StructType x, StructType y) -> x `compatStructInfo` y
    _ -> False

compatRetTypes :: RetType -> RetType -> Bool
compatRetTypes Nothing Nothing = True
compatRetTypes (Just x) (Just y) = compatMemTypes x y
compatRetTypes _ _ = False

compatMemTypeLists :: [MemType] -> [MemType] -> Bool
compatMemTypeLists [] [] = True
compatMemTypeLists (x:xl) (y:yl) =
  compatMemTypes x y && compatMemTypeLists xl yl
compatMemTypeLists _ _ = False

compatMemTypeVectors :: V.Vector MemType -> V.Vector MemType -> Bool
compatMemTypeVectors x y =
  V.length x == V.length y &&
  allOf traverse (uncurry compatMemTypes) (V.zip x y)
