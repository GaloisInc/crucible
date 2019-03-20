{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}

-- Turn off some warnings during active development
{-# OPTIONS_GHC -Wincomplete-patterns -Wall
                -fno-warn-unused-imports
                -fno-warn-name-shadowing
                -fno-warn-unused-matches
                -fno-warn-unticked-promoted-constructors #-}

module Mir.Generator
{-
, MirGenerator
, VarMap
, VarInfo (..)
, varInfoRepr
, LabelMap
, AdtMap
, TraitMap (..)
, TraitImpls (..)
, vtableTyRepr
, methodIndex
, vtables
, traitImpls
, FnState (..)
, MirExp (..)
, MirHandle (..)
, HandleMap
, varMap
, labelMap
, handleMap
, traitMap
, MirValue(..)
, valueToExpr
  , getTraitImplementation) 
-}
where

import           Data.Kind(Type)

import qualified Data.Maybe as Maybe
import           Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import qualified Data.Text as Text
import           Data.Functor.Identity
--import           Control.Monad

import           Control.Lens hiding (Empty, (:>), Index, view)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

import           Lang.Crucible.CFG.Generator hiding (dropRef)

import           Mir.DefId
import           Mir.Mir
import           Mir.Intrinsics


import           Unsafe.Coerce(unsafeCoerce)
import           Control.Monad
import           Debug.Trace


---------------------------------------------------------------------------------
-- TODO: Should be in Data.Parameterized.Classes
-- 
-- Safe usage requires that f be a singleton type
newtype DI f a = Don'tInstantiate (KnownRepr f a => Dict (KnownRepr f a))

knownInstance :: forall a f . f a -> Dict (KnownRepr f a)
knownInstance s = with_sing_i Dict
  where
    with_sing_i :: (KnownRepr f a => Dict (KnownRepr f a)) -> Dict (KnownRepr f a)
    with_sing_i si = unsafeCoerce (Don'tInstantiate si) s

-- | convert an explicit repr to an implicit repr
withKnownRepr :: forall n r f. f n -> (KnownRepr f n => r) -> r
withKnownRepr si r = case knownInstance si of
                        Dict -> r
---------------------------------------------------------------------------------
  

-- h for state monad
-- s phantom parameter for CFGs
type MirGenerator h s ret = Generator MIR h s FnState ret

--------------------------------------------------------------------------------
-- ** Generator state for MIR translation to Crucible
--
-- | Generator state for MIR translation
data FnState (s :: Type)
  = FnState { _varMap    :: !(VarMap s),
              _preds     :: [Predicate],
              _labelMap  :: !(LabelMap s),              
              _handleMap :: !HandleMap,
              _traitMap  :: !(TraitMap s),
              _staticTraitMap :: !StaticTraitMap,
              _debugLevel :: !Int,
              _collection :: !Collection
            }


---------------------------------------------------------------------------
-- *** VarMap

-- | The VarMap maps identifier names to registers (if the id
--   corresponds to a local variable) or an atom (if the id
--   corresponds to a function argument)
type VarMap s = Map Text.Text (Some (VarInfo s))
data VarInfo s tp where
  VarRegister  :: Reg s tp -> VarInfo s tp
  VarReference :: Reg s (MirReferenceType tp) -> VarInfo s tp
  VarAtom      :: Atom s tp -> VarInfo s tp

varInfoRepr :: VarInfo s tp -> TypeRepr tp
varInfoRepr (VarRegister reg0)  = typeOfReg reg0
varInfoRepr (VarReference reg0) =
  case typeOfReg reg0 of
    MirReferenceRepr tp -> tp
    _ -> error "impossible: varInfoRepr"
varInfoRepr (VarAtom a) = typeOfAtom a

---------------------------------------------------------------------------
-- *** LabelMap

-- | The LabelMap maps identifiers to labels of their corresponding basicblock
type LabelMap s = Map.Map BasicBlockInfo (Label s)

---------------------------------------------------------------------------
-- *** HandleMap

data MirHandle where
    MirHandle :: MethName -> FnSig -> [Predicate] -> FnHandle init ret -> MirHandle

instance Show MirHandle where
    show (MirHandle _nm sig preds c) = show c ++ ":" ++ show sig ++ " where " ++ show preds

instance Pretty MirHandle where
    pretty (MirHandle nm sig preds _c) = text (show nm) <> colon <> pretty sig <+> text "where" <+> pretty preds

-- | The HandleMap maps mir functions to their corresponding function
-- handle. Function handles include the original method name (for
-- convenience) and original Mir type (for trait resolution).
type HandleMap = Map.Map MethName MirHandle

---------------------------------------------------------------------------
-- *** TraitMap and StaticTraitMap

-- | A TraitMap maps trait names to their vtables and instances
data TraitMap (s::Type) = TraitMap (Map TraitName (Some (TraitImpls s)))

-- | A StaticTraitMap maps trait method names to all traits that contain them
-- (There could be multiple, and will need to use type info to resolve further)
type StaticTraitMap = Map.Map MethName [TraitName]


-- | The implementation of a Trait.
-- The 'ctx' parameter lists the required members of the trait
-- NOTE: the vtables are an instance of the more general type
-- listed in the vtableTyRepr
data TraitImpls (s::Type) ctx = TraitImpls
  {_vtableTyRepr :: CtxRepr ctx
   -- ^ Describes the types of Crucible structs that store the VTable
   -- of implementations
  ,_methodIndex :: Map MethName (Some (Index ctx))
   -- ^ Tells which fields (indices) of the struct correspond to
   -- method names of the given trait
  ,_vtables :: Map Ty (Assignment (MirValue s) ctx)
   -- ^ gives the vtable for each type implementing a given trait
   -- the type Ty may have free type variables, in which case the lookup
   -- function will match against the type to resolve the instance 
  }


type family ImplementTrait (implSubst :: Substitution) (arg :: k) :: k where
  -- Ctx k
  ImplementTrait implSubst EmptyCtx = EmptyCtx
  ImplementTrait implSubst (ctx ::> ty) = ImplementTrait implSubst ctx ::> ImplementTrait implSubst ty
  -- CrucibleType
  ImplementTrait implSubst (PolyFnType k args ret) =
      PolyFnType k  (Instantiate implSubst args) (Instantiate implSubst ret)
  -- ImplementTrait implSubst (ty :: CrucibleType)  = Instantiate implSubst ty                                               

implementRepr :: SubstRepr implSubst -> TypeRepr ty -> TypeRepr (ImplementTrait implSubst ty)
implementRepr implSubst (PolyFnRepr k args ret) =
  PolyFnRepr k (instantiate implSubst args) (instantiate implSubst ret)
implementRepr implSubst ty = error "ImplementRepr: should only be called with polymorphic function types"

implementCtxRepr :: SubstRepr implSubst -> CtxRepr ctx -> CtxRepr (ImplementTrait implSubst ctx)
implementCtxRepr _implSubst Empty = Empty
implementCtxRepr implSubst (ctx :> ty) = implementCtxRepr implSubst ctx :> implementRepr implSubst ty

implementIdx :: SubstRepr implSubst -> Index ctx a -> Index (ImplementTrait implSubst ctx) (ImplementTrait implSubst a)
implementIdx _implSubst idx = unsafeCoerce idx

-- | Compute the type of values stored in the vtables. 
-- This type must be a specialization of the expected type of the vtable
data MirValue s ty where
  MirValue :: SubstRepr implSubst
           -> TypeRepr   (ImplementTrait implSubst ty)
           -> Expr MIR s (ImplementTrait implSubst ty)  
           -> MirValue s ty

valueToExpr :: SubstRepr implSubst -> MirValue s ty -> Expr MIR s (ImplementTrait implSubst ty)
valueToExpr wantedImpl (MirValue implRepr _ e)
  | Just Refl <- testEquality wantedImpl implRepr
  = e
  | otherwise 
  = error $ "Invalid implementation type. "

vtblToStruct :: SubstRepr implSubst -> Assignment (MirValue s) ctx
             -> Assignment (Expr MIR s) (ImplementTrait implSubst ctx)
vtblToStruct _implSubst Empty = Empty
vtblToStruct implSubst (ctx :> val) = vtblToStruct implSubst ctx :> valueToExpr implSubst val

------------------------------------------------------------------------------------
-- ** Working with generic traits (i.e. not specialized to any particular translation)

data GenericMirValue ty    = GenericMirValue   (forall (s::Type). MirValue s ty)
data GenericTraitImpls ctx = GenericTraitImpls (forall (s::Type). TraitImpls s ctx)
data GenericTraitMap       = GenericTraitMap   (forall (s::Type). Map TraitName (Some (TraitImpls s)))


mkGenericTraitMap :: [(TraitName,Some GenericTraitImpls)] -> GenericTraitMap
mkGenericTraitMap [] = GenericTraitMap Map.empty
mkGenericTraitMap ((tn,Some (GenericTraitImpls impls)):rest) =
  case mkGenericTraitMap rest of
    GenericTraitMap m ->
      GenericTraitMap (Map.insert tn (Some impls) m)

mkGenericTraitImpls ::  CtxRepr ctx
           -> Map.Map MethName (Some (Index ctx))
           -> Map.Map Ty (Assignment GenericMirValue ctx)
           -> GenericTraitImpls ctx
mkGenericTraitImpls str midx vtbls' =
  GenericTraitImpls $
  let g (GenericMirValue mv) = mv
      vtbls = fmap (fmapFC g) vtbls'
  in
    TraitImpls {_vtableTyRepr = str
               ,_methodIndex  = midx
               ,_vtables      = vtbls
               }


mkStaticTraitMap :: [(TraitName,Some GenericTraitImpls)] -> Map.Map MethName [TraitName]
mkStaticTraitMap impls = foldr g Map.empty impls where
  g :: (TraitName, Some GenericTraitImpls) -> StaticTraitMap -> StaticTraitMap
  g (tn, Some (GenericTraitImpls (TraitImpls _ mi _))) stm =
    let meths = Map.keys mi in
      foldr (\n m -> Map.insertWith (++) n [tn] m) stm meths

-- | The main data type for values, bundling the term-level type tp along with a crucible expression of type tp.
data MirExp s where
    MirExp :: TypeRepr tp -> Expr MIR s tp -> MirExp s
instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)
   

addVTable :: forall s implSubst. TraitName -> Ty -> SubstRepr implSubst -> [ (MethName, MirExp s) ] -> TraitMap s -> TraitMap s
addVTable tname ty implSubst meths (TraitMap tm) =
  case Map.lookup tname tm of
    Nothing -> error "Trait not found"
    Just (Some (timpl@(TraitImpls ctxr _mi vtab))) ->
      let go :: Index ctx ty -> TypeRepr ty -> Identity (MirValue s ty)
          go idx tyr2 = do
            let i = indexVal idx
            let (_implName, smv) = if i < length meths then meths !! i else error "impl_vtable: BUG"
            case smv of
              (MirExp tyr e) ->                
                case testEquality tyr (implementRepr implSubst tyr2)  of
                  Just Refl -> return (MirValue implSubst tyr e)
                  Nothing   -> error "Invalid type for addVTable"
                   
          asgn'  = runIdentity (traverseWithIndex go ctxr)
          timpl' = timpl { _vtables = Map.insert ty asgn' vtab } in
      TraitMap (Map.insert tname (Some timpl') tm)
         

------------------------------------------------------------------------------------
-- ** helper function for traits


-- | Smart constructor
traitImpls :: CtxRepr ctx
           -> Map.Map MethName (Some (Index ctx))
           -> Map.Map Ty (Assignment (MirValue s) ctx)
           -> TraitImpls s ctx
traitImpls str midx vtbls =
  TraitImpls {_vtableTyRepr = str
             ,_methodIndex  = midx
             ,_vtables      = vtbls
             }


type Solution = Integer 

combineMaps :: Map Solution Ty -> Map Solution Ty -> Maybe (Map Solution Ty)
combineMaps m1 m2 = Map.foldrWithKey go (Just m2) m1 where
  go :: Solution -> Ty -> Maybe (Map Solution Ty) -> Maybe (Map Solution Ty)
  go _k _ty Nothing = Nothing
  go k ty (Just res) =
    case Map.lookup k res of
      Just ty' -> if ty == ty' then Just res else Nothing
      Nothing ->  Just (Map.insert k ty res)

-- | Try to match an implementation type against a trait type
matchSig :: FnSig -> FnSig -> Maybe (Map Solution Ty)
matchSig (FnSig instArgs instRet) (FnSig genArgs genRet) = do
  m1 <- matchTys instArgs genArgs
  m2 <- matchTy  instRet  genRet
  combineMaps m1 m2

-- | Try to match an implementation type (first argument) against a (generic) trait type  
matchTy :: Ty -> Ty -> Maybe (Map Solution Ty)
matchTy inst arg
  | inst == arg
  = return Map.empty
matchTy ty (TyParam i) 
  = return (Map.insert i ty Map.empty)
matchTy (TyTuple instTys) (TyTuple genTys) =
  matchTys instTys genTys
matchTy (TySlice t1) (TySlice t2) = matchTy t1 t2
matchTy (TyArray t1 i1) (TyArray t2 i2) | i1 == i2 = matchTy t1 t2
matchTy (TyRef t1 m1) (TyRef t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyAdt d1 s1) (TyAdt d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyFnDef d1 s1) (TyFnDef d2 s2) | d1 == d2 = matchSubsts s1 s2
matchTy (TyClosure d1 s1) (TyClosure d2 s2) | d1 == d2 =  matchSubsts s1 s2
matchTy (TyFnPtr sig1) (TyFnPtr sig2) = matchSig sig1 sig2
matchTy (TyRawPtr t1 m1)(TyRawPtr t2 m2) | m1 == m2 = matchTy t1 t2
matchTy (TyDowncast t1 i1) (TyDowncast t2 i2) | i1 == i2 = matchTy t1 t2
matchTy ty1 ty2@(TyProjection d2 s2) = error $
  "BUG: found " ++ show (pretty ty2) ++ " when trying to match " ++ show (pretty ty1)
  

-- more
matchTy _ _ = Nothing

matchSubsts :: Substs -> Substs -> Maybe (Map Solution Ty)
matchSubsts (Substs tys1) (Substs tys2) = matchTys tys1 tys2

matchTys :: [Ty] -> [Ty] -> Maybe (Map Solution Ty)
matchTys [] [] = return Map.empty
matchTys (t1:instTys) (t2:genTys) = do
  m1 <- matchTy t1 t2
  m2 <- matchTys instTys genTys
  combineMaps m1 m2
matchTys _ _ = Nothing  
  
-- | Decide whether the given method definition is an implementation method for
-- a declared trait. If so, return any such declared traits along with the type substitution
  
getTraitImplementation :: Map.Map DefId Trait          -- ^ all traits in the collection
                       -> (MethName,MirHandle)         -- ^ a specific function in the collection
                       -> [(TraitName, Substs)]        -- ^ traits that this function could implement
getTraitImplementation trts (name, handle@(MirHandle _mname sig _ _fh))
  -- find just the text of the method name
  | Just methodEntry <- parseImplName name = do
  
    -- find signature of methods that use this name
    let isTraitMethod (TraitMethod tm ts) = if sameTraitMethod methodEntry tm then Just (tm,ts) else Nothing
        isTraitMethod _ = Nothing

    -- traits, potential methods, plus their method signatures
    let namedTraits = [ (tr, tm, ts) | tr@(Trait _tn items _supers) <- Map.elems trts,
                                       (tm,ts) <- Maybe.mapMaybe isTraitMethod items ]

    --traceM $ "named Traits for : " ++ show name
    --traceM $ "\t with sig: " ++ show (pretty sig)
    --forM_ namedTraits $ \(tr,tm,ts) -> do
    --     traceM $ "\t traitName:" ++ show (tr^.traitName) ++ " has method " ++ show tm 
    --     traceM $ "\t withSig:  " ++ show (pretty ts)         
  
    let typedTraits = Maybe.mapMaybe (\(tr,tm,ts) -> (tr,tm,ts,) <$> matchSig sig ts) namedTraits

    let g (trait,_,_,instMap) =
        -- TODO: hope all of the params actually appear....
         -- otherwise there will be a gap
              (trait^.traitName, Substs (Map.elems instMap))

--    traceM $ "TypedTraits for : " ++ show name
--    forM_ typedTraits $ \(tn,_tm,_ts,_) -> do
--         traceM $ "\t" ++ show tn 

    
    map g typedTraits
getTraitImplementation _ _ = []

-------------------------------------------------------------------------------------------------------

makeLenses ''TraitImpls
makeLenses ''FnState


$(return [])

------------------------------------------------------------------------------------

first :: (a -> Maybe b) -> [a] -> Maybe b
first f [] = Nothing
first f (x:xs) = case f x of Just y   -> Just y
                             Nothing  -> first f xs

-- TODO: remove errors and return Nothing instead
resolveStaticTrait :: StaticTraitMap -> TraitMap s -> MethName -> Substs -> Maybe (MirExp s)
resolveStaticTrait stm tm mn sub =
  case  Map.lookup mn stm of
    Just ts -> case sub of
      (Substs (_:_)) -> first (\tn -> resolveTraitMethod tm tn sub mn) ts
      Substs []      -> error $ "Cannot resolve trait " ++ show mn ++ " without type arguments"
    Nothing -> Nothing

resolveTraitMethod :: TraitMap s -> TraitName -> Substs -> MethName -> Maybe (MirExp s)
resolveTraitMethod (TraitMap tmap) tn (Substs subs@(ty:_)) mn
  | Just (Some timpls) <- Map.lookup tn tmap
  , Just (Some idx)    <- Map.lookup mn (timpls^.methodIndex)
  = do
     let vtab = timpls^.vtables
     case Map.lookup ty vtab of
       Just assn -> case assn ! idx of 
         MirValue _ tye e -> return (MirExp tye e)
       Nothing   ->
         let -- go :: Ty -> Assignment (MirValue s) ctx -> Maybe (MirExp s) -> Maybe (MirExp s)
             go keyTy assn res =
               case matchTy ty keyTy of
                 Nothing -> res
                 Just _inst -> case (assn ! idx) of
                   MirValue _ ty e -> Just $ MirExp ty e
         in                     
            Map.foldrWithKey go Nothing vtab
            
resolveTraitMethod _ tn (Substs (_:_)) mn = 
  error $ "Cannot find trait " ++ show tn ++ " or its method " ++ show mn
resolveTraitMethod (TraitMap tmap) tn (Substs []) mn =
  error $ "Cannot resolve trait without type arguments"


-------------------------------------------------------------------------------------------------------

--  LocalWords:  ty ImplementTrait ctx vtable
