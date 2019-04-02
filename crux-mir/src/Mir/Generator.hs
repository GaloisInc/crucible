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

-- The data structures used during translation, especially those concerned with
-- the dictionary-passing interpretation of Traits.
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
import           Mir.MirTy
import           Mir.Intrinsics
import           Mir.GenericOps(ATDict)


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

-- * The top-level generator type

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
              _collection :: !Collection,
              _assocTyMap :: ATDict
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

data MirHandle = forall init ret. 
    MirHandle { _mhName       :: MethName
              , _mhSig        :: FnSig
              -- The type of the function handle includes "free variables"
              , _mhHandle     :: FnHandle init ret
              }


instance Show MirHandle where
    show (MirHandle _nm sig c) =
      show c ++ ":" ++ show sig

instance Pretty MirHandle where
    pretty (MirHandle nm sig _c) =
      text (show nm) <> colon <> pretty sig 

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
   -- TyParam 0 is the "Self" type that will be replaced in all
   -- instances
   -- There may be other associated types for the trait (i.e.
   -- TyParam 1, ...
  ,_methodIndex :: Map MethName (Some (Index ctx))
   -- ^ Tells which fields (indices) of the struct correspond to
   -- method names of the given trait
  ,_vtables :: Map Ty (Assignment (MirValue s) ctx)
   -- ^ Gives the vtable for each type implementing a given trait
   -- the type Ty may have free type variables, in which case the lookup
   -- function will match against the type to resolve the instance
   -- TODO: if the impl methods need additional preds, we won't be able to
   -- add them. Need a work-around for this.
  }


-- | The values stored in the vtables --- Crucible expressions 
-- This type must be a *specialization* of the expected type of the vtable
data MirValue s ty where
  MirValue :: SubstRepr implSubst
           -> TypeRepr   (ImplementTrait implSubst ty)
           -> Expr MIR s (ImplementTrait implSubst ty)
           -> [Predicate]
           -> MirValue s ty

-- | The main data type for values, bundling the term-level
-- type ty along with a crucible expression of type ty
data MirExp s where
    MirExp :: TypeRepr ty -> Expr MIR s ty -> MirExp s
instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)



-- | Type-level instantiation function 
-- This seems a little weird. Why don't we shift the substitution inside the polytype?
type family ImplementTrait (implSubst :: Substitution) (arg :: CrucibleType) :: CrucibleType where  
  ImplementTrait implSubst (PolyFnType k args ret) =
      PolyFnType k  (Instantiate implSubst args) (Instantiate implSubst ret)
  -- ImplementTrait implSubst (ty :: CrucibleType)  = Instantiate implSubst ty                                               

-- | Map the instantiation function across the context
type family ImplementCtxTrait (implSubst :: Substitution) (arg :: Ctx k) :: Ctx k where
  ImplementCtxTrait implSubst EmptyCtx = EmptyCtx
  ImplementCtxTrait implSubst (ctx ::> ty) = ImplementCtxTrait implSubst ctx ::> ImplementTrait implSubst ty

-- | "Repr" versions of the above
implementRepr :: SubstRepr implSubst -> TypeRepr ty -> TypeRepr (ImplementTrait implSubst ty)
implementRepr implSubst (PolyFnRepr k args ret) =
  PolyFnRepr k (instantiate implSubst args) (instantiate implSubst ret)
implementRepr implSubst ty = error "ImplementRepr: should only be called with polymorphic function types"

implementCtxRepr :: SubstRepr implSubst -> CtxRepr ctx -> CtxRepr (ImplementCtxTrait implSubst ctx)
implementCtxRepr _implSubst Empty = Empty
implementCtxRepr implSubst (ctx :> ty) = implementCtxRepr implSubst ctx :> implementRepr implSubst ty

implementIdx :: SubstRepr implSubst -> Index ctx a -> Index (ImplementCtxTrait implSubst ctx) (ImplementTrait implSubst a)
implementIdx _implSubst idx = unsafeCoerce idx


-- | Extract the Crucible expression from the vtable. Must provide the correct instantiation
-- for this particular value, or fails at runtime
valueToExpr :: SubstRepr implSubst -> MirValue s ty -> Expr MIR s (ImplementTrait implSubst ty)
valueToExpr wantedImpl (MirValue implRepr _ e _)
  | Just Refl <- testEquality wantedImpl implRepr
  = e
  | otherwise 
  = error $ "BUG: Invalid implementation type. " 

vtblToStruct :: SubstRepr implSubst -> Assignment (MirValue s) ctx
             -> Assignment (Expr MIR s) (ImplementCtxTrait implSubst ctx)
vtblToStruct _implSubst Empty = Empty
vtblToStruct implSubst (ctx :> val) = vtblToStruct implSubst ctx :> valueToExpr implSubst val

------------------------------------------------------------------------------------
-- ** Working with generic traits (i.e. not specialized to any particular translation 's')
-- In practice, this means that the values can only be FunctionHandles

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

   
{-
addVTable :: forall s implSubst. TraitName -> Ty -> [Predicate] -> SubstRepr implSubst -> [ (MethName, MirExp s) ] -> TraitMap s -> TraitMap s
addVTable tname ty preds implSubst meths (TraitMap tm) =
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
                  Just Refl -> return (MirValue implSubst tyr e preds)
                  Nothing   -> error "Invalid type for addVTable"
                   
          asgn'  = runIdentity (traverseWithIndex go ctxr)
          timpl' = timpl { _vtables = Map.insert ty asgn' vtab } in
      TraitMap (Map.insert tname (Some timpl') tm)
-}       

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




-------------------------------------------------------------------------------------------------------

makeLenses ''TraitImpls
makeLenses ''FnState
makeLenses ''MirHandle

$(return [])

------------------------------------------------------------------------------------

first :: (a -> Maybe b) -> [a] -> Maybe b
first f [] = Nothing
first f (x:xs) = case f x of Just y   -> Just y
                             Nothing  -> first f xs

------------------------------------------------------------------------------------

-- TODO: remove errors and return Nothing instead
-- | Given a (static)-trait method name and type substitution, figure out which
-- trait implementation to use
resolveStaticTrait :: StaticTraitMap -> Collection -> TraitMap s -> MethName -> Substs -> Maybe (MirExp s, [Predicate])
resolveStaticTrait stm col tm mn sub =
  case  Map.lookup mn stm of
    Just ts -> case sub of
      (Substs (_:_)) -> first (\tn -> resolveTraitMethod tm tn sub mn) ts
      Substs []      -> error $ "Cannot resolve trait " ++ show mn ++ " without type arguments"
    Nothing -> Nothing

resolveTraitMethod :: TraitMap s -> TraitName -> Substs -> MethName -> Maybe (MirExp s, [Predicate])
resolveTraitMethod (TraitMap tmap) tn (Substs subs@(ty:_)) mn
  | Just (Some timpls) <- Map.lookup tn tmap
  , Just (Some idx)    <- Map.lookup mn (timpls^.methodIndex)
  = do
     let vtab = timpls^.vtables
     case Map.lookup ty vtab of
       Just assn -> case assn ! idx of 
         MirValue _ tye e preds -> return (MirExp tye e, preds)
       Nothing   ->
         let -- go :: Ty -> Assignment (MirValue s) ctx -> Maybe (MirExp s) -> Maybe (MirExp s)
             go keyTy assn res =
               case matchTy ty keyTy of
                 Nothing -> res
                 Just _inst -> case (assn ! idx) of
                   MirValue _ ty e preds -> Just (MirExp ty e, preds)
         in                     
            Map.foldrWithKey go Nothing vtab
            
resolveTraitMethod _ tn (Substs (_:_)) mn = 
  error $ "Cannot find trait " ++ show tn ++ " or its method " ++ show mn
resolveTraitMethod (TraitMap tmap) tn (Substs []) mn =
  error $ "Cannot resolve trait without type arguments"


-------------------------------------------------------------------------------------------------------

--  LocalWords:  ty ImplementTrait ctx vtable
