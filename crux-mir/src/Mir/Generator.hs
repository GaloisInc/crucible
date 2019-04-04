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
-- the dictionary-passing interpretation of traits.
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
import           Control.Monad

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.Peano

import           Lang.Crucible.FunctionHandle
import           Lang.Crucible.Types

import           Lang.Crucible.CFG.Generator hiding (dropRef)

import           Mir.DefId
import           Mir.Mir
import           Mir.MirTy
import           Mir.Intrinsics
import           Mir.GenericOps(ATDict)
import           Mir.PP

import           Unsafe.Coerce(unsafeCoerce)
import           Debug.Trace
import           GHC.Stack


---------------------------------------------------------------------------------

-- | The main data type for values, bundling the term-level
-- type ty along with a crucible expression of type ty
data MirExp s where
    MirExp :: TypeRepr ty -> Expr MIR s ty -> MirExp s
instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)

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
type LabelMap s = Map BasicBlockInfo (Label s)

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
type HandleMap = Map MethName MirHandle

---------------------------------------------------------------------------
-- *** TraitMap and StaticTraitMap

-- | A TraitMap maps trait names to their vtables and instances
data TraitMap (s::Type) = TraitMap (Map TraitName (Some (TraitImpls s)))

-- | A StaticTraitMap maps trait method names to all traits that contain them
-- (There could be multiple, and will need to use type info to resolve further)
type StaticTraitMap = Map MethName [TraitName]


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
  ,_vtables :: Map [Ty] (Assignment (MirValue s) ctx)
   -- ^ Gives the vtable for each type substitution implementing a given trait
   -- the length of [Ty] depends on the number of type params to the trait
   -- (usually one, called Self, but could be more)
   -- 
   -- NOTE: the index types [Ty] may have free type variables, in which case the lookup
   -- function will match against the type to resolve the instance
   -- TODO: if the impl methods need additional preds, we won't be able to
   -- add them. Need a work-around for this.
  }


-- | The values stored in the vtables --- Crucible expressions 
-- This type must be a *specialization* of the expected type of the vtable
data MirValue s ty where
  MirValue :: CtxRepr implSubst
           -> TypeRepr   (ImplementTrait implSubst ty)
           -> Expr MIR s (ImplementTrait implSubst ty)
           -> FnSig
           -> MirValue s ty




-- | Type-level instantiation function
-- All values stored in the vtables must be polymorphic functions
type family ImplementTrait (timpls :: Ctx CrucibleType ) (arg :: CrucibleType) :: CrucibleType where  
  ImplementTrait timpls (PolyFnType k args ret) =
    PolyFnType (Minus k (CtxSizeP timpls))
               (Instantiate (MkSubst timpls) args)
               (Instantiate (MkSubst timpls) ret)
         
-- | Map the instantiation function across a context
type family ImplementCtxTrait (implSubst :: Ctx CrucibleType) (arg :: Ctx k) :: Ctx k where
  ImplementCtxTrait implSubst EmptyCtx = EmptyCtx
  ImplementCtxTrait implSubst (ctx ::> ty) = ImplementCtxTrait implSubst ctx ::> ImplementTrait implSubst ty

-- | "Repr" versions of the above
implementRepr :: CtxRepr implSubst -> TypeRepr ty -> TypeRepr (ImplementTrait implSubst ty)
implementRepr implSubst (PolyFnRepr k args ret) =
  PolyFnRepr (minusP k (ctxSizeP implSubst))
             (instantiate (mkSubst implSubst) args) (instantiate (mkSubst implSubst) ret)
implementRepr implSubst ty = error "ImplementRepr: should only be called with polymorphic function types"

implementCtxRepr :: CtxRepr implSubst -> CtxRepr ctx -> CtxRepr (ImplementCtxTrait implSubst ctx)
implementCtxRepr _implSubst Empty = Empty
implementCtxRepr implSubst (ctx :> ty) = implementCtxRepr implSubst ctx :> implementRepr implSubst ty

implementIdx :: CtxRepr implSubst -> Index ctx a -> Index (ImplementCtxTrait implSubst ctx) (ImplementTrait implSubst a)
implementIdx _implSubst idx = unsafeCoerce idx


-- | Extract the Crucible expression from the vtable. Must provide the correct instantiation
-- for this particular value, or fails at runtime
valueToExpr :: HasCallStack => CtxRepr implSubst -> MirValue s ty -> Expr MIR s (ImplementTrait implSubst ty)
valueToExpr wantedImpl (MirValue implRepr _ e _)
  | Just Refl <- testEquality wantedImpl implRepr
  = e
  | otherwise 
  = error $ "BUG: Invalid implementation type. " 

-- | Create a Crucible struct from the vtable --- this is a dictionary for the trait
vtblToStruct ::
     CtxRepr implSubst
  -> Assignment (MirValue s) ctx
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

mkGenericTraitImpls :: CtxRepr ctx
           -> Map MethName (Some (Index ctx))
           -> Map [Ty] (Assignment GenericMirValue ctx)
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
           -> Map.Map [Ty] (Assignment (MirValue s) ctx)
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
-- extra: Control.Monad.Extra

firstJustM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
firstJustM f [] = return Nothing
firstJustM f (x:xs) = do
  mx <- f x
  case mx of
    Just y  -> return $ Just y
    Nothing -> firstJustM f xs

------------------------------------------------------------------------------------


-- | Given a (static)-trait method name and type substitution, find the 
-- implementation to use
--
-- Returns the function, its type and any remaining substitution types not used for
-- method resolution.
-- If no method can be found, return Nothing
--
-- This returns a Maybe instead of failing so that we can try something else if 
-- resolution of the method name fails
--
-- NOTE: tries the 
resolveStaticTrait :: MethName -> Substs -> MirGenerator h s ret (Maybe (MirExp s, FnSig, Substs))
resolveStaticTrait mn sub = do
  stm <- use staticTraitMap
  case (stm Map.!? mn) of
    Just tns -> firstJustM (resolveStaticMethod mn sub) (getTraitName mn : tns)
    Nothing -> resolveStaticMethod mn sub (getTraitName mn)

resolveStaticMethod mn (Substs tys) tn = do
  col <- use collection
  (TraitMap tmap) <- use traitMap
  case (col^.traits) Map.!? tn of
    Nothing -> return $ Nothing -- fail $ "Cannot find trait in collection" ++ show tn
    Just trait -> do
      case tmap Map.!? tn of
        Nothing -> return $ Nothing -- fail $ "Cannot find trait in traitMap " ++ fmt tn
        Just (Some timpls) ->
          case (timpls^.methodIndex) Map.!? mn of
            Nothing -> return $ Nothing -- fail $ "Cannot find method " ++ fmt mn ++ " in trait " ++ fmt tn
            Just (Some idx) -> do
              let numParams       = length (trait^.traitParams)
              let (trTys,methTys) = splitAt numParams tys
--              traceM $ "resolveStaticTrait: looking for " ++ fmt mn ++ " in trait " ++ fmt tn
--              traceM $ "    with trTys   " ++ fmt trTys
--              traceM $ "    and methTys  " ++ fmt methTys
              let vtab            = timpls^.vtables
              case vtab Map.!? trTys of
                Just assn -> case assn ! idx of
                  MirValue _ tye e sig -> do
                    -- find it directly
                    return (Just (MirExp tye e, sig, Substs methTys))
                Nothing ->
                  -- find it via unification
                  let --go :: [Ty] -> Assignment (MirValue s) ctx -> Maybe (MirExp s) -> Maybe (MirExp s)
                      go keyTy assn res =
                        case matchTys trTys keyTy of
                          Nothing -> res
                          Just _inst -> case (assn ! idx) of
                            MirValue _ ty e sig -> Just (MirExp ty e, sig, Substs methTys)
                  in                     
                     return $ Map.foldrWithKey go Nothing vtab

-------------------------------------------------------------------------------------------------------

--  LocalWords:  ty ImplementTrait ctx vtable
