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

import qualified Data.List as List
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
import           Mir.GenericOps(ATDict,tySubst,mkSubsts,matchSubsts)
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
    MkTraitType (Minus k (CtxSizeP timpls))
                (Instantiate (MkSubst timpls) args)
                (Instantiate (MkSubst timpls) ret)

type family MkTraitType (k :: Peano) (args :: Ctx CrucibleType) (ret :: CrucibleType) where
  MkTraitType Z args ret = FunctionHandleType args ret
  MkTraitType k args ret = PolyFnType k args ret
         
-- | Map the instantiation function across a context
type family ImplementCtxTrait (implSubst :: Ctx CrucibleType) (arg :: Ctx k) :: Ctx k where
  ImplementCtxTrait implSubst EmptyCtx = EmptyCtx
  ImplementCtxTrait implSubst (ctx ::> ty) = ImplementCtxTrait implSubst ctx ::> ImplementTrait implSubst ty

-- | "Repr" versions of the above
implementRepr :: CtxRepr implSubst -> TypeRepr ty -> TypeRepr (ImplementTrait implSubst ty)
implementRepr implSubst (PolyFnRepr k args ret) =
  case peanoView (minusP k (ctxSizeP implSubst)) of
    ZRepr -> FunctionHandleRepr (instantiate (mkSubst implSubst) args) (instantiate (mkSubst implSubst) ret)
    SRepr n -> PolyFnRepr (minusP k (ctxSizeP implSubst))
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

firstJust :: (a -> Maybe b) -> [a] -> Maybe b
firstJust f = Maybe.listToMaybe . Maybe.mapMaybe f

------------------------------------------------------------------------------------
-- | Given a (static)-trait method name and type substitution, find the 
-- implementation to use.
-- Returns the handle for the method as well as all type arguments to supply
-- in the method call.
--
-- If no method can be found, return Nothing
--
-- This returns a Maybe instead of failing so that we can try something else if 
-- resolution fails
--
-- During method resolution, additional method arguments discovered via unification
-- are added to the beginning of the returned substs
--
resolveStaticTrait :: HasCallStack => MethName -> Substs -> MirGenerator h s ret (Maybe (MirHandle, Substs))
resolveStaticTrait mn sub = do
  stm <- use staticTraitMap
  case (stm Map.!? mn) of
    Just tns -> firstJustM (resolveStaticMethod mn sub) (getTraitName mn : tns)
    Nothing -> resolveStaticMethod mn sub (getTraitName mn)
                          
resolveStaticMethod :: HasCallStack => MethName -> Substs -> TraitName -> MirGenerator h s ret (Maybe (MirHandle, Substs))
resolveStaticMethod methName substs traitName = do
   db <- use debugLevel
   col <- use collection
   case (col^.traits) Map.!? traitName of
     Nothing -> return $ Nothing -- BUG: Cannot find trait in collection
     Just trait -> do
       let (traitSub, methSub) = splitAtSubsts (length (trait^.traitParams)) substs
       mimpl <- findItem methName traitSub trait
       case mimpl of
          Nothing -> return $ Nothing  -- OK: there is no impl for this method name & traitsub in this trait
          Just (traitImpl, unifier, traitImplItem) -> do
            hmap <- use handleMap
            case hmap Map.!? (traitImplItem^.tiiName) of
              Nothing -> return Nothing -- BUG: impls should all be in the handle map
              Just mh -> do                
                let ulen = case Map.lookupMax unifier of
                                  Just (k,_) -> k + 1
                                  Nothing    -> 0
                let ss'  = takeSubsts (fromInteger ulen) (mkSubsts unifier)
                when (db > 6) $ do
                    traceM $ "***Found " ++ fmt methName ++ " in " ++ fmt traitName
                    traceM $ "\t traitSub is " ++ fmt traitSub
                    traceM $ "\t methSub  is " ++ fmt methSub                  
                    traceM $ "\t unifier is " ++ fmt (Map.toList unifier)
                    traceM $ "\t of size " ++ fmt (Map.size unifier)                
                return (Just (mh, ss' <> methSub))
       
-- | Look for a static trait implementation in a particular Trait
findItem :: HasCallStack => MethName -> Substs -> Trait -> MirGenerator h s ret (Maybe (TraitImpl, Map Integer Ty, TraitImplItem))
findItem methName traitSub trait = do
  db <- use debugLevel
  col <- use collection
  let isImpl :: TraitImpl -> Maybe (TraitImpl, Map Integer Ty)
      isImpl ti
       | (TraitRef tn ss) <- ti^.tiTraitRef
       , tn == trait^.traitName
       = case matchSubsts traitSub ss of
              Right m  ->
                Just (ti, m)
              Left _e -> Nothing           
       | otherwise = Nothing
       
  case firstJust isImpl (col^.impls) of
    Nothing -> return Nothing
    Just (ti, unifier) -> do
      return $ (ti,unifier,) <$> List.find (\x -> x^.tiiImplements == methName) (ti^.tiItems)

-------------------------------------------------------------------------------------------------------
--
-- | Determine whether a function call can be resolved via dictionary projection
--
-- If so, return the dictionary variable, the rvalue that is the dictionary projection
-- and the method substitutions
--
--
-- 1. find the <potential_traits> that could potentially contain this method 
-- 2. find the trait name <tn> and <fields> of a dictionary type for all potential_traits
-- 3. find the index <idx> of the method in the dictionary
-- 4. find the <trait> in the collection and method type <sig> from the trait implementations
--
-- In findVar:
-- 5. separate substs into those for trait, and those for method 
-- 6. create the <var> for the dictionary make sure that it in scope
-- 7. create the <exp> that projects the appropriate field at <idx>
-- 8. return everything


resolveDictionaryProjection :: HasCallStack => MethName -> Substs -> MirGenerator h s ret (Maybe (Var, Rvalue, FnSig, Substs))
resolveDictionaryProjection nm subst = do
  stm <- use staticTraitMap
  col  <- use collection
  db <- use debugLevel
  vm <- use varMap
  case stm Map.!? nm of
    Nothing -> return Nothing
    Just potential_traits -> do
      let prjs :: [(TraitName, [Field], Int, Trait, FnSig)]  
          prjs = [ (tn, fields, idx, trait, sig)
                 | (tn, Just (Adt _ [Variant _ _ fields _])) <-
                     map (\tn -> (tn,Map.lookup tn (col^.adts))) potential_traits 
                 , idx   <- Maybe.maybeToList (List.findIndex (\(Field fn _ _) -> nm == fn) fields)
                 , trait <- Maybe.maybeToList ((col^.traits) Map.!? tn)
                 , TraitMethod _ sig <-
                     Maybe.maybeToList $ List.find (\tm -> tm^.itemName == nm) (trait^.traitItems)
                 ]

          findVar (tn, fields, idx, trait, sig) = do
             let (Substs tsubst,msubst) = splitAtSubsts (length (trait^.traitParams)) subst
             let var = mkPredVar (TyAdt tn (Substs tsubst))
             if (not (Map.member (var^.varname) vm)) then return Nothing
             else do

               let (Field _ (TyFnPtr ty) fsubst) = fields !! idx
               let ty'  = tySubst (Substs tsubst) ty
               let sig' = specialize sig tsubst
               let exp = Use (Copy (LProjection (LvalueProjection (Local var) (PField idx (TyFnPtr ty')))))

               when (db > 6) $ do
                 traceM $ "***lookupFunction: at dictionary projection for " ++ show (pretty nm)
                 traceM $ "   traitParams are" ++ fmt (trait^.traitParams)
                 traceM $ "   traitPreds are " ++ fmt (trait^.traitPredicates)
                 traceM $ "   tsubst is      " ++ fmt tsubst
                 traceM $ "   msubst is      " ++ fmt msubst
                 traceM $ "   fsubst is      " ++ fmt fsubst
                 traceM $ "   ty is          " ++ fmt ty
                 traceM $ "   ty' is         " ++ fmt ty'
                 traceM $ "   sig' is         " ++ fmt sig'
                 traceM $ "   exp is         " ++ fmt exp

               return $ Just (var, exp, sig', msubst)
               
      firstJustM findVar prjs



-- | make a variable corresponding to a dictionary type
-- NOTE: this could make a trait for Fn/FnMut/FnOnce
mkPredVar :: Ty -> Var
mkPredVar ty@(TyAdt did ss) = Var {
                _varname  = idText did <> Text.pack (fmt ss)
              , _varmut   = Immut
              , _varty    = ty
              , _varscope = "dictionary"
              , _varpos   = "dictionary argument"
              }
mkPredVar ty = error $ "BUG in mkPredVar: must provide Adt type"


-------------------------------------------------------------------------------------------------------
--
-- | Determine whether a function call can be resolved via explicit name bound in the handleMap
--

resolveImpl :: HasCallStack => MethName -> Substs -> MirGenerator h s ret (Maybe MirHandle)
resolveImpl nm tys = do
  hmap <- use handleMap
  case Map.lookup nm hmap of
    Just h@(MirHandle _nm fs fh) -> do
      -- make sure the number of type arguments is consistent with the impl
      -- we don't have to instantiate all of them, but we can't have too many
      if lengthSubsts tys <= length (fs^.fsgenerics) then
        return (Just h)
      else
        return Nothing
    Nothing -> return Nothing



--  LocalWords:  ty ImplementTrait ctx vtable
