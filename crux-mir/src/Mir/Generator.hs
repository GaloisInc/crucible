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

-- The data structures used during translation
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
import           Data.Text (Text)
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
import           Data.Parameterized.BoolRepr

import qualified Lang.Crucible.FunctionHandle as FH
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Syntax as S



import           Mir.DefId
import           Mir.Mir
import           Mir.MirTy
import           Mir.Intrinsics
import           Mir.GenericOps(ATDict,tySubst,mkSubsts,matchSubsts)
import           Mir.PP

import           Unsafe.Coerce(unsafeCoerce)
import           Debug.Trace
import           GHC.Stack


--------------------------------------------------------------------------------------
-- * Result of translating a collection
--
-- 
data RustModule = RustModule {
         _rmCS    :: CollectionState
       , _rmCFGs  :: Map Text (Core.AnyCFG MIR)
     }


---------------------------------------------------------------------------------

-- | The main data type for values, bundling the term-level
-- type ty along with a crucible expression of type ty
data MirExp s where
    MirExp :: C.TypeRepr ty -> R.Expr MIR s ty -> MirExp s
    

---------------------------------------------------------------------------------

-- * The top-level generator type
-- h state monad token
-- s phantom parameter for CFGs
type MirGenerator h s ret = G.Generator MIR h s FnState ret

--------------------------------------------------------------------------------
-- * Generator state for MIR translation to Crucible
--
-- | Generator state for MIR translation
data FnState (s :: Type)
  = FnState { _varMap     :: !(VarMap s),
              _labelMap   :: !(LabelMap s),                            
              _debugLevel :: !Int,
              _currentFn  :: !Fn,
              _cs         :: !CollectionState,
              _customOps  :: !CustomOpMap,
              _assertFalseOnError :: !Bool              
            }

-- | State about the entire collection used for the translation
data CollectionState 
  = CollectionState {
      _handleMap      :: !HandleMap,
      _staticTraitMap :: !StaticTraitMap,
      _staticMap      :: !(Map DefId StaticVar),
      _collection     :: !Collection
      }


---------------------------------------------------------------------------
-- ** Custom operations

type CustomOpMap = Map ExplodedDefId CustomRHS              

type ExplodedDefId = ([Text], Text, [Text])
data CustomOp      =
    CustomOp (forall h s ret. HasCallStack 
                 => [Ty]       -- ^ argument types
                 -> [MirExp s] -- ^ operand values
                 -> MirGenerator h s ret (MirExp s))
  | CustomMirOp (forall h s ret. HasCallStack
      => [Operand] -> MirGenerator h s ret (MirExp s))
    -- ^ custom operations that dispatch to other functions
    -- i.e. they are essentially the translation of
    -- a function call expression
  | CustomOpExit (forall h s ret.
         [MirExp s]
      -> MirGenerator h s ret Text)
    -- ^ custom operations that don't return
type CustomRHS = Substs -> Maybe CustomOp


---------------------------------------------------------------------------
-- ** Static variables

data StaticVar where
  StaticVar :: C.Closed ty => G.GlobalVar ty -> StaticVar


---------------------------------------------------------------------------
-- *** VarMap

-- | The VarMap maps identifier names to registers (if the id
--   corresponds to a local variable) or an atom (if the id
--   corresponds to a function argument)
type VarMap s = Map Text.Text (Some (VarInfo s))
data VarInfo s tp where
  VarRegister  :: R.Reg s tp -> VarInfo s tp
  VarReference :: R.Reg s (MirReferenceType tp) -> VarInfo s tp
  VarAtom      :: R.Atom s tp -> VarInfo s tp

---------------------------------------------------------------------------
-- *** LabelMap

-- | The LabelMap maps identifiers to labels of their corresponding basicblock
type LabelMap s = Map BasicBlockInfo (R.Label s)

---------------------------------------------------------------------------
-- *** HandleMap

-- | The HandleMap maps mir functions to their corresponding function
-- handle. Function handles include the original method name (for
-- convenience) and original Mir type (for trait resolution).
type HandleMap = Map MethName MirHandle

data MirHandle = forall init ret. 
    MirHandle { _mhName       :: MethName
              , _mhSig        :: FnSig
              -- The type of the function handle can include "free variables"
              , _mhHandle     :: FH.FnHandle init ret
              }

---------------------------------------------------------------------------
-- *** StaticTraitMap


-- | A StaticTraitMap maps trait method names to all traits that contain them
-- (There could be multiple, and will need to use type info to resolve further)
type StaticTraitMap = Map MethName [TraitName]

 

-------------------------------------------------------------------------------------------------------

makeLenses ''FnState
makeLenses ''MirHandle
makeLenses ''CollectionState
makeLenses ''RustModule

$(return [])

-------------------------------------------------------------------------------------------------------

-- ** Operations and instances

instance Semigroup RustModule where
  (RustModule cs1 cm1) <> (RustModule cs2 cm2) = RustModule (cs1 <> cs2) (cm1 <> cm2)
instance Monoid RustModule where
  mempty  = RustModule mempty mempty
  mappend = (<>)

instance Semigroup CollectionState  where
  (CollectionState hm1 stm1 sm1 col1) <> (CollectionState hm2 stm2 sm2 col2) =
      (CollectionState (hm1 <> hm2) (stm1 <> stm2) (sm1 <> sm2) (col1 <> col2))
instance Monoid CollectionState where
  mappend = ((<>))
  mempty  = CollectionState mempty mempty mempty mempty


instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)

instance Show MirHandle where
    show (MirHandle _nm sig c) =
      show c ++ ":" ++ show sig

instance Pretty MirHandle where
    pretty (MirHandle nm sig _c) =
      text (show nm) <> colon <> pretty sig 


varInfoRepr :: VarInfo s tp -> C.TypeRepr tp
varInfoRepr (VarRegister reg0)  = R.typeOfReg reg0
varInfoRepr (VarReference reg0) =
  case R.typeOfReg reg0 of
    MirReferenceRepr tp -> tp
    _ -> error "impossible: varInfoRepr"
varInfoRepr (VarAtom a) = R.typeOfAtom a

mkStaticTraitMap :: Collection -> StaticTraitMap
mkStaticTraitMap col = foldr addTrait Map.empty (col^.traits) where
  addTrait :: Trait -> StaticTraitMap -> StaticTraitMap
  addTrait tr tm = foldr addItem tm (tr^.traitItems) where
    tn = tr^.traitName
    addItem :: TraitItem -> StaticTraitMap -> StaticTraitMap
    addItem tii@(TraitMethod methName _sig) tm =
      Map.insertWith (++) methName [tn] tm
    addItem _ tm = tm


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
  stm <- use (cs . staticTraitMap)
  case (stm Map.!? mn) of
    Just tns -> firstJustM (resolveStaticMethod mn sub) (getTraitName mn : tns)
    Nothing -> resolveStaticMethod mn sub (getTraitName mn)
                          
resolveStaticMethod :: HasCallStack => MethName -> Substs -> TraitName -> MirGenerator h s ret (Maybe (MirHandle, Substs))
resolveStaticMethod methName substs traitName = do
   db <- use debugLevel
   col <- use (cs . collection)
   case (col^.traits) Map.!? traitName of
     Nothing -> return $ Nothing -- BUG: Cannot find trait in collection
     Just trait -> do
       let (traitSub, methSub) = splitAtSubsts (length (trait^.traitParams)) substs
       mimpl <- findItem methName traitSub trait
       case mimpl of
          Nothing -> return $ Nothing  -- OK: there is no impl for this method name & traitsub in this trait
          Just (traitImpl, unifier, traitImplItem) -> do
            hmap <- use (cs.handleMap)
            case hmap Map.!? (traitImplItem^.tiiName) of
              Nothing -> return Nothing -- BUG: impls should all be in the handle map
              Just mh -> do                
                let ulen = case Map.lookupMax unifier of
                                  Just (k,_) -> k + 1
                                  Nothing    -> 0
                let ss'  = takeSubsts (fromInteger ulen) (mkSubsts unifier)
                let mhgens = mh^.mhSig^.fsgenerics
                 
                when (db > 5) $ do
                    traceM $ "***Found " ++ fmt methName ++ " in " ++ fmt traitName
                    traceM $ "\t traitSub is " ++ fmt traitSub
                    traceM $ "\t ss' is      " ++ fmt ss'
                    traceM $ "\t methSub  is " ++ fmt methSub                  
                    traceM $ "\t unifier is  " ++ fmt (Map.toList unifier)
                    traceM $ "\t of size     " ++ fmt (Map.size unifier)
                    traceM $ "\t handle is   " ++ fmt mh
                return (Just (mh, ss' <> methSub))
       
-- | Look for a static trait implementation in a particular Trait
findItem :: HasCallStack => MethName -> Substs -> Trait -> MirGenerator h s ret (Maybe (TraitImpl, Map Integer Ty, TraitImplItem))
findItem methName traitSub trait = do
  db <- use debugLevel
  col <- use (cs.collection)
  let isImpl :: TraitImpl -> Maybe (TraitImpl, Map Integer Ty)
      isImpl ti
       | (TraitRef tn ss) <- ti^.tiTraitRef
       , tn == trait^.traitName
       = (if db > 6 then trace $ "Comparing " ++ fmt traitSub ++ " with " ++ fmt ss else id) $
         case matchSubsts traitSub ss of
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
  stm <- use (cs.staticTraitMap)
  col  <- use (cs.collection)
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

resolveFn :: HasCallStack => MethName -> Substs -> MirGenerator h s ret (Maybe MirHandle)
resolveFn nm tys = do
  hmap <- use (cs.handleMap)
  case Map.lookup nm hmap of
    Just h@(MirHandle _nm fs fh) -> do
      -- make sure the number of type arguments is consistent with the impl
      -- we don't have to instantiate all of them, but we can't have too many
      if lengthSubsts tys <= length (fs^.fsgenerics) then
        return (Just h)
      else
        return Nothing
    Nothing -> return Nothing

---------------------------------------------------------------------------------------------------

{-
-- Can use the (static) type arguments to decide whether to override
memberCustomFunc :: DefId -> Substs -> MirGenerator h s ret Bool
memberCustomFunc defid substs = do
  co <- use customOp
  let edid = (map fst (did_path defid), fst (did_name defid), map fst (did_extra defid)) 
  case Map.lookup edid co of
    Just f  -> return $ Maybe.isJust (f substs)
    Nothing -> return False
-}

resolveCustom :: DefId -> Substs -> MirGenerator h s ret (Maybe CustomOp)
resolveCustom defid substs = do
  let edid = (map fst (did_path defid), fst (did_name defid), map fst (did_extra defid))
  co <- use customOps
  case Map.lookup edid co of
    Just f -> return $ f substs
    Nothing -> return Nothing

---------------------------------------------------------------------------------------------------




--  LocalWords:  ty ImplementTrait ctx vtable idx runtime struct
--  LocalWords:  vtblToStruct
