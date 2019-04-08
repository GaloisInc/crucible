{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE OverloadedStrings #-}


{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall -fno-warn-unticked-promoted-constructors #-}

module Mir.GenericOps where

import qualified Data.ByteString as B
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)

import Control.Lens((^.),(&),(%~), makeLenses)

import Mir.DefId
import Mir.Mir
import Mir.PP(fmt)

import GHC.Generics
import GHC.Stack

import Data.Coerce

import Debug.Trace


type ATDict = Map AssocTy Ty
data ATInfo = ATInfo {
     _atStart :: Integer    -- ^ index to start renaming
   , _atNum   :: Integer    -- ^ number of ATs to insert
   , _atDict  :: ATDict     -- ^ mapping for AssocTys
   , _atCol   :: Collection -- ^ collection
   , _atMeths :: Map MethName (FnSig,Trait)
       -- ^ declared types of trait methods, plus params and AssocTys from the trait
   }

makeLenses ''ATInfo

--------------------------------------------------------------------------------------
--
-- Generic operations over MIR AST
--

-- 
-- These syntax-directed operations are defined via GHC.Generics so
-- that they can automatically adapt to changes in the Mir AST.
--
-- 
class GenericOps a where

  -- | Crawl over the AST and rename the module that defIds live in.
  -- We need this because we are loading our own variant of the standard
  -- library, but all of the definitions there will have the wrong name.
  relocate :: a -> a
  default relocate :: (Generic a, GenericOps' (Rep a)) => a -> a
  relocate x = to (relocate' (from x))

  -- | Find all C-style Adts in the AST and convert them to Custom (CEnum _)
  markCStyle :: (Map DefId Adt,Collection) -> a -> a 
  default markCStyle :: (Generic a, GenericOps' (Rep a)) => (Map DefId Adt,Collection) -> a -> a
  markCStyle s x = to (markCStyle' s (from x))

  -- | Type variable substitution. Type variables are represented via indices.
  tySubst :: HasCallStack => Substs -> a -> a 
  default tySubst :: (Generic a, GenericOps' (Rep a), HasCallStack) => Substs -> a -> a
  tySubst s x = to (tySubst' s (from x))

  -- | Renaming for term variables
  replaceVar :: Var -> Var -> a -> a
  default replaceVar :: (Generic a, GenericOps' (Rep a)) => Var -> Var -> a -> a
  replaceVar o n x = to (replaceVar' o n (from x))

  -- | ???
  replaceLvalue :: Lvalue -> Lvalue -> a -> a
  default replaceLvalue :: (Generic a, GenericOps' (Rep a)) => Lvalue -> Lvalue -> a -> a
  replaceLvalue o n x = to (replaceLvalue' o n (from x))

  -- | count number of type params that appear (i.e. returns index of largest TyParam + 1)
  numTyParams :: a -> Integer
  default numTyParams ::  (Generic a, GenericOps' (Rep a)) => a -> Integer
  numTyParams x = numTyParams' (from x)

  -- | replace "TyProjection"s with their associated types
  -- and add additional arguments to type substitutions
  abstractATs :: ATInfo -> a -> a 
  default abstractATs :: (Generic a, GenericOps' (Rep a)) => ATInfo -> a -> a
  abstractATs s x = to (abstractATs' s (from x))

  -- | Update the list of predicates in an AST node
  modifyPreds :: RUPInfo -> a -> a
  default modifyPreds :: (Generic a, GenericOps' (Rep a)) => RUPInfo -> a -> a
  modifyPreds s x = to (modifyPreds' s (from x))

--------------------------------------------------------------------------------------
-- ** abstractATs

{-
   We need this operation to turn associated types into additional type arguments
   in *trait definitions* and in polymorphic methods.

   For example, consider this Rust trait:

   pub trait Index<Idx> where
    Idx: ?Sized, 
   {
    type Output: ?Sized;
    fn index(&self, index: Idx) -> &Self::Output;
   }

   In MIR it will look like this, where Self is "TyParam 0"
   and other parameters follow.

   Trait "Index"
         [TraitType "Output",
          TraitMethod "index" (&0,&1) -> &Output<0,1>]

   This operation converts the Output<0,1> type so that it
   is an additional type parameter to the trait method.

   Trait "Index"
         [TraitType "Output",
          TraitMethod "index" (&0,&1) -> &2]

   Implementations of this trait will then unify this
   parameter just as the others.

   NOTE: associated types must go between the trait parameters and
   the method parameters. So we need to rename any method parameters
   starting at a particular index (start) and shift them over by the
   number of ATs that we add.

-}


-- | Special case for Ty
abstractATsTy :: ATInfo -> Ty -> Ty
abstractATsTy ati (TyParam i)
    | i < (ati^.atStart) = TyParam i          -- trait param,  leave alone
    | otherwise = TyParam (i + (ati^.atNum))  -- method param, shift over
abstractATsTy ati ty@(TyProjection d substs)
    -- associated type, replace with new param
    | Just nty <- Map.lookup (d,substs) (ati^.atDict) = nty
    | otherwise = error $ fmt ty ++ " with unknown translation"
abstractATsTy s ty = to (abstractATs' s (from ty))

-- Add additional args to the substs for traits with atys
abstractATsPredicate :: ATInfo -> Predicate -> Predicate
abstractATsPredicate ati (TraitPredicate tn ss) 
    | Just tr <- (ati^.atCol.traits) Map.!? tn
    = let 
        ats  = map (\(n,ss') -> TyProjection n ss') (tr^.traitAssocTys)
        ss1  = abstractATs ati ss
        ats' = tySubst ss1 ats
      in 
        TraitPredicate tn (ss1 <> Substs (map (abstractATs ati) ats'))
    | otherwise
    = (TraitPredicate tn ss)  -- error $ "BUG: Found trait " ++ fmt tn ++ " with no info in collection."
abstractATsPredicate ati (TraitProjection did ss ty)
    = TraitProjection did (abstractATs ati ss) (abstractATs ati ty)
abstractATsPredicate _ati UnknownPredicate = error "BUG: found UnknownPredicate"

-- What if the function itself has associated types?
-- or, what if the function we are calling is
abstractATsConstVal :: ATInfo -> ConstVal -> ConstVal
abstractATsConstVal ati (ConstFunction defid funsubst)
  | Just (fs,mt) <- fnType ati defid
  = let
       
      
       -- remove any ats from the current substs
       funsubst1 = abstractATs ati funsubst

       -- add ATs from trait (if any) to the appropriate place
       -- in the middle of the funsubst
       funsubst2 :: Substs
       funsubst2 = case mt of
                     Nothing -> funsubst1
                     Just tr ->
                       let tats  = tySubst funsubst1 (tr^.traitAssocTys)
                           j     = length $ tr^.traitParams
                           tats' = lookupATs ati tats
                       in
                         substInsertAt tats' j funsubst1
                         
       -- find any ats for the method instantiate them 
       ats       = tySubst funsubst1 (fs^.fsassoc_tys)
       
       -- replace ats with their definition
       ats'      = lookupATs ati ats

       -- add method ats to the end of the function subst
       hsubst    = funsubst2 <> ats'
    in 
       ConstFunction defid hsubst
         
abstractATsConstVal ati val = to (abstractATs' ati (from val))


lookupATs :: ATInfo -> [AssocTy] -> Substs
lookupATs ati ats =
  Substs $ abstractATs ati (map (\(a,b) -> TyProjection a b) ats)

-- | Find the type of a function 
fnType :: ATInfo -> MethName -> Maybe (FnSig, Maybe Trait)
fnType ati mn 

  -- normal function 
  | Just fn <- (ati^.atCol.functions) Map.!? mn
  = Just (fn^.fsig, Nothing)

  -- trait method
  | Just (s, tr) <- (ati^.atMeths) Map.!? mn
  = Just (s, Just tr)
  
  | otherwise
  = Nothing


-- |  insertAt xs k ys
-- is equivalent to take k ++ xs ++ drop k

insertAt :: [a] -> Int -> [a] -> [a]
insertAt xs 0 ys = xs ++ ys
insertAt xs _n [] = xs
insertAt xs n (y:ys) = y : insertAt xs (n - 1)ys

substInsertAt :: Substs -> Int -> Substs -> Substs
substInsertAt = coerce (insertAt @Ty)

--------------------------------------------------------------------------------------

-- ** markCStyle

-- A CStyle ADT is one that is an enumeration of numeric valued options
-- containing no data
isCStyle :: Adt -> Bool
isCStyle (Adt _ variants) = all isConst variants where
    isConst (Variant _ _ [] ConstKind) = True
    isConst _ = False


-- | For ADTs that are represented as CEnums, we need to find the actual numbers that we
-- use to represent each of the constructors.
adtIndices :: Adt -> Collection -> [Integer]
adtIndices (Adt _aname vars) col = map go vars where
 go (Variant _vname (Explicit did) _fields _knd) =
    case Map.lookup did (_functions col) of
      Just fn ->
        case fn^.fbody.mblocks of
          [ BasicBlock _info (BasicBlockData [Assign _lhs (Use (OpConstant (Constant _ty (Value (ConstInt i))))) _loc] _term) ] ->
            fromIntegerLit i
            
          _ -> error "CEnum should only have one basic block"
          
      Nothing -> error "cannot find CEnum value"
 go (Variant _vname (Relative i) _fields _kind) = toInteger i    --- TODO: check this

markCStyleTy :: (Map DefId Adt,Collection) -> Ty -> Ty
markCStyleTy (ads,s) (TyAdt n ps)  | Just adt <- Map.lookup n ads =
   if ps == Substs [] then
      TyCustom (CEnum n (adtIndices adt s))
   else
      error "Cannot have params to C-style enum!"
markCStyleTy s ty = to (markCStyle' s (from ty))

--------------------------------------------------------------------------------------
-- ** modifyPreds 

--- Annoyingly, we don't use the newtype for the list of predicates
-- So we have to implement this operation in all of the containing types

-- filter function for predicates
type RUPInfo = [Predicate] -> [Predicate]

modifyPreds_FnSig :: RUPInfo -> FnSig -> FnSig
modifyPreds_FnSig f fs = fs & fspredicates %~ f
                            & fsarg_tys    %~ modifyPreds f
                            & fsreturn_ty  %~ modifyPreds f
                            
modifyPreds_Trait :: RUPInfo -> Trait -> Trait
modifyPreds_Trait f fs = fs & traitPredicates %~ f
                            & traitItems      %~ modifyPreds f

modifyPreds_TraitImpl :: RUPInfo -> TraitImpl -> TraitImpl
modifyPreds_TraitImpl f fs = fs & tiPredicates %~ f
                                & tiItems      %~ modifyPreds f
                                & tiTraitRef   %~ modifyPreds f 

modifyPreds_TraitImplItem :: RUPInfo -> TraitImplItem -> TraitImplItem
modifyPreds_TraitImplItem f fs@(TraitImplMethod {}) = fs & tiiPredicates %~ f
                                                         & tiiSignature  %~ modifyPreds f
modifyPreds_TraitImplItem f fs@(TraitImplType {}) = fs & tiiPredicates %~ f
                                                       & tiiType       %~ modifyPreds f
                                                       


--------------------------------------------------------------------------------------

-- ** Overridden instances for Mir AST types

instance GenericOps ConstVal where
  abstractATs = abstractATsConstVal
instance GenericOps Predicate where
  abstractATs = abstractATsPredicate
                                                       
-- special case for DefIds
instance GenericOps DefId where
  relocate          = relocateDefId 
  markCStyle _      = id
  tySubst    _      = id
  replaceVar _ _    = id
  replaceLvalue _ _ = id
  numTyParams _     = 0
  abstractATs _     = id
  modifyPreds _     = id

-- special case for Ty
instance GenericOps Ty where

  -- see above
  markCStyle = markCStyleTy
  abstractATs = abstractATsTy
  
  -- Substitute for type variables
  tySubst (Substs substs) (TyParam i)
     | fromInteger i < length substs = substs !! fromInteger i 
     | otherwise    = error $
           "BUG in substitution: Indexing at " ++ show i ++ "  from subst " ++ fmt substs
  tySubst substs ty = to (tySubst' substs (from ty))

  -- Count ty params
  numTyParams (TyParam x) = x + 1
  numTyParams ty = numTyParams' (from ty)



-- special case for Vars
instance GenericOps Var where
  replaceVar old new v = if _varname v == _varname old then new else v

  replaceLvalue (Local old) (Local new) v = replaceVar old new v
  replaceLvalue _ _ v = v

-- special case for LValue
instance GenericOps Lvalue where
    replaceLvalue old new v = fromMaybe v (repl_lv v)
      where
        repl_lv :: Lvalue -> Maybe Lvalue -- some light unification
        repl_lv v0 =
          case v0 of
            LProjection (LvalueProjection lb k)
              | Just ans <- repl_lv lb -> Just $ LProjection (LvalueProjection ans k)
            Tagged lb _ | Just ans <- repl_lv lb -> Just ans
            _ | v == old -> Just new
            _ -> Nothing

-- ** derived instances for MIR AST types
-- If new types are added to the AST, then new derived instances need to be added here

instance GenericOps BaseSize
instance GenericOps FloatKind
instance GenericOps FnSig where
  modifyPreds = modifyPreds_FnSig
instance GenericOps Adt
instance GenericOps VariantDiscr
instance GenericOps CtorKind
instance GenericOps Variant
instance GenericOps Field
instance GenericOps CustomTy
instance GenericOps Mutability
instance GenericOps Collection
instance GenericOps Param
instance GenericOps Fn
instance GenericOps MirBody
instance GenericOps BasicBlock
instance GenericOps BasicBlockData
instance GenericOps Statement
instance GenericOps Rvalue
instance GenericOps AdtAg
instance GenericOps Terminator
instance GenericOps Operand
instance GenericOps Constant
instance GenericOps LvalueProjection
instance GenericOps Lvpelem
instance GenericOps NullOp
instance GenericOps BorrowKind
instance GenericOps UnOp
instance GenericOps BinOp
instance GenericOps CastKind
instance GenericOps Literal
instance GenericOps IntLit
instance GenericOps FloatLit
instance GenericOps AggregateKind
instance GenericOps CustomAggregate
instance GenericOps Trait where
  modifyPreds = modifyPreds_Trait
instance GenericOps TraitItem
instance GenericOps TraitRef
instance GenericOps TraitImpl where
  modifyPreds = modifyPreds_TraitImpl
instance GenericOps TraitImplItem where
  modifyPreds = modifyPreds_TraitImplItem

-- instances for newtypes
-- we need the deriving strategy 'anyclass' to disambiguate 
-- from generalized newtype deriving
-- either version would work, but GHC doesn't know that and gives a warning
instance GenericOps Substs
instance GenericOps Params
instance GenericOps Predicates

-- *** Instances for Prelude types                 

instance GenericOps Int     where
   relocate   = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const id
   modifyPreds = const id
instance GenericOps Integer where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0 
   abstractATs = const id  
   modifyPreds = const id   
instance GenericOps Char    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const id
   modifyPreds = const id   
instance GenericOps Bool    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const id
   modifyPreds = const id
   
instance GenericOps Text    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractATs = const id
   modifyPreds = const id
   
instance GenericOps B.ByteString where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id   
   numTyParams _ = 0
   abstractATs = const id
   modifyPreds = const id
   
instance GenericOps b => GenericOps (Map.Map a b) where
   relocate          = Map.map relocate 
   markCStyle s      = Map.map (markCStyle s)
   tySubst s         = Map.map (tySubst s)
   replaceVar o n    = Map.map (replaceVar o n)
   replaceLvalue o n = Map.map (replaceLvalue o n)   
   numTyParams m     = Map.foldr (max . numTyParams) 0 m
   abstractATs i     = Map.map (abstractATs i)
   modifyPreds i     = Map.map (modifyPreds i)
   
instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)

   
replaceList :: GenericOps a => [(Lvalue, Lvalue)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replaceLvalue old new a




--------------------------------------------------------------------------------------
-- ** Generic programming plumbing

class GenericOps' f where
  relocate'      :: f p -> f p
  markCStyle'    :: (Map.Map DefId Adt,Collection) -> f p -> f p
  tySubst'       :: HasCallStack => Substs -> f p -> f p 
  replaceVar'    :: Var -> Var -> f p -> f p
  replaceLvalue' :: Lvalue -> Lvalue -> f p -> f p
  numTyParams'   :: f p -> Integer
  abstractATs'   :: ATInfo -> f p -> f p
  modifyPreds'   :: RUPInfo -> f p -> f p
  
instance GenericOps' V1 where
  relocate' _x      = error "impossible: this is a void type"
  markCStyle' _ _x  = error "impossible: this is a void type"
  tySubst' _ _      = error "impossible: this is a void type"
  replaceVar' _ _ _ = error "impossible: this is a void type"
  replaceLvalue' _ _ _ = error "impossible: this is a void type"
  numTyParams' _    = error "impossible: this is a void type"
  abstractATs' _  = error "impossible: this is a void type"
  modifyPreds' _  = error "impossible: this is a void type"

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :+: g) where
  relocate'     (L1 x) = L1 (relocate' x)
  relocate'     (R1 x) = R1 (relocate' x)
  markCStyle' s (L1 x) = L1 (markCStyle' s x)
  markCStyle' s (R1 x) = R1 (markCStyle' s x)
  tySubst'    s (L1 x) = L1 (tySubst' s x)
  tySubst'    s (R1 x) = R1 (tySubst' s x)
  replaceVar' o n (L1 x) = L1 (replaceVar' o n x)
  replaceVar' o n (R1 x) = R1 (replaceVar' o n x)
  replaceLvalue' o n (L1 x) = L1 (replaceLvalue' o n x)
  replaceLvalue' o n (R1 x) = R1 (replaceLvalue' o n x)
  numTyParams' (L1 x) = numTyParams' x
  numTyParams' (R1 x) = numTyParams' x
  abstractATs' s (L1 x) = L1 (abstractATs' s x)
  abstractATs' s (R1 x) = R1 (abstractATs' s x)
  modifyPreds' s (L1 x) = L1 (modifyPreds' s x)
  modifyPreds' s (R1 x) = R1 (modifyPreds' s x)

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  relocate'       (x :*: y) = relocate'   x     :*: relocate' y
  markCStyle' s   (x :*: y) = markCStyle'   s x :*: markCStyle' s y
  tySubst'    s   (x :*: y) = tySubst'      s x :*: tySubst'    s y
  replaceVar' o n (x :*: y) = replaceVar' o n x :*: replaceVar' o n y
  replaceLvalue' o n (x :*: y) = replaceLvalue' o n x :*: replaceLvalue' o n y
  numTyParams' (x :*: y)    = max (numTyParams' x) (numTyParams' y)
  abstractATs' s (x :*: y) = abstractATs' s x :*: abstractATs' s y
  modifyPreds' s (x :*: y) = modifyPreds' s x :*: modifyPreds' s y  

instance (GenericOps c) => GenericOps' (K1 i c) where
  relocate'     (K1 x) = K1 (relocate x)
  markCStyle' s (K1 x) = K1 (markCStyle s x)
  tySubst'    s (K1 x) = K1 (tySubst s x)
  replaceVar' o n (K1 x) = K1 (replaceVar o n x)
  replaceLvalue' o n (K1 x) = K1 (replaceLvalue o n x)  
  numTyParams' (K1 x)  = numTyParams x
  abstractATs'    s (K1 x) = K1 (abstractATs s x)
  modifyPreds'    s (K1 x) = K1 (modifyPreds s x)
  
instance (GenericOps' f) => GenericOps' (M1 i t f) where
  relocate'     (M1 x) = M1 (relocate' x)
  markCStyle' s (M1 x) = M1 (markCStyle' s x)
  tySubst'    s (M1 x) = M1 (tySubst' s x)
  replaceVar' o n (M1 x) = M1 (replaceVar' o n x)
  replaceLvalue' o n (M1 x) = M1 (replaceLvalue' o n x)
  numTyParams' (M1 x)  = numTyParams' x
  abstractATs' s (M1 x) = M1 (abstractATs' s x)
  modifyPreds' s (M1 x) = M1 (modifyPreds' s x)  
  
instance (GenericOps' U1) where
  relocate'      U1 = U1
  markCStyle' _s U1 = U1
  tySubst'    _s U1 = U1
  replaceVar' _ _ U1 = U1
  replaceLvalue' _ _ U1 = U1
  numTyParams' U1 = 0
  abstractATs' _s U1 = U1
  modifyPreds' _s U1 = U1  
