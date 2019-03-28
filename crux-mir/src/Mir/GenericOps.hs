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

import Control.Lens((^.))

import Mir.DefId
import Mir.Mir
import Mir.PP(fmt)

import GHC.Generics
import GHC.Stack


--------------------------------------------------------------------------------------

deriving instance GenericOps BaseSize
deriving instance GenericOps FloatKind

deriving instance GenericOps FnSig
deriving instance GenericOps Adt
deriving instance GenericOps VariantDiscr
deriving instance GenericOps CtorKind
deriving instance GenericOps Variant
deriving instance GenericOps Field
deriving instance GenericOps CustomTy
deriving instance GenericOps Mutability

deriving instance GenericOps Collection
deriving instance GenericOps Predicate
deriving instance GenericOps Param
deriving instance GenericOps Fn
deriving instance GenericOps MirBody
deriving instance GenericOps BasicBlock
deriving instance GenericOps BasicBlockData
deriving instance GenericOps Statement

deriving instance GenericOps Rvalue
deriving instance GenericOps AdtAg
deriving instance GenericOps Terminator
deriving instance GenericOps Operand
deriving instance GenericOps Constant
deriving instance GenericOps LvalueProjection
deriving instance GenericOps Lvpelem
deriving instance GenericOps NullOp
deriving instance GenericOps BorrowKind
deriving instance GenericOps UnOp
deriving instance GenericOps BinOp
deriving instance GenericOps CastKind
deriving instance GenericOps Literal
deriving instance GenericOps IntLit
deriving instance GenericOps FloatLit
deriving instance GenericOps ConstVal
deriving instance GenericOps AggregateKind
deriving instance GenericOps CustomAggregate
deriving instance GenericOps Trait
deriving instance GenericOps TraitItem
deriving instance GenericOps TraitRef
deriving instance GenericOps TraitImpl
deriving instance GenericOps TraitImplItem

deriving anyclass instance GenericOps Substs
deriving anyclass instance GenericOps Params
deriving anyclass instance GenericOps Predicates


--------------------------------------------------------------------------------------

--
-- Generic operations
--

-- These operations are defined via GHC.Generics so that they can automatically
-- adapt to changes in the Mir AST.  

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

  -- | number of type params that appear (i.e. largest TyParam + 1)
  numTyParams :: a -> Integer
  default numTyParams ::  (Generic a, GenericOps' (Rep a)) => a -> Integer
  numTyParams x = numTyParams' (from x)

  -- | replace Associated Types
  abstractAssocTys :: AbstractAssocTysInfo -> a -> a 
  default abstractAssocTys ::  (Generic a, GenericOps' (Rep a)) => AbstractAssocTysInfo -> a -> a
  abstractAssocTys s x = to (abstractAssocTys' s (from x))


data AbstractAssocTysInfo = AbstractAssocTysInfo {
     start :: Integer
   , len   :: Integer
   , aMap  :: Map (DefId, Substs) Ty
   }
--------------------------------------------------------------------------------------

class GenericOps' f where
  relocate'      :: f p -> f p
  markCStyle'    :: (Map.Map DefId Adt,Collection) -> f p -> f p
  tySubst'       :: HasCallStack => Substs -> f p -> f p 
  replaceVar'    :: Var -> Var -> f p -> f p
  replaceLvalue' :: Lvalue -> Lvalue -> f p -> f p
  numTyParams'   :: f p -> Integer
  abstractAssocTys' ::  AbstractAssocTysInfo -> f p -> f p
  
--------------------------------------------------------------------------------------  

instance GenericOps' V1 where
  relocate' _x      = error "impossible: this is a void type"
  markCStyle' _ _x  = error "impossible: this is a void type"
  tySubst' _ _      = error "impossible: this is a void type"
  replaceVar' _ _ _ = error "impossible: this is a void type"
  replaceLvalue' _ _ _ = error "impossible: this is a void type"
  numTyParams' _    = error "impossible: this is a void type"
  abstractAssocTys' _  = error "impossible: this is a void type"

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
  abstractAssocTys' s (L1 x) = L1 (abstractAssocTys' s x)
  abstractAssocTys' s (R1 x) = R1 (abstractAssocTys' s x)

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  relocate'       (x :*: y) = relocate'   x     :*: relocate' y
  markCStyle' s   (x :*: y) = markCStyle'   s x :*: markCStyle' s y
  tySubst'    s   (x :*: y) = tySubst'      s x :*: tySubst'    s y
  replaceVar' o n (x :*: y) = replaceVar' o n x :*: replaceVar' o n y
  replaceLvalue' o n (x :*: y) = replaceLvalue' o n x :*: replaceLvalue' o n y
  numTyParams' (x :*: y)    = max (numTyParams' x) (numTyParams' y)
  abstractAssocTys' s (x :*: y) = abstractAssocTys' s x :*: abstractAssocTys' s y

instance (GenericOps c) => GenericOps' (K1 i c) where
  relocate'     (K1 x) = K1 (relocate x)
  markCStyle' s (K1 x) = K1 (markCStyle s x)
  tySubst'    s (K1 x) = K1 (tySubst s x)
  replaceVar' o n (K1 x) = K1 (replaceVar o n x)
  replaceLvalue' o n (K1 x) = K1 (replaceLvalue o n x)  
  numTyParams' (K1 x)  = numTyParams x
  abstractAssocTys'    s (K1 x) = K1 (abstractAssocTys s x)
  
instance (GenericOps' f) => GenericOps' (M1 i t f) where
  relocate'     (M1 x) = M1 (relocate' x)
  markCStyle' s (M1 x) = M1 (markCStyle' s x)
  tySubst'    s (M1 x) = M1 (tySubst' s x)
  replaceVar' o n (M1 x) = M1 (replaceVar' o n x)
  replaceLvalue' o n (M1 x) = M1 (replaceLvalue' o n x)
  numTyParams' (M1 x)  = numTyParams' x
  abstractAssocTys' s (M1 x) = M1 (abstractAssocTys' s x)
  
instance (GenericOps' U1) where
  relocate'      U1 = U1
  markCStyle' _s U1 = U1
  tySubst'    _s U1 = U1
  replaceVar' _ _ U1 = U1
  replaceLvalue' _ _ U1 = U1
  numTyParams' U1 = 0
  abstractAssocTys' _s U1 = U1
--------------------------------------------------------------------------------------

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

    
-- special case for DefIds
instance GenericOps DefId where
  relocate     = relocateDefId 
  markCStyle _   = id
  tySubst    _   = id
  replaceVar _ _ = id
  replaceLvalue _ _ = id
  numTyParams _  = 0

-- special case for Tys
instance GenericOps Ty where

  -- Translate C-style enums to CEnum types
  markCStyle (ads,s) (TyAdt n ps)  | Just adt <- Map.lookup n ads =
   if ps == Substs [] then
      TyCustom (CEnum n (adtIndices adt s))
   else
      error "Cannot have params to C-style enum!"
  markCStyle s ty = to (markCStyle' s (from ty))

  -- Substitute for type variables
  tySubst (Substs substs) (TyParam i)
     | fromInteger i < length substs = substs !! fromInteger i 
     | otherwise    = error $
           "BUG in substitution: Indexing at " ++ show i ++ "  from subst " ++ fmt substs
  tySubst substs ty = to (tySubst' substs (from ty))

  numTyParams (TyParam x) = x + 1
  numTyParams ty = numTyParams' (from ty)



  abstractAssocTys (AbstractAssocTysInfo tk ta _atys) (TyParam i)
    | i < tk    = TyParam i         -- trait param,  leave alone
    | otherwise = TyParam (i + ta)  -- method param, shift over
  abstractAssocTys (AbstractAssocTysInfo _tk _ta atys) ty@(TyProjection d substs)
    -- associated type, replace with new param
    | Just nty <- Map.lookup (d,substs) atys = nty
    | otherwise = error $ fmt ty ++ " with unknown translation"
  abstractAssocTys s ty = to (abstractAssocTys' s (from ty))

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
                      
instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)

instance GenericOps Int     where
   relocate   = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractAssocTys = const id
   
instance GenericOps Integer where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0 
   abstractAssocTys = const id  
   
instance GenericOps Char    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractAssocTys = const id
   
instance GenericOps Bool    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractAssocTys = const id
   
instance GenericOps Text    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   numTyParams _ = 0
   abstractAssocTys = const id
   
instance GenericOps B.ByteString where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id   
   numTyParams _ = 0
   abstractAssocTys = const id
   
instance GenericOps b => GenericOps (Map.Map a b) where
   relocate       = Map.map relocate 
   markCStyle s   = Map.map (markCStyle s)
   tySubst s      = Map.map (tySubst s)
   replaceVar o n = Map.map (replaceVar o n)
   replaceLvalue o n = Map.map (replaceLvalue o n)   
   numTyParams m  = Map.foldr (max . numTyParams) 0 m
   abstractAssocTys = const id
   
replaceList :: GenericOps a => [(Lvalue, Lvalue)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replaceLvalue old new a
