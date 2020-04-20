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
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Data.Vector(Vector)
import qualified Data.Vector as V

import Control.Lens((^.),(&),(%~))

import Mir.DefId
import Mir.Mir
import Mir.PP(fmt)

import GHC.Generics
import GHC.Stack

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

  -- | Type variable substitution. Type variables are represented via indices.
  tySubst :: HasCallStack => Substs -> a -> a 
  default tySubst :: (Generic a, GenericOps' (Rep a), HasCallStack) => Substs -> a -> a
  tySubst s x = to (tySubst' s (from x))

  -- | Replace `TyInterned` with real types by applying a function.  The types
  -- returned by the function are expected to be free of further `TyInterned`,
  -- so this function will not recursively `uninternTys` on them.
  uninternTys :: HasCallStack => (Text -> Ty) -> a -> a
  default uninternTys :: (Generic a, GenericOps' (Rep a), HasCallStack) => (Text -> Ty) -> a -> a
  uninternTys f x = to (uninternTys' f (from x))

  -- | Update the list of predicates in an AST node
  modifyPreds :: RUPInfo -> a -> a
  default modifyPreds :: (Generic a, GenericOps' (Rep a)) => RUPInfo -> a -> a
  modifyPreds s x = to (modifyPreds' s (from x))


--------------------------------------------------------------------------------------

-- | Find the discriminant values used for each variant of an enum.  Some
-- generated `PartialEq` impls use `Rvalue::Discriminant` and compare the
-- result to the constants from the enum definition.
adtIndices :: Adt -> Collection -> [Integer]
adtIndices (Adt _aname _kind vars _ _) col = go 0 vars
  where
    go _ [] = []
    go lastExplicit (v : vs) =
        let discr = getDiscr lastExplicit v
            lastExplicit' = if isExplicit v then discr else lastExplicit
        in discr : go lastExplicit' vs

    getDiscr _ (Variant name (Explicit did) _fields _knd) = case Map.lookup did (_functions col) of
        Just fn -> case fn^.fbody.mblocks of
            [ BasicBlock _info (BasicBlockData [Assign _lhs (Use (OpConstant (Constant _ty (Value (ConstInt i))))) _loc] _term) ] ->
                fromIntegerLit i
            
            _ -> error "enum discriminant constant should only have one basic block"
          
        Nothing -> error $ "cannot find discriminant constant " ++ show did ++
            " for variant " ++ show name
    getDiscr lastExplicit (Variant _vname (Relative i) _fields _kind) =
        lastExplicit + toInteger i

    isExplicit (Variant _ (Explicit _) _ _) = True
    isExplicit _ = False

--------------------------------------------------------------------------------------
-- ** modifyPreds 

--- Annoyingly, we don't use the newtype for the list of predicates
-- So we have to implement this operation in all of the containing types

-- filter function for predicates
type RUPInfo = TraitName -> Bool

filterPreds :: RUPInfo -> [Predicate] -> [Predicate]
filterPreds f =
  filter knownPred where
     knownPred :: Predicate -> Bool
     knownPred (TraitPredicate did _) = f did
     knownPred (TraitProjection {})   = True
     -- TODO: not sure if the auto trait case is right, or what this is used for
     knownPred (AutoTraitPredicate _) = True
     knownPred UnknownPredicate       = False


modifyPreds_FnSig :: RUPInfo -> FnSig -> FnSig
modifyPreds_FnSig f fs = fs & fspredicates %~ filterPreds f
                            & fsarg_tys    %~ modifyPreds f
                            & fsreturn_ty  %~ modifyPreds f
                            
modifyPreds_Trait :: RUPInfo -> Trait -> Trait
modifyPreds_Trait f fs = fs & traitPredicates %~ filterPreds f
                            & traitItems      %~ modifyPreds f
                            & traitSupers     %~ filter f

--------------------------------------------------------------------------------------

-- ** Overridden instances for Mir AST types

instance GenericOps ConstVal where
instance GenericOps Predicate where

-- special case for DefIds
instance GenericOps DefId where
  tySubst    _      = id
  uninternTys _     = id
  modifyPreds _     = id



-- | increment all free variables in the range of the substitution by n
lift :: Int -> Substs -> Substs
lift 0 ss = ss
lift n ss = takeSubsts n (incN 0) <> tySubst (incN n) ss  where


-- | An infinite substitution that increments all type vars by n
incN :: Int -> Substs
incN n = Substs (TyParam . toInteger <$> [n ..])

-- special case for Ty
instance GenericOps Ty where

  -- Substitute for type variables
  tySubst (Substs substs) (TyParam i)
     | Just x <- safeNth (fromInteger i) substs  = x
     | otherwise    = error $
           "BUG in substitution: Indexing at " ++ show i ++ "  from subst " ++ fmt (Substs substs)
  tySubst substs ty = to (tySubst' substs (from ty))

  uninternTys f (TyInterned name) = f name
  uninternTys f ty = to (uninternTys' f (from ty))



-- special case for Vars
instance GenericOps Var where

-- special case for LValue
instance GenericOps Lvalue where

-- ** derived instances for MIR AST types
-- If new types are added to the AST, then new derived instances need to be added here

instance GenericOps BaseSize
instance GenericOps FloatKind
instance GenericOps FnSig where
  modifyPreds = modifyPreds_FnSig
  
  tySubst substs (FnSig args ret params preds atys abi spread) =
      (FnSig (tySubst ss args) (tySubst ss ret) params (tySubst ss preds) (tySubst ss atys) abi spread)
        where ss = lift (length params) substs

  
instance GenericOps Adt
instance GenericOps VariantDiscr
instance GenericOps AdtKind
instance GenericOps CtorKind
instance GenericOps Variant
instance GenericOps Field
instance GenericOps Mutability
instance GenericOps Collection
instance GenericOps Param
instance GenericOps Fn
instance GenericOps Abi
instance GenericOps MirBody
instance GenericOps BasicBlock
instance GenericOps BasicBlockData
instance GenericOps Statement
instance GenericOps Rvalue
instance GenericOps AdtAg
instance GenericOps Terminator
instance GenericOps Operand
instance GenericOps Constant
instance GenericOps PlaceBase
instance GenericOps PlaceElem
instance GenericOps NullOp
instance GenericOps BorrowKind
instance GenericOps UnOp
instance GenericOps BinOp
instance GenericOps VtableItem
instance GenericOps CastKind
instance GenericOps Literal
instance GenericOps IntLit
instance GenericOps FloatLit
instance GenericOps AggregateKind
instance GenericOps Trait where
  modifyPreds = modifyPreds_Trait
instance GenericOps TraitItem
instance GenericOps Promoted
instance GenericOps Static
instance GenericOps Vtable
instance GenericOps Intrinsic
instance GenericOps Instance
instance GenericOps InstanceKind
instance GenericOps NamedTy

-- instances for newtypes
-- we need the deriving strategy 'anyclass' to disambiguate 
-- from generalized newtype deriving
-- either version would work, but GHC doesn't know that and gives a warning
instance GenericOps Substs
instance GenericOps Params
instance GenericOps Predicates

-- *** Instances for Prelude types                 

instance GenericOps Int     where
   tySubst    = const id
   uninternTys = const id
   modifyPreds = const id
instance GenericOps Integer where
   tySubst    = const id
   uninternTys = const id
   modifyPreds = const id   
instance GenericOps Char    where
   tySubst    = const id
   uninternTys = const id
   modifyPreds = const id   
instance GenericOps Bool    where
   tySubst    = const id
   uninternTys = const id
   modifyPreds = const id
   
instance GenericOps Text    where
   tySubst    = const id
   uninternTys = const id
   modifyPreds = const id
   
instance GenericOps B.ByteString where
   tySubst    = const id
   uninternTys = const id
   modifyPreds = const id
   
instance GenericOps b => GenericOps (Map.Map a b) where
   tySubst s         = Map.map (tySubst s)
   uninternTys f     = Map.map (uninternTys f)
   modifyPreds i     = Map.map (modifyPreds i)
   
instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)
instance GenericOps a => GenericOps (Vector a) where
   tySubst s         = V.map (tySubst s)
   uninternTys f     = V.map (uninternTys f)
   modifyPreds i     = V.map (modifyPreds i)
  
   
--------------------------------------------------------------------------------------
-- ** Generic programming plumbing

class GenericOps' f where
  tySubst'       :: Substs -> f p -> f p 
  uninternTys'   :: (Text -> Ty) -> f p -> f p
  modifyPreds'   :: RUPInfo -> f p -> f p
  
instance GenericOps' V1 where
  tySubst' _ _      = error "impossible: this is a void type"
  uninternTys' _  = error "impossible: this is a void type"
  modifyPreds' _  = error "impossible: this is a void type"

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :+: g) where
  tySubst'    s (L1 x) = L1 (tySubst' s x)
  tySubst'    s (R1 x) = R1 (tySubst' s x)
  uninternTys' s (L1 x) = L1 (uninternTys' s x)
  uninternTys' s (R1 x) = R1 (uninternTys' s x)
  modifyPreds' s (L1 x) = L1 (modifyPreds' s x)
  modifyPreds' s (R1 x) = R1 (modifyPreds' s x)

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  tySubst'    s   (x :*: y) = tySubst'      s x :*: tySubst'    s y
  uninternTys' s (x :*: y) = uninternTys' s x :*: uninternTys' s y
  modifyPreds' s (x :*: y) = modifyPreds' s x :*: modifyPreds' s y  

instance (GenericOps c) => GenericOps' (K1 i c) where
  tySubst'    s (K1 x) = K1 (tySubst s x)
  uninternTys'    s (K1 x) = K1 (uninternTys s x)
  modifyPreds'    s (K1 x) = K1 (modifyPreds s x)

instance (GenericOps' f) => GenericOps' (M1 i t f) where
  tySubst'    s (M1 x) = M1 (tySubst' s x)
  uninternTys' s (M1 x) = M1 (uninternTys' s x)
  modifyPreds' s (M1 x) = M1 (modifyPreds' s x)  
  
instance (GenericOps' U1) where
  tySubst'    _s U1 = U1
  uninternTys' _s U1 = U1
  modifyPreds' _s U1 = U1  
