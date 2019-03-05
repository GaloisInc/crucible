-- |
-- Module           : Lang.Crucible.Substitution
-- Description      : This module includes generic definitions for implementing de Bruijn indices
--                    and parallel substitution in types

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}

module Lang.Crucible.Substitution
  (
     -- * Kind-polymorphic substitutions
    SubstK    
  , SubstVar
  , substVar
  , IdSubst, SuccSubst, ExtendSubst, LiftSubst, TailSubst
  , SubstReprK(..)

  , Liftn
  , liftn
  , MkSubst
  , mkSubst
  , Compose
  , compose

  , Term(..)
  , Instantiate  
  , InstantiateF(..)
  , InstantiateFC(..)
  , InstantiateType(..)

  -- ** Evidence for closedness
  , ClosedK(..)  
  , closedInstantiate
  , closedInstantiateF
  , closedInstantiateFC

  , checkClosedAssignment

  -- ** reexports
  , Dict(..)
  , Peano
  , PeanoView(..)
  , peanoView
  , PeanoRepr(..)
  
  ) where

import           Data.Proxy
import           Data.Kind(Type)
import           Data.Constraint(Dict(..))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import           Data.Parameterized.Peano

import Unsafe.Coerce

-------------------------------------------------------------------------
-------------------------------------------------------------------------
-- * Representation of (parallel) substitutions

-- We can view a substitution as an infinite stream of terms (of type a)
-- where variable i is mapped to the ith term in the list.

-- The usual representation of these substitutions is as
-- functions. But type-level Haskell does not have anonymous
-- functions. It is also too strict to work with infinite lists.
-- Therefore, we use a finite representation derived by
-- defunctionalizing the usual function-based operations.
data SubstK (a :: Type) = 
    IdSubst
     -- ^ the identity substitution, leaves all variables alone
     -- i.e. [ var 0, var 1, var 2, var 3, ... ]
  | SuccSubst
     -- ^ increments every variable by one
     -- i.e. [ var 1, var 2, var 3, var 4, ... ]
  | ExtendSubst a (SubstK a)
     -- ^ add a new mapping to the beginning of the substitution
     -- i.e. if s is [ ty0, ty1 , ty2, ... ]
     -- then ExtendSubst ty s is   [ ty , ty0 , ty1 , ty2, ... ]
  | TailSubst (SubstK a)
     -- ^ remove the first mapping in the substitution
     -- i.e. if s is [ ty0, ty1, ty2 ... ]
     -- then TailSubst s is [ ty1 , ty2, ... ]
  | LiftSubst (SubstK a)
     -- ^ identity for var0, but increment all vars in the range of s
     -- i.e. if s is [ ty0, ty1, ty2, ... ]
     -- then LiftSubst s is [ var 0, lift ty0, lift ty1, lift ty2, ... ]
type IdSubst     = 'IdSubst
type SuccSubst   = 'SuccSubst
type ExtendSubst = 'ExtendSubst
type LiftSubst   = 'LiftSubst
type TailSubst   = 'TailSubst

-- | Apply the substitution to a variable nth
-- This is like looking up the nth entry in the list
type family SubstVar (s :: SubstK k) (n :: Peano) :: k where
  SubstVar ('IdSubst :: SubstK k) n   = MkVar k n
  SubstVar ('SuccSubst :: SubstK k) n = MkVar k (S n)
  SubstVar ('ExtendSubst ty s) ('S m) = SubstVar s m
  SubstVar ('ExtendSubst ty s) 'Z     = ty
  SubstVar (('LiftSubst s) :: SubstK k) Z     = MkVar k Z
  SubstVar (('LiftSubst s) :: SubstK k) (S m) = Instantiate ('SuccSubst :: SubstK k) (SubstVar s m)
  SubstVar ('TailSubst s) x          = SubstVar s (S x)
  
-- | Create a substitution from a Ctx of types
type family MkSubst (c :: Ctx k) :: SubstK k where
  MkSubst EmptyCtx     = IdSubst
  MkSubst (ctx ::> ty) = ExtendSubst ty (MkSubst ctx)

-- | Compose two substitutions together
type family Compose (s1 :: SubstK k) (s2 :: SubstK k) :: SubstK k where
  Compose s1 IdSubst = s1
  Compose s1 SuccSubst = TailSubst s1
  Compose s1 (ExtendSubst ty s2) = ExtendSubst (Instantiate s1 ty) (Compose s1 s2)
  Compose s1 (LiftSubst s2) = ExtendSubst (SubstVar s1 Z) (Compose (TailSubst s1) s2)
  Compose s1 (TailSubst s2) = TailSubst (Compose s1 s2)

-- | Apply the "lift" substitution m-times
type family Liftn (m :: Peano) (s :: SubstK k) :: SubstK k where
  Liftn Z s     = s
  Liftn (S m) s = LiftSubst (Liftn m s)


-------------------------------------------------------------------------------
-- * Instantiation Operation

-- | Type-level, kind-indexed multi-substitution function
-- 
type family Instantiate (subst :: SubstK a) (v :: k) :: k

-- | Class of types that support instantiation (at runtime)
-- 
class InstantiateType k (ty :: Type) where
  instantiate :: SubstReprK k subst -> ty -> Instantiate subst ty

type instance Instantiate subst ((a b) :: Type)
  = Instantiate subst a (Instantiate subst b)
type instance Instantiate subst ((a b) :: k -> Type)
  = Instantiate subst a (Instantiate subst b)

class InstantiateF m (a :: k -> Type) where
  instantiateF :: SubstReprK m subst -> a b -> Instantiate subst (a b)
  instantiateF _ _ = error "instantiateF: must be defined to use polymorphism"
class InstantiateFC m (a :: (k -> Type) -> k -> Type) where
  instantiateFC :: InstantiateF m b => SubstReprK m subst -> a b c
    -> Instantiate subst (a b) (Instantiate subst c)
  instantiateFC _ _ = error "instantiateFC: must be defined to use polymorphism"

instance (InstantiateF m t) => InstantiateType m (t a) where
  instantiate = instantiateF
instance (InstantiateFC m t, InstantiateF m a) => InstantiateF m (t a) where
  instantiateF = instantiateFC


-------------------------------------------------------------------------------
-- * Terms and substitution

-- | A class of (type-level) terms that support substitution
-- The datakinds (k) that are instances of this class must have
-- some data constructor for variables, and the action of the
-- Instantiate operation on this data constructor must be be the
-- 'SubstVar' function (see axiomSubstVar).
class Term (k :: Type) where
   
   -- | Construct a variable from an index
   type MkVar k :: Peano -> k

   axiomSubstVar :: p1 subst -> p2 n ->
         Instantiate subst (MkVar k n) :~: SubstVar subst n
   
    -- | This datakind must have a runtime representation
   type Repr  k :: k -> Type

   varRepr :: PeanoRepr n -> Repr k (MkVar k n)

   instantiateRepr :: SubstReprK k subst -> Repr k t -> Repr k (Instantiate subst t)


-------------------------------------------------------------------------
  
-- Runtime Representation type for SubstKs (singleton)
data SubstReprK k (s :: SubstK k) where
  IdRepr     :: SubstReprK k 'IdSubst
  SuccRepr   :: SubstReprK k 'SuccSubst
  ExtendRepr :: Repr k ty -> SubstReprK k s -> SubstReprK k ('ExtendSubst ty s)
  LiftRepr   :: SubstReprK k s -> SubstReprK k ('LiftSubst s)
  TailRepr   :: SubstReprK k s -> SubstReprK k ('TailSubst s)
  
instance KnownRepr (SubstReprK k) IdSubst where
  knownRepr = IdRepr
instance KnownRepr (SubstReprK k) SuccSubst where
  knownRepr = SuccRepr
instance (KnownRepr (SubstReprK k) s, KnownRepr m ty, Repr k ~ m) => KnownRepr (SubstReprK k) (ExtendSubst ty s) where
  knownRepr = ExtendRepr knownRepr knownRepr
instance KnownRepr (SubstReprK k) s => KnownRepr (SubstReprK k) (LiftSubst s) where
  knownRepr = LiftRepr knownRepr
instance KnownRepr (SubstReprK k) s => KnownRepr (SubstReprK k) (TailSubst s) where
  knownRepr = TailRepr knownRepr

instance (TestEquality (Repr k)) => TestEquality (SubstReprK k) where
  testEquality IdRepr IdRepr
    = return Refl
  testEquality SuccRepr SuccRepr
    = return Refl
  testEquality (ExtendRepr t1 s1) (ExtendRepr t2 s2)
    | Just Refl <- testEquality t1 t2
    , Just Refl <- testEquality s1 s2
    = return Refl
  testEquality (LiftRepr s1) (LiftRepr s2)
    | Just Refl <- testEquality s1 s2
    = return Refl
  testEquality (TailRepr s1)(TailRepr s2)
    | Just Refl <- testEquality s1 s2
    = return Refl
  testEquality _ _ = Nothing

-------------------------------------------------------------------------

substVar :: forall k s n. (Term k) => SubstReprK k s -> PeanoRepr n -> Repr k (SubstVar s n)
substVar IdRepr n   = varRepr n
substVar SuccRepr n = varRepr (succP n)
substVar (ExtendRepr ty s) n = case peanoView n of
      ZRepr     -> ty
      (SRepr m) -> substVar s m
substVar (LiftRepr (s0 :: SubstReprK k s0)) n = case peanoView n of
      ZRepr     -> varRepr zeroP
      (SRepr (m :: PeanoRepr m)) ->
           let
             inst :: Repr k (Instantiate (SuccSubst :: SubstK k) (SubstVar s0 m))
             inst = instantiateRepr (SuccRepr :: SubstReprK k 'SuccSubst) (substVar s0 m)
           in
             inst
substVar (TailRepr s) n = substVar s (succP n)

mkSubst :: Ctx.Assignment (Repr k) ctx -> SubstReprK k (MkSubst ctx)
mkSubst ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> IdRepr
    Ctx.AssignExtend ctx0 ty -> ExtendRepr ty (mkSubst ctx0)

compose :: Term k => SubstReprK k ctx1 -> SubstReprK k ctx2 -> SubstReprK k (Compose ctx1 ctx2)
compose s1 IdRepr = s1
compose s1 SuccRepr = TailRepr s1
compose s1 (ExtendRepr ty s2) =
  ExtendRepr (instantiateRepr s1 ty) (compose s1 s2)
compose s1 (LiftRepr s2) =
  ExtendRepr (substVar s1 zeroP) (compose (TailRepr s1) s2)
compose s1 (TailRepr s2) =
  TailRepr (compose s1 s2)


liftn :: PeanoRepr m -> SubstReprK k s -> SubstReprK k (Liftn m s)
liftn n s = case peanoView n of
  ZRepr -> s
  (SRepr m) -> LiftRepr (liftn m s)

-------------------------------------------------------------------------

-- | Types that do not contain any free type variables are Closed. If they are
-- closed then we know that instantiation and lifting does nothing.
-- The two proxies (p1 and p2) allows us to specify the arguments
-- without using a type application.

class ClosedK m (t :: k) where
  closed :: p1 t -> p2 (subst :: SubstK m) -> Instantiate subst t :~: t
  closed = error "closed: must define closed to use instantiation"


-- Types that are statically known to be closed can benefit from the following
-- default definitions 

closedInstantiate :: forall k ty subst. ClosedK k ty => SubstReprK k subst -> ty -> Instantiate subst ty
closedInstantiate subst | Refl <- closed (Proxy :: Proxy ty) subst = id

closedInstantiateF :: forall k t0 a subst. (ClosedK k t0, ClosedK k a)
  =>  SubstReprK k subst -> t0 a -> (Instantiate subst t0) (Instantiate subst a)
closedInstantiateF s | Refl <- closed (Proxy :: Proxy t0) s, Refl <- closed (Proxy :: Proxy a) s = id
  
closedInstantiateFC :: forall k t0 a b subst. (ClosedK k t0, ClosedK k a, ClosedK k b, InstantiateF k a)
  =>  SubstReprK k subst -> t0 a b
  -> (Instantiate subst t0) (Instantiate subst a) (Instantiate subst b)
closedInstantiateFC s |
    Refl <- closed (Proxy :: Proxy t0) s,
    Refl <- closed (Proxy :: Proxy a) s,
    Refl <- closed (Proxy :: Proxy b) s = id




-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
-- () :: Type

type instance Instantiate subst () = ()
instance ClosedK m () where closed _ _ = Refl

-------------------------------------------------------------------------------
-- Ctx.Assignment :: (k -> Type) -> Ctx k -> Type

type instance Instantiate subst Ctx.Assignment = Ctx.Assignment

type instance Instantiate subst EmptyCtx = EmptyCtx
type instance Instantiate subst (ctx ::> ty) = Instantiate subst ctx ::> Instantiate subst ty


instance InstantiateF m f => InstantiateF m (Ctx.Assignment f) where
  instantiateF _subst Ctx.Empty = Ctx.Empty 
  instantiateF subst (ctx Ctx.:> ty) = instantiate subst ctx Ctx.:> instantiate subst ty

instance (ClosedK m EmptyCtx) where
  closed _ _ = Refl  

instance (ClosedK m ty, ClosedK m ctx) => ClosedK m (ctx ::> ty)
 where
    closed (_ :: p1 (ctx ::> ty))  p2 
       | Refl <- closed (Proxy :: Proxy ctx) p2
       , Refl <- closed (Proxy :: Proxy ty)  p2
       = Refl


-- | Attempt to construct evidence that a context is closed, assuming
-- the invariant that type variables are well-scoped.
checkClosedAssignment :: (forall t. Repr k t -> Maybe (Dict (ClosedK m t)))
               -> Ctx.Assignment (Repr k) (ts :: Ctx k)  -> Maybe (Dict (ClosedK m ts))
checkClosedAssignment cc ctx =
  case Ctx.viewAssign ctx of
    Ctx.AssignEmpty -> Just Dict
    Ctx.AssignExtend ts t ->
      do Dict <- checkClosedAssignment cc ts
         Dict <- cc t
         Just Dict

-------------------------------------------------------------------------------
-- Ctx.Index :: Ctx k -> k -> Type
         
-- Ctx.Index is just a number
type instance Instantiate subst Ctx.Index = Ctx.Index 
instance InstantiateF m (Ctx.Index ctx) where
  instantiateF _subst = unsafeCoerce

----------------------------------------------------------------------------
--  LocalWords:  assumeClosed checkClosed checkClosedCtx closedness         
