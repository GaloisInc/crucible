{-
Module           : Lang.Crucible.FunctionHandle
Copyright        : (c) Galois, Inc 2014-2016
Maintainer       : Joe Hendrix <jhendrix@galois.com>
License          : BSD3

This provides handles to functions, which provides a unique
identifier of a function at runtime.  Function handles can be thought of
as function pointers, but there are no operations to manipulate them.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Lang.Crucible.FunctionHandle
  ( -- * Function handle
    FnHandle
  , FunctionName
  , handleID
  , handleName
  , handleArgTypes
  , handleReturnType
  , handleType
  , HandleExpr(..)
  , handleExprType
  , handleExprName
  , instantiatePolyHandleExpr
  , SomeHandle(..)
    -- * Allocate handle.
  , HandleAllocator
  , haCounter
  , newHandleAllocator
  , withHandleAllocator
  , mkHandle
  , mkHandle'
    -- * FnHandleMap
  , FnHandleMap
  , emptyHandleMap
  , insertHandleMap
  , lookupHandleMap
    -- * Reference cells
  , RefCell
  , freshRefCell
  , refType
  ) where

import           Control.Monad.ST
import           Data.Hashable
import           Data.Kind
import qualified Data.Maybe as Maybe
import           Data.Ord (comparing)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce.Unsafe

import           What4.FunctionName
import           What4.Utils.MonadST

import           Lang.Crucible.Types

import           Unsafe.Coerce(unsafeCoerce)

------------------------------------------------------------------------
-- FunctionHandle

-- | A handle uniquely identifies a function.  The signature indicates the
--   expected argument types and the return type of the function.
data FnHandle (args :: Ctx CrucibleType) (ret :: CrucibleType)

   = H { handleID         :: !(Nonce (args ::> ret))
         -- ^ A unique identifier for the function.
       , handleName       :: !FunctionName
         -- ^ The name of the function (not necessarily unique)
       , handleArgTypes   :: !(CtxRepr args)
         -- ^ The arguments types for the function
       , handleReturnType :: !(TypeRepr ret)
         -- ^ The return type of the function.
       }

instance Eq (FnHandle args ret) where
  h1 == h2 = handleID h1 == handleID h2

instance Ord (FnHandle args ret) where
  compare h1 h2 = comparing handleID h1 h2

instance Show (FnHandle args ret) where
  show h = show (handleName h)

instance Hashable (FnHandle args ret) where
  hashWithSalt s h = hashWithSalt s (handleID h)

-- | Return type of handle.
handleType :: FnHandle args ret -> TypeRepr (FunctionHandleType args ret)
handleType h = FunctionHandleRepr (handleArgTypes h) (handleReturnType h)


-- Polymorphism note: FnHandles may be parametrically polymorphic
-- (i.e. using an erasure interpretation of polymorphism)
-- However, as they are concrete values, they cannot reference type variables
-- bound in outer scopes. Instead, they implicitly bind all type variables
-- appearing in their argument and return types. 

-- For example, suppose we have a function of type
--    map :: (a -> b) -> t a -> t b
-- the type of the function handle for map generalizes over the type
-- variables a and b. However, in a CFG for map, a register may contain a
-- higher-order argument of type (a -> b).  However, this CFG *must* be
-- instantiated with types for a and b, before we actually put a FnHandle
-- argument in that register.  


------------------------------------------------------------------------
-- Polymorphism and function handles
-- 
-- Handle expressions are function handles that have a sequence of
-- instantiations applied to them.
-- They may or may not be polymorphic

data HandleExpr (ct :: CrucibleType) where
  MonoFnHandle ::
      FnHandle a r ->
      HandleExpr (FunctionHandleType a r)

  PolyFnHandle ::
      NatRepr k ->
      FnHandle a r -> 
      HandleExpr (PolyFnType k a r)
    
  SubstitutedFnHandle ::
  -- NOTE: these instantiations stack
       HandleExpr ty
    -> NatRepr n -> CtxRepr subst 
    -> HandleExpr (Instantiate n subst ty)

-- Return the run time version of the type of the handle expression
handleExprType :: HandleExpr ty -> TypeRepr ty
handleExprType (MonoFnHandle h) = handleType h
handleExprType (PolyFnHandle k h) = PolyFnRepr k (handleArgTypes h) (handleReturnType h)
handleExprType (SubstitutedFnHandle he n subst) =
  instantiate n subst (handleExprType he)

handleExprName :: HandleExpr ty -> FunctionName
handleExprName (MonoFnHandle h)   = handleName h
handleExprName (PolyFnHandle _k h) = handleName h
handleExprName (SubstitutedFnHandle he _ _) = handleExprName he

instance TestEquality HandleExpr where
  testEquality (MonoFnHandle h1) (MonoFnHandle h2) = do
    Refl <- testEquality (handleType h1) (handleType h2) 
    if h1 == h2 then Just Refl else Nothing
  testEquality (PolyFnHandle k1 h1) (PolyFnHandle k2 h2) = do
    Refl <- testEquality k1 k2 
    Refl <- testEquality (handleType h1) (handleType h2) 
    if h1 == h2 then Just Refl else Nothing
  testEquality (SubstitutedFnHandle h1 n1 s1) (SubstitutedFnHandle h2 n2 s2) = do
    Refl <- testEquality h1 h2
    Refl <- testEquality n1 n2
    Refl <- testEquality s1 s2
    return Refl
  testEquality _ _ = Nothing

instance OrdF HandleExpr where
  compareF (MonoFnHandle h1) (MonoFnHandle h2) = do
    case compareF (handleType h1) (handleType h2) of
      EQF -> case compare h1 h2 of
               LT -> LTF
               EQ -> EQF
               GT -> GTF
      x   -> x
  compareF (MonoFnHandle _) _ = LTF      
  compareF (PolyFnHandle k1 h1) (PolyFnHandle k2 h2) =
    case compareF k1 k2 of
      EQF ->  case compareF (handleType h1) (handleType h2) of
                 EQF -> case compare h1 h2 of
                         LT -> LTF
                         EQ -> EQF
                         GT -> GTF
                 GTF -> GTF
                 LTF -> LTF
      GTF   -> GTF
      LTF   -> LTF
  compareF (PolyFnHandle _ _) _ = LTF
  compareF (SubstitutedFnHandle he1 n1 s1) (SubstitutedFnHandle he2 n2 s2) =
    case compareF he1 he2 of
      EQF -> case compareF n1 n2 ofxz
               EQF -> case compareF s1 s2 of
                        EQF -> EQF
                        LTF -> LTF
                        GTF -> GTF
               LTF -> LTF
               GTF -> GTF
      LTF -> LTF
      GTF -> GTF
  compareF (SubstitutedFnHandle _ _ _) _ = GTF
           
instance Eq (HandleExpr ty) where
  h1 == h2 = Maybe.isJust (testEquality h1 h2)

instance Ord (HandleExpr ty) where
  compare h1 h2 = toOrdering (compareF h1 h2)

instance Show (HandleExpr ty) where
  show (MonoFnHandle h) = show (handleName h)
  show (PolyFnHandle _k h) = show (handleName h)
  show (SubstitutedFnHandle he n subst) = show he ++ "@" ++ show n ++ show subst

-- If we get a PolyFnType from instantiation, we started with one
data Axiom k a r n subst ty = forall a' r' p1 p2.
  (ty ~ PolyFnType k a' r',
    Instantiate (n + k) (Lift 0 k subst) a' ~ a,
    Instantiate (n + k) (Lift 0 k subst) r' ~ r)  => Axiom (p1 a') (p2 r')

axiom :: forall k a r n subst ty.
         (PolyFnType k a r ~ Instantiate n subst ty) => Axiom k a r n subst ty
axiom = unsafeCoerce Axiom


axiom2 :: forall k1 n subst targs k (a' :: k1).
  (Instantiate n (Instantiate 0 targs subst) (Instantiate 0 targs a') :~:
   Instantiate 0 targs (Instantiate (n+k) (Lift 0 k subst) a'))
axiom2 = unsafeCoerce Refl

instantiatePolyHandleExpr :: forall k a r targs.
  HandleExpr (PolyFnType k a r)
  -> CtxRepr targs
  -> HandleExpr (FunctionHandleType (Instantiate 0 targs a) (Instantiate 0 targs r))
instantiatePolyHandleExpr (PolyFnHandle _k h) targs =
  SubstitutedFnHandle (MonoFnHandle h) (knownRepr :: NatRepr 0) targs

-- PolyFnType k a r ~ Instantiate n subst ty
-- From axiom:
--     ty ~ PolyFnType k a' r'
--     Instantiate (n + k) (Lift 0 k subst) a' ~ a,
--     Instantiate (n + k) (Lift 0 k subst) r' ~ r
--  i.e.
--    Instantiate n subst (PolyFnType k a' r') ~
--      PolyFnType k (Instantiate (n + k) (Lift 0 k subst a'))
--                   (Instantiate (n + k) (Lift 0 k subst a'))
--  wtp
--    Instantiate 0 tyargs (Instantiate (n+k) (Lift 0 k subst a')) ~
--       
--  Inst n (Inst 0 targs s) (Inst 0 targs ty) ~
--    Inst 0 targs (Inst n s ty)
instantiatePolyHandleExpr
  (SubstitutedFnHandle (he :: HandleExpr ty) (n  :: NatRepr n) (subst :: CtxRepr subst)) targs 
  | Axiom (_x :: p1 a') (_y :: p2 r') <- axiom @k @a @r @n @subst @ty
  ,  Refl <- axiom2 @_ @n @subst @targs @k @a'
  ,  Refl <- axiom2 @_ @n @subst @targs @k @r'
--    Refl  <- composeInstantiateAxiom @0 @targs @(n+k) @(Lift 0 k subst)
--             @(FunctionHandleType a' r')
  =  let
       _he1 :: HandleExpr (PolyFnType k a' r')
       _he1 = he
       _pf1 :: a :~: Instantiate (n+k) (Lift 0 k subst) a'
       _pf1 = Refl
       _pf2 :: r :~: Instantiate (n+k) (Lift 0 k subst) r'
       _pf2 = Refl

       -- we have an instantiation to apply to the polymorphic function
       -- as well as a substitution for the free variables in the polymorphic
       -- function
       -- NOTE: the instantiation should not apply to any free variables in the
       --   substitution --- those should have been lifted away when the
       --   subst was applied to the Polymorphic function
       -- OTOH, when we 
       he' :: HandleExpr (FunctionHandleType (Instantiate 0 targs a')
                                            (Instantiate 0 targs r'))
       he' = instantiatePolyHandleExpr he targs

       subst' :: CtxRepr (Instantiate 0 targs subst)
       subst' = instantiate (knownRepr :: NatRepr 0) targs subst


       _she :: HandleExpr
                        (FunctionHandleType
                           (Instantiate
                              n (Instantiate 0 targs subst)
                                (Instantiate 0 targs a'))
                           (Instantiate
                              n
                              (Instantiate 0 targs subst)
                              (Instantiate 0 targs r')))

       _she = SubstitutedFnHandle he' n subst'
     in
      -- WANT
      (undefined ::
          HandleExpr (FunctionHandleType
                       (Instantiate 0 targs (Instantiate (n+k) (Lift 0 k subst) a'))
                       (Instantiate 0 targs (Instantiate (n+k) (Lift 0 k subst) r'))))


------------------------------------------------------------------------
-- SomeHandle

-- | A function handle is a reference to a function in a given
-- run of the simulator.  It has a set of expected arguments and return type.
data SomeHandle where
   SomeHandle :: !(FnHandle args ret) -> SomeHandle

instance Eq SomeHandle where
  SomeHandle x == SomeHandle y = isJust (testEquality (handleID x) (handleID y))

instance Hashable SomeHandle where
  hashWithSalt s (SomeHandle x) = hashWithSalt s (handleID x)

instance Show SomeHandle where
  show (SomeHandle h) = show (handleName h)


------------------------------------------------------------------------
-- HandleAllocator

-- | Used to allocate function handles.
newtype HandleAllocator s
   = HA { haCounter :: NonceGenerator s
        }

-- | Create a new handle allocator.
newHandleAllocator :: MonadST s m => m (HandleAllocator s)
newHandleAllocator = do
  HA <$> liftST newNonceGenerator

-- | Create a new handle allocator and run the given computation.
withHandleAllocator :: MonadST s m => (HandleAllocator s -> m a) -> m a
withHandleAllocator k = newHandleAllocator >>= k

-- | Allocate a new function handle with requested 'args' and 'ret' types
mkHandle :: (KnownCtx TypeRepr args, KnownRepr TypeRepr ret)
         => HandleAllocator s
         -> FunctionName
         -> ST s (FnHandle args ret)
mkHandle a nm = mkHandle' a nm knownRepr knownRepr

-- | Allocate a new function handle.
mkHandle' :: HandleAllocator s
          -> FunctionName
          -> Ctx.Assignment TypeRepr args
          -> TypeRepr ret
          -> ST s (FnHandle args ret)
mkHandle' a nm args ret = do
  i <- freshNonce (haCounter a)
  return $! H { handleID   = i
              , handleName = nm
              , handleArgTypes   = args
              , handleReturnType = ret
              }

------------------------------------------------------------------------
-- Reference cells

data RefCell (tp :: CrucibleType)
   = RefCell (TypeRepr tp) (Nonce tp)

refType :: RefCell tp -> TypeRepr tp
refType (RefCell tpr _) = tpr

freshRefCell :: HandleAllocator s
             -> TypeRepr tp
             -> ST s (RefCell tp)
freshRefCell ha tpr =
  RefCell tpr <$> freshNonce (haCounter ha)

instance Show (RefCell tp) where
  show (RefCell _ n) = show n

instance ShowF RefCell where

instance TestEquality RefCell where
  testEquality (RefCell _ x) (RefCell _ y) =
    case testEquality x y of
      Just Refl -> Just Refl
      Nothing   -> Nothing

instance OrdF RefCell where
  compareF (RefCell _tx x) (RefCell _ty y) =
    case compareF x y of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

instance Eq (RefCell tp) where
  x == y = isJust (testEquality x y)

instance Ord (RefCell tp) where
  compare x y = toOrdering (compareF x y)

------------------------------------------------------------------------
-- FnHandleMap

data HandleElt (f :: Ctx CrucibleType -> CrucibleType -> Type) ctx where
  HandleElt :: f args ret -> HandleElt f (args::>ret)

newtype FnHandleMap f = FnHandleMap (MapF Nonce (HandleElt f))

emptyHandleMap :: FnHandleMap f
emptyHandleMap = FnHandleMap MapF.empty

insertHandleMap :: FnHandle args ret
                -> f args ret
                -> FnHandleMap f
                -> FnHandleMap f
insertHandleMap hdl x (FnHandleMap m) =
    FnHandleMap (MapF.insert (handleID hdl) (HandleElt x) m)

lookupHandleMap :: FnHandle args ret
                -> FnHandleMap f
                -> Maybe (f args ret)
lookupHandleMap hdl (FnHandleMap m) =
  case MapF.lookup (handleID hdl) m of
     Just (HandleElt x) -> Just x
     Nothing -> Nothing
