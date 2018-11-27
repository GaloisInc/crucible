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
module Lang.Crucible.FunctionHandle
  ( -- * Function handle
    FnHandle
  , handleID
  , handleName
  , handleArgTypes
  , handleReturnType
  , handleType
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
import           Data.Ord (comparing)

import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce.Unsafe

import           What4.FunctionName
import           What4.Utils.MonadST

import           Lang.Crucible.Types

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
