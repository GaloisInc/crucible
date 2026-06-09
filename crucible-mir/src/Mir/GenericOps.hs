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

module Mir.GenericOps where

import qualified Data.ByteString as B
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Vector(Vector)
import qualified Data.Vector as V
import Data.Word (Word64)

import Mir.DefId
import Mir.Mir

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

  -- | Replace `TyInterned` with real types by applying a function.  The types
  -- returned by the function are expected to be free of further `TyInterned`,
  -- so this function will not recursively `uninternTys` on them.
  uninternTys :: HasCallStack => (Text -> Ty) -> a -> a
  default uninternTys :: (Generic a, GenericOps' (Rep a), HasCallStack) => (Text -> Ty) -> a -> a
  uninternTys f x = to (uninternTys' f (from x))


--------------------------------------------------------------------------------------

-- ** Overridden instances for Mir AST types

instance GenericOps ConstVal where

-- special case for DefIds
instance GenericOps DefId where
  uninternTys _     = id


-- special case for Ty
instance GenericOps Ty where

  uninternTys f (TyInterned name) = f name
  uninternTys f ty = to (uninternTys' f (from ty))

instance GenericOps CoroutineArgs where


-- special case for Vars
instance GenericOps Var where

-- special case for LValue
instance GenericOps Lvalue where

-- ** derived instances for MIR AST types
-- If new types are added to the AST, then new derived instances need to be added here

instance GenericOps BaseSize
instance GenericOps FloatKind
instance GenericOps FnSig
instance GenericOps Adt
instance GenericOps AdtKind
instance GenericOps CtorKind
instance GenericOps Variant
instance GenericOps Field
instance GenericOps Mutability
instance GenericOps Collection
instance GenericOps Fn
instance GenericOps Abi
instance GenericOps RustCallBodyInfo
instance GenericOps MirBody
instance GenericOps BasicBlock
instance GenericOps BasicBlockData
instance GenericOps Statement
instance GenericOps StatementKind
instance GenericOps Rvalue
instance GenericOps AdtAg
instance GenericOps Terminator
instance GenericOps TerminatorKind
instance GenericOps Operand
instance GenericOps Constant
instance GenericOps PlaceElem
instance GenericOps BorrowKind
instance GenericOps UnOp
instance GenericOps BinOp
instance GenericOps VtableItem
instance GenericOps CastKind
instance GenericOps IntLit
instance GenericOps FloatLit
instance GenericOps AggregateKind
instance GenericOps Trait
instance GenericOps TraitItem
instance GenericOps Static
instance GenericOps Vtable
instance GenericOps Intrinsic
instance GenericOps Instance
instance GenericOps InstanceKind
instance GenericOps NamedTy
instance GenericOps Layout
instance GenericOps LangItem
instance GenericOps NonDivergingIntrinsic
instance GenericOps TyInfo

-- instances for newtypes
-- we need the deriving strategy 'anyclass' to disambiguate
-- from generalized newtype deriving
-- either version would work, but GHC doesn't know that and gives a warning
instance GenericOps Substs

-- *** Instances for Prelude types

instance GenericOps Int     where
   uninternTys = const id
instance GenericOps Integer where
   uninternTys = const id
instance GenericOps Char    where
   uninternTys = const id
instance GenericOps Bool    where
   uninternTys = const id
instance GenericOps Word    where
   uninternTys = const id
instance GenericOps Word64  where
   uninternTys = const id

instance GenericOps Text    where
   uninternTys = const id

instance GenericOps B.ByteString where
   uninternTys = const id

instance GenericOps b => GenericOps (Map.Map a b) where
   uninternTys f     = Map.map (uninternTys f)

instance GenericOps (Set.Set a) where
   uninternTys = const id

instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)
instance GenericOps a => GenericOps (Vector a) where
   uninternTys f     = V.map (uninternTys f)


--------------------------------------------------------------------------------------
-- ** Generic programming plumbing

class GenericOps' f where
  uninternTys'   :: (Text -> Ty) -> f p -> f p

instance GenericOps' V1 where
  uninternTys' _  = error "impossible: this is a void type"

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :+: g) where
  uninternTys' s (L1 x) = L1 (uninternTys' s x)
  uninternTys' s (R1 x) = R1 (uninternTys' s x)

instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  uninternTys' s (x :*: y) = uninternTys' s x :*: uninternTys' s y

instance (GenericOps c) => GenericOps' (K1 i c) where
  uninternTys'    s (K1 x) = K1 (uninternTys s x)

instance (GenericOps' f) => GenericOps' (M1 i t f) where
  uninternTys' s (M1 x) = M1 (uninternTys' s x)

instance (GenericOps' U1) where
  uninternTys' _s U1 = U1
