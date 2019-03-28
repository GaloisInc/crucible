{- |
Module           : Mir.Mir
Description      : Type definitions and serialization functions for Mir
License          : BSD3
-}


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

{-# LANGUAGE OverloadedStrings #-}


{-# LANGUAGE DeriveGeneric, DeriveAnyClass, DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts, TypeOperators #-}

{-# OPTIONS_GHC -Wincomplete-patterns -Wall -fno-warn-unticked-promoted-constructors #-}

module Mir.Mir where

import qualified Data.ByteString as B
import qualified Data.Map.Strict as Map
import Data.Text (Text)

import Data.Semigroup

import Control.Lens(makeLenses,(^.), Simple, Lens, lens)




import GHC.Generics 
import GHC.Stack

import Mir.DefId

-- NOTE: below, all unwinding calls can be ignored
--
--

-- SCW:
-- High-level description of MIR: https://github.com/rust-lang/rfcs/blob/master/text/1211-mir.md
-- documentation of rustc data structures
--   https://doc.rust-lang.org/nightly/nightly-rustc/rustc/mir/index.html
-- Source code:
--   https://github.com/rust-lang/rust/blob/master/src/librustc/mir/mod.rs

data BaseSize =
    USize
      | B8
      | B16
      | B32
      | B64
      | B128
      deriving (Eq, Ord, Show, Generic)

data FloatKind
  = F32
  | F64
  deriving (Eq, Ord, Show, Generic)

-- | Type parameters
newtype Substs = Substs [Ty]
  deriving (Eq, Ord, Show, Generic)
--  deriving anyclass (GenericOps)
  deriving newtype (Semigroup, Monoid)

-- | Associated types
--   The projection of an associated type
type AssocTy = (DefId, Substs)
-- TODO: make this a newtype
--newtype AssocTy = AssocTy (DefId, Substs)
--  deriving (Eq, Ord, Show, Generic)
--  deriving anyclass (GenericOps)


data Ty =
        TyBool               -- The primitive boolean type. Written as bool.
      | TyChar
      | TyInt BaseSize
      | TyUint BaseSize
      | TyTuple [Ty]         -- A tuple type. For example, (i32, bool)
      | TySlice Ty
      | TyArray Ty Int
      | TyRef Ty Mutability  -- Written &'a mut T or &'a T
      | TyAdt DefId Substs 
      | TyUnsupported
      | TyCustom CustomTy
      | TyParam Integer
      | TyFnDef DefId Substs
      | TyClosure DefId Substs
      | TyStr
      | TyFnPtr FnSig             -- written as fn() -> i32
      | TyDynamic DefId
      | TyRawPtr Ty Mutability    -- Written as *mut T or *const T
      | TyFloat FloatKind
      | TyDowncast Ty Integer     -- result type of downcasting an ADT. Ty must be an ADT type
      | TyProjection DefId Substs -- The projection of an associated type. For example, <T as Trait<..>>::N.
      | TyLifetime
      deriving (Eq, Ord, Show, Generic)

data FnSig = FnSig [Ty] Ty 
    deriving (Eq, Ord, Show, Generic)

data Adt = Adt {_adtname :: DefId, _adtvariants :: [Variant]}
    deriving (Eq, Ord, Show, Generic)

data VariantDiscr
  = Explicit DefId
  | Relative Int
  deriving (Eq, Ord, Show, Generic)


data CtorKind
  = FnKind
  | ConstKind
  | FictiveKind
  deriving (Eq, Ord, Show, Generic)


data Variant = Variant {_vname :: DefId, _vdiscr :: VariantDiscr, _vfields :: [Field], _vctorkind :: CtorKind}
    deriving (Eq, Ord,Show, Generic)


data Field = Field {_fName :: DefId, _fty :: Ty, _fsubsts :: Substs}
    deriving (Show, Eq, Ord, Generic)


data CustomTy =
        BoxTy Ty
      | VecTy Ty                 -- ::vec::Vec<Ty>
      | IterTy Ty
      | CEnum DefId [Integer]    -- C-style Enumeration, all variants must be trivial
    deriving (Eq, Ord, Show, Generic)

data Mutability
  = Mut
  | Immut
  deriving (Eq, Ord, Show, Generic)

data Var = Var {
    _varname :: Text,
    _varmut :: Mutability,
    _varty :: Ty,
    _varscope :: VisibilityScope,
    _varpos :: Text }
    deriving (Eq, Show, Generic)

instance Ord Var where
    compare (Var n _ _ _ _) (Var m _ _ _ _) = compare n m


data Collection = Collection {
    _functions :: Map.Map MethName Fn,
    _adts      :: Map.Map AdtName Adt,
    _traits    :: Map.Map TraitName Trait,
    _impls     :: [TraitImpl]
} deriving (Show, Eq, Ord, Generic)

data Predicate =
  TraitPredicate {
    _ptrait :: DefId,
    _psubst :: Substs
    }
  | TraitProjection {
    _pitemid :: DefId,
    _psubst  :: Substs,
    _ty      :: Ty
    }
  | UnknownPredicate
    deriving (Show, Eq, Ord, Generic)

data Param = Param {
    _pname :: Text
} deriving (Show, Eq, Ord, Generic)

newtype Params = Params [Param]
   deriving (Show, Eq, Ord, Generic)


newtype Predicates = Predicates [Predicate]
   deriving (Show, Eq, Ord, Generic)


data Fn = Fn {
    _fname       :: DefId,
    _fargs       :: [Var],
    _freturn_ty  :: Ty,
    _fbody       :: MirBody,
    _fgenerics   :: [Param],
    _fpredicates :: [Predicate],
    _fassocTys   :: [AssocTy]    -- new params added in a pre-pass
    }
    deriving (Show,Eq, Ord, Generic)



data MirBody = MirBody {
    _mvars :: [Var],
    _mblocks :: [BasicBlock]
}
    deriving (Show,Eq, Ord, Generic)


data BasicBlock = BasicBlock {
    _bbinfo :: BasicBlockInfo,
    _bbdata :: BasicBlockData
}
    deriving (Show,Eq, Ord, Generic)



data BasicBlockData = BasicBlockData {
    _bbstmts :: [Statement],
    _bbterminator :: Terminator
}
    deriving (Show,Eq, Ord, Generic)


data Statement =
      Assign { _alhs :: Lvalue, _arhs :: Rvalue, _apos :: Text }
      -- TODO: the rest of these variants also have positions
      | SetDiscriminant { _sdlv :: Lvalue, _sdvi :: Int }
      | StorageLive { _slv :: Var }
      | StorageDead { _sdv :: Var }
      | Nop
    deriving (Show,Eq, Ord, Generic)

-- This is called 'Place' now
data Lvalue =
      Local { _lvar :: Var}         -- ^ local variable
    | Static                        -- ^ static or static mut variable
    | LProjection LvalueProjection  -- ^ projection out of a place (access a field, deref a pointer, etc)
    | Promoted Promoted Ty          -- ^ Constant code promoted to an injected static
    | Tagged Lvalue Text -- for internal use during the translation
    deriving (Show, Eq, Generic)

instance Ord Lvalue where
    compare l1 l2 = compare (show l1) (show l2)


data Rvalue =
        Use { _uop :: Operand }
        -- ^ just read an lvalue
      | Repeat { _rop :: Operand, _rlen :: ConstUsize }
      | Ref { _rbk :: BorrowKind, _rvar :: Lvalue, _rregion :: Text }
      | Len { _lenvar :: Lvalue }
        -- ^ load length from a slice
      | Cast { _cck :: CastKind, _cop :: Operand, _cty :: Ty }
      | BinaryOp { _bop :: BinOp, _bop1 :: Operand, _bop2 :: Operand }
      | CheckedBinaryOp { _cbop :: BinOp, _cbop1 :: Operand, _cbop2 :: Operand }
      | NullaryOp { _nuop :: NullOp, _nty :: Ty }
      | UnaryOp { _unop :: UnOp, _unoperand :: Operand}
      | Discriminant { _dvar :: Lvalue }
      | Aggregate { _ak :: AggregateKind, _ops :: [Operand] }
      | RAdtAg AdtAg
      | RCustom CustomAggregate
    deriving (Show,Eq, Ord, Generic)

data AdtAg = AdtAg { _agadt :: Adt, _avgariant :: Integer, _aops :: [Operand], _adtagty :: Ty }
    deriving (Show, Eq, Ord, Generic)


data Terminator =
        Goto { _gbb :: BasicBlockInfo}
        -- ^ normal control flow
      | SwitchInt { _sdiscr    :: Operand,
                    _switch_ty :: Ty,
                    _svalues   :: [Maybe Integer],
                    _stargets  :: [BasicBlockInfo] }
        -- ^ case  
      | Resume
      | Return
        -- ^ return to caller normally
      | Unreachable
      | Drop { _dloc    :: Lvalue,
               _dtarget :: BasicBlockInfo,
               _dunwind :: Maybe BasicBlockInfo }
      | DropAndReplace { _drloc    :: Lvalue,
                         _drval    :: Operand,
                         _drtarget :: BasicBlockInfo,
                         _drunwind :: Maybe BasicBlockInfo }
      | Call { _cfunc   :: Operand,
               _cargs   :: [Operand],
               _cdest   :: Maybe (Lvalue, BasicBlockInfo),
               _cleanup :: Maybe BasicBlockInfo }
      | Assert { _acond     :: Operand,
                 _aexpected :: Bool,
                 _amsg      :: AssertMessage,
                 _atarget   :: BasicBlockInfo,
                 _acleanup  :: Maybe BasicBlockInfo}
      deriving (Show,Eq, Ord, Generic)

data Operand =
        Copy Lvalue
      | Move Lvalue
      | OpConstant Constant
      deriving (Show, Eq, Ord, Generic)

data Constant = Constant { _conty :: Ty, _conliteral :: Literal } deriving (Show, Eq, Ord, Generic)

data LvalueProjection = LvalueProjection { _lvpbase :: Lvalue, _lvpkind :: Lvpelem }
    deriving (Show,Eq, Ord, Generic)

data Lvpelem =
    Deref
      | PField Int Ty
      | Index Var
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int }
      | Downcast Integer
      deriving (Show, Eq, Ord, Generic)



data NullOp =
        SizeOf
      | Box
      deriving (Show,Eq, Ord, Generic)



data BorrowKind =
        Shared
      | Unique
      | Mutable
      deriving (Show,Eq, Ord, Generic)


data UnOp =
    Not
  | Neg
  deriving (Show,Eq, Ord, Generic)


data BinOp =
    Add
      | Sub
      | Mul
      | Div
      | Rem
      | BitXor
      | BitAnd
      | BitOr
      | Shl
      | Shr
      | Beq
      | Lt
      | Le
      | Ne
      | Ge
      | Gt
      | Offset
      deriving (Show,Eq, Ord, Generic)

data CastKind =
    Misc
      | ReifyFnPointer
      | ClosureFnPointer
      | UnsafeFnPointer
      | Unsize
      deriving (Show,Eq, Ord, Generic)

data Literal =
    Item DefId Substs
  | Value ConstVal
  | LPromoted Promoted
  deriving (Show,Eq, Ord, Generic)

data IntLit
  = U8 Integer
  | U16 Integer
  | U32 Integer
  | U64 Integer
  | Usize Integer
  | I8 Integer
  | I16 Integer
  | I32 Integer
  | I64 Integer
  | Isize Integer
  deriving (Eq, Ord, Show, Generic)

data FloatLit
  = FloatLit FloatKind String
  deriving (Eq, Ord, Show, Generic)


data ConstVal =
    ConstFloat FloatLit
  | ConstInt IntLit
  | ConstStr String
  | ConstByteStr B.ByteString
  | ConstBool Bool
  | ConstChar Char
  | ConstVariant DefId
  | ConstFunction DefId Substs
  | ConstStruct
  | ConstTuple [ConstVal]
  | ConstArray [ConstVal]
  | ConstRepeat ConstVal Int
  deriving (Show,Eq, Ord, Generic)

data AggregateKind =
        AKArray Ty
      | AKTuple
      | AKClosure DefId Substs
      deriving (Show,Eq, Ord, Generic)

data CustomAggregate =
    CARange Ty Operand Operand -- deprecated but here in case something else needs to go here
    deriving (Show,Eq, Ord, Generic)

data Trait = Trait { _traitName       :: DefId,
                     _traitItems      :: [TraitItem],
                     _traitSupers     :: [TraitName],
                     _traitParams     :: [Param],
                     _traitPredicates :: [Predicate],
                     _traitAssocTys   :: [AssocTy]    -- new params added in a pre-pass
                   } 
    deriving (Eq, Ord, Show, Generic)


data TraitItem
    = TraitMethod DefId FnSig [Predicate]
    | TraitType DefId         -- associated type
    | TraitConst DefId Ty
    deriving (Eq, Ord, Show, Generic)

data TraitRef
    = TraitRef DefId Substs
      -- Indicates the trait this impl implements.
      -- `substs` gives the type arguments for the trait,
    deriving (Show, Eq, Ord, Generic)

data TraitImpl
    = TraitImpl { _tiName       :: DefId
                -- name of the impl group (Not very useful)
                , _tiTraitRef   :: TraitRef
                -- name of the trait and the type we are implementing it
                , _tiGenerics   :: [Param]
                , _tiPredicates :: [Predicate]
                , _tiItems      :: [TraitImplItem]
                }
    deriving (Show, Eq, Ord, Generic)
data TraitImplItem
    = TraitImplMethod { _tiiName :: DefId
                        -- the def path of the item
                        -- should match the name of the corresponding entry in 'fns'
                      , _tiiImplements :: DefId
                        -- The def path of the trait-item that this impl-item implements.
                        -- If there is no impl-item that `implements` a particular
                        -- trait-item, that means the impl uses the default from the trait.
                      , _tiiGenerics :: [Param]
                        -- Generics for the method itself.  
                        -- should match the generics of the `fn`.  This consists of the generics
                        -- inherited from the impl (if any), followed by any generics
                        -- declared on the impl-item itself.
                      , _tiiPredicates :: [Predicate]
                      , _tiiSignature  :: FnSig
                      }
      | TraitImplType { _tiiName       :: DefId
                      , _tiiImplements :: DefId
                      , _tiiGenerics   :: [Param]
                      , _tiiPredicates :: [Predicate]
                      , _tiiType       :: Ty
                      }
      deriving (Show, Eq, Ord, Generic)

-- Documentation for particular use-cases of DefIds
type TraitName = DefId
type MethName  = DefId
type AdtName   = DefId

--- Other texts
type Promoted = Text
type ConstUsize = Integer
type VisibilityScope = Text
type AssertMessage = Text
type ClosureSubsts = Text
type BasicBlockInfo = Text


--------------------------------------------------------------------------------------
-- Lenses
--------------------------------------------------------------------------------------


makeLenses ''Variant
makeLenses ''Var
makeLenses ''Collection
makeLenses ''Fn
makeLenses ''MirBody
makeLenses ''BasicBlock
makeLenses ''BasicBlockData
makeLenses ''Adt
makeLenses ''AdtAg
makeLenses ''Trait

makeLenses ''TraitImpl
makeLenses ''TraitImplItem

itemName :: Simple Lens TraitItem DefId
itemName = lens (\ti -> case ti of
                          TraitMethod did _ _ -> did
                          TraitType did -> did
                          TraitConst did _ -> did)
              (\ti nd -> case ti of
                  TraitMethod _ s ps -> TraitMethod nd s ps
                  TraitType _ -> TraitType nd
                  TraitConst _ t -> TraitConst nd t)

--------------------------------------------------------------------------------------
-- Other instances for ADT types
--------------------------------------------------------------------------------------

instance Semigroup Collection where
  (Collection f1 a1 t1 i1) <> (Collection f2 a2 t2 i2) =
    Collection (f1 <> f2) (a1 <> a2) (t1 <> t2) (i1 <> i2)
instance Monoid Collection where
  mempty  = Collection mempty mempty mempty mempty
  mappend = (<>)

  

--------------------------------------------------------------------------------------
--- aux functions ---
--------------------------------------------------------------------------------------

-- | access the Integer in an IntLit
fromIntegerLit :: IntLit -> Integer
fromIntegerLit (U8 i)    = i
fromIntegerLit (U16 i)   = i
fromIntegerLit (U32 i)   = i
fromIntegerLit (U64 i)   = i
fromIntegerLit (Usize i) = i
fromIntegerLit (I8 i)    = i
fromIntegerLit (I16 i)   = i
fromIntegerLit (I32 i)   = i
fromIntegerLit (I64 i)   = i
fromIntegerLit (Isize i) = i


-- | Convert an associated type into a Mir type parameter
toParam :: AssocTy -> Param
toParam (did,_substs) = Param (idText did)  -- do we need to include substs?

-- | Access *all* of the params of the trait
traitParamsWithAssocTys :: Trait -> [Param]
traitParamsWithAssocTys trait =
   trait^.traitParams ++ map toParam (trait^.traitAssocTys)



-- A CStyle ADT is one that is an enumeration of numeric valued options
-- containing no data
isCStyle :: Adt -> Bool
isCStyle (Adt _ variants) = all isConst variants where
    isConst (Variant _ _ [] ConstKind) = True
    isConst _ = False

varOfLvalue :: HasCallStack => Lvalue -> Var
varOfLvalue (Local v) = v
varOfLvalue l = error $ "bad var of lvalue: " ++ show l


lValueofOp :: HasCallStack => Operand -> Lvalue
lValueofOp (Copy lv) = lv
lValueofOp (Move lv) = lv
lValueofOp l = error $ "bad lvalue of op: " ++ show l

funcNameofOp :: HasCallStack => Operand -> DefId
funcNameofOp (OpConstant (Constant _ (Value (ConstFunction id1 _substs)))) = id1
funcNameofOp _ = error "bad extract func name"

funcSubstsofOp :: HasCallStack => Operand -> Substs
funcSubstsofOp (OpConstant (Constant _ (Value (ConstFunction _id1 substs)))) = substs
funcSubstsofOp _ = error "bad extract func name"





--------------------------------------------------------------------------------------
-- | arithType

data ArithType = Signed | Unsigned

class ArithTyped a where
    arithType :: a -> Maybe ArithType
instance TypeOf a => ArithTyped a where
    arithType a =
      case typeOf a of
        (TyInt _) -> Just Signed
        (TyUint _ ) -> Just Unsigned
        _  -> Nothing

--------------------------------------------------------------------------------------
-- | TypeOf

class TypeOf a where
    typeOf :: a -> Ty

instance TypeOf Ty where
    typeOf ty = ty

instance TypeOf Var where
    typeOf (Var _ _ t _ _) = t

instance TypeOf Lvalue where
  typeOf lv = case lv of
    Static                -> error "typeOf: static"
    Tagged lv' _          -> typeOf lv'
    Local (Var _ _ t _ _) -> t
    LProjection proj      -> typeOf proj
    Promoted _ t          -> t

instance TypeOf Rvalue where
  typeOf (Use a) = typeOf a
  typeOf (Repeat a sz) = TyArray (typeOf a) (fromIntegral sz)
  typeOf (Ref Shared lv _)  = TyRef (typeOf lv) Immut
  typeOf (Ref Mutable lv _) = TyRef (typeOf lv) Mut
  typeOf (Ref Unique _lv _)  = error "FIXME? type of Unique reference?"
  typeOf (Len _) = TyUint USize
  typeOf (Cast _ _ ty) = ty
  typeOf (NullaryOp _op ty) = ty
  typeOf (RAdtAg (AdtAg _ _ _ ty)) = ty
  typeOf rv = error ("typeOf Rvalue unimplemented: " ++ show rv)

instance TypeOf Operand where
    typeOf (Move lv) = typeOf lv
    typeOf (Copy lv) = typeOf lv
    typeOf (OpConstant c) = typeOf c

instance TypeOf Constant where
    typeOf (Constant a _b) = a

instance TypeOf LvalueProjection where
  typeOf (LvalueProjection base kind) =
    case kind of
      PField _ t      -> t
      Deref           -> peelRef (typeOf base)
      Index{}         -> peelIdx (typeOf base)
      ConstantIndex{} -> peelIdx (typeOf base)
      Downcast i      -> TyDowncast (typeOf base) i   --- TODO: check this
      Subslice{}      -> TySlice (peelIdx (typeOf base))

   where
   peelRef :: Ty -> Ty
   peelRef (TyRef t _) = t
   peelRef t = t

   peelIdx :: Ty -> Ty
   peelIdx (TyArray t _) = t
   peelIdx (TySlice t)   = t
   peelIdx (TyRef t m)   = TyRef (peelIdx t) m
   peelIdx t             = t

  
--------------------------------------------------------------------------------------------
