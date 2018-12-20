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
import           Data.Text (Text)
import Control.Lens(makeLenses)
import Data.Maybe (fromMaybe)


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
      deriving (Eq, Ord, Show, Generic, GenericOps)

data FloatKind
  = F32
  | F64
  deriving (Eq, Ord, Show, Generic, GenericOps)

-- | Type parameters
newtype Substs = Substs [Ty]
  deriving (Eq, Ord, Show, Generic)
  deriving anyclass (GenericOps)
  deriving newtype (Semigroup, Monoid)

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
    deriving (Eq, Ord, Show, Generic, GenericOps)

data Adt = Adt {_adtname :: DefId, _adtvariants :: [Variant]}
    deriving (Eq, Ord, Show, Generic, GenericOps)

data VariantDiscr
  = Explicit DefId
  | Relative Int
  deriving (Eq, Ord, Show, Generic, GenericOps)


data CtorKind
  = FnKind
  | ConstKind
  | FictiveKind
  deriving (Eq, Ord, Show, Generic, GenericOps)


data Variant = Variant {_vname :: DefId, _vdiscr :: VariantDiscr, _vfields :: [Field], _vctorkind :: CtorKind}
    deriving (Eq, Ord,Show, Generic, GenericOps)


data Field = Field {_fName :: DefId, _fty :: Ty, _fsubsts :: Substs}
    deriving (Show, Eq, Ord, Generic, GenericOps)


data CustomTy =
        BoxTy Ty
      | VecTy Ty
      | IterTy Ty
      | CEnum DefId    -- C-style Enumeration, all variants must be trivial
    deriving (Eq, Ord, Show, Generic, GenericOps)

data Mutability
  = Mut
  | Immut
  deriving (Eq, Ord, Show, Generic, GenericOps)

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
    _functions :: [Fn],
    _adts      :: [Adt],
    _traits    :: [Trait]
} deriving (Show, Eq, Ord, Generic, GenericOps)

data Predicate = Predicate {
    _ptrait :: DefId,
    _psubst :: Substs
    }
    | UnknownPredicate
    deriving (Show, Eq, Ord, Generic, GenericOps)

data Param = Param {
    _pname :: Text
} deriving (Show, Eq, Ord, Generic, GenericOps)

newtype Params = Params [Param]
   deriving (Show, Eq, Ord, Generic)
   deriving anyclass (GenericOps)

newtype Predicates = Predicates [Predicate]
   deriving (Show, Eq, Ord, Generic)
   deriving anyclass (GenericOps)

data Fn = Fn {
    _fname :: DefId,
    _fargs :: [Var],
    _freturn_ty :: Ty,
    _fbody :: MirBody,
    _fgenerics :: [Param],
    _fpredicates :: [Predicate]
    }
    deriving (Show,Eq, Ord, Generic, GenericOps)



data MirBody = MirBody {
    _mvars :: [Var],
    _mblocks :: [BasicBlock]
}
    deriving (Show,Eq, Ord, Generic, GenericOps)


data BasicBlock = BasicBlock {
    _bbinfo :: BasicBlockInfo,
    _bbdata :: BasicBlockData
}
    deriving (Show,Eq, Ord, Generic, GenericOps)



data BasicBlockData = BasicBlockData {
    _bbstmts :: [Statement],
    _bbterminator :: Terminator
}
    deriving (Show,Eq, Ord, Generic, GenericOps)


data Statement =
      Assign { _alhs :: Lvalue, _arhs :: Rvalue, _apos :: Text }
      -- TODO: the rest of these variants also have positions
      | SetDiscriminant { _sdlv :: Lvalue, _sdvi :: Int }
      | StorageLive { _slv :: Var }
      | StorageDead { _sdv :: Var }
      | Nop
    deriving (Show,Eq, Ord, Generic, GenericOps)

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
    deriving (Show,Eq, Ord, Generic, GenericOps)

data AdtAg = AdtAg { _agadt :: Adt, _avgariant :: Integer, _aops :: [Operand]}
    deriving (Show, Eq, Ord, Generic, GenericOps)


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
      deriving (Show,Eq, Ord, Generic, GenericOps)

data Operand =
        Copy Lvalue
      | Move Lvalue
      | OpConstant Constant
      deriving (Show, Eq, Ord, Generic, GenericOps)

data Constant = Constant { _conty :: Ty, _conliteral :: Literal } deriving (Show, Eq, Ord, Generic, GenericOps)

data LvalueProjection = LvalueProjection { _lvpbase :: Lvalue, _lvpkind :: Lvpelem }
    deriving (Show,Eq, Ord, Generic, GenericOps)

data Lvpelem =
    Deref
      | PField Int Ty
      | Index Var
      | ConstantIndex { _cioffset :: Int, _cimin_len :: Int, _cifrom_end :: Bool }
      | Subslice { _sfrom :: Int, _sto :: Int }
      | Downcast Integer
      deriving (Show, Eq, Ord, Generic, GenericOps)



data NullOp =
        SizeOf
      | Box
      deriving (Show,Eq, Ord, Generic, GenericOps)



data BorrowKind =
        Shared
      | Unique
      | Mutable
      deriving (Show,Eq, Ord, Generic, GenericOps)


data UnOp =
    Not
  | Neg
  deriving (Show,Eq, Ord, Generic, GenericOps)


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
      deriving (Show,Eq, Ord, Generic, GenericOps)

data CastKind =
    Misc
      | ReifyFnPointer
      | ClosureFnPointer
      | UnsafeFnPointer
      | Unsize
      deriving (Show,Eq, Ord, Generic, GenericOps)

data Literal =
    Item DefId Substs
  | Value ConstVal
  | LPromoted Promoted
  deriving (Show,Eq, Ord, Generic, GenericOps)

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
  deriving (Eq, Ord, Show, Generic, GenericOps)

data FloatLit
  = FloatLit FloatKind String
  deriving (Eq, Ord, Show, Generic, GenericOps)


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
  deriving (Show,Eq, Ord, Generic, GenericOps)

data AggregateKind =
        AKArray Ty
      | AKTuple
      | AKClosure DefId Substs
      deriving (Show,Eq, Ord, Generic, GenericOps)

data CustomAggregate =
    CARange Ty Operand Operand -- deprecated but here in case something else needs to go here
    deriving (Show,Eq, Ord, Generic, GenericOps)

data Trait = Trait DefId [TraitItem]
    deriving (Eq, Ord, Show, Generic, GenericOps)


data TraitItem
    = TraitMethod DefId FnSig  
    | TraitType DefId         -- associated type
    | TraitConst DefId Ty
    deriving (Eq, Ord, Show, Generic, GenericOps)



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
  markCStyle :: [AdtName] -> a -> a 
  default markCStyle :: (Generic a, GenericOps' (Rep a)) => [AdtName] -> a -> a
  markCStyle s x = to (markCStyle' s (from x))

  -- | Type variable substitution. Type variables are represented via indices.
  tySubst :: Substs -> a -> a 
  default tySubst :: (Generic a, GenericOps' (Rep a)) => Substs -> a -> a
  tySubst s x = to (tySubst' s (from x))

  -- | Renaming for term variables
  replaceVar :: Var -> Var -> a -> a
  default replaceVar :: (Generic a, GenericOps' (Rep a)) => Var -> Var -> a -> a
  replaceVar o n x = to (replaceVar' o n (from x))

  -- |
  replaceLvalue :: Lvalue -> Lvalue -> a -> a
  default replaceLvalue :: (Generic a, GenericOps' (Rep a)) => Lvalue -> Lvalue -> a -> a
  replaceLvalue o n x = to (replaceLvalue' o n (from x))

  

-- special case for DefIds
instance GenericOps DefId where
  relocate     = relocateDefId 
  markCStyle _   = id
  tySubst    _   = id
  replaceVar _ _ = id
  replaceLvalue _ _ = id  

-- special case for Tys
instance GenericOps Ty where

  -- Translate C-style enums to CEnum types
  markCStyle s (TyAdt n (Substs []))  | n `elem` s = TyCustom (CEnum n)
  markCStyle s (TyAdt n _ps) | n `elem` s = error "Cannot have params to C-style enum!"
  markCStyle s ty = to (markCStyle' s (from ty))

  -- Substitute for type variables
  tySubst (Substs substs) (TyParam i)
     | fromInteger i < length substs = substs !! fromInteger i 
     | otherwise    = error $ "Indexing at " ++ show i ++ "  from subst " ++ show substs
  tySubst substs ty = to (tySubst' substs (from ty))

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


class GenericOps' f where
  relocate'   :: f p -> f p
  markCStyle' :: [AdtName] -> f p -> f p
  tySubst'    :: Substs -> f p -> f p 
  replaceVar' :: Var -> Var -> f p -> f p
  replaceLvalue' :: Lvalue -> Lvalue -> f p -> f p
  
instance GenericOps' V1 where
  relocate' _x      = error "impossible: this is a void type"
  markCStyle' _ _x  = error "impossible: this is a void type"
  tySubst' _ _      = error "impossible: this is a void type"
  replaceVar' _ _ _ = error "impossible: this is a void type"
  replaceLvalue' _ _ _ = error "impossible: this is a void type"

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


instance (GenericOps' f, GenericOps' g) => GenericOps' (f :*: g) where
  relocate'       (x :*: y) = relocate'   x     :*: relocate' y
  markCStyle' s   (x :*: y) = markCStyle'   s x :*: markCStyle' s y
  tySubst'    s   (x :*: y) = tySubst'      s x :*: tySubst'    s y
  replaceVar' o n (x :*: y) = replaceVar' o n x :*: replaceVar' o n y
  replaceLvalue' o n (x :*: y) = replaceLvalue' o n x :*: replaceLvalue' o n y
  

instance (GenericOps c) => GenericOps' (K1 i c) where
  relocate'     (K1 x) = K1 (relocate x)
  markCStyle' s (K1 x) = K1 (markCStyle s x)
  tySubst'    s (K1 x) = K1 (tySubst s x)
  replaceVar' o n (K1 x) = K1 (replaceVar o n x)
  replaceLvalue' o n (K1 x) = K1 (replaceLvalue o n x)  
  
instance (GenericOps' f) => GenericOps' (M1 i t f) where
  relocate'     (M1 x) = M1 (relocate' x)
  markCStyle' s (M1 x) = M1 (markCStyle' s x)
  tySubst'    s (M1 x) = M1 (tySubst' s x)
  replaceVar' o n (M1 x) = M1 (replaceVar' o n x)
  replaceLvalue' o n (M1 x) = M1 (replaceLvalue' o n x)

instance (GenericOps' U1) where
  relocate'      U1 = U1
  markCStyle' _s U1 = U1
  tySubst'    _s U1 = U1
  replaceVar' _ _ U1 = U1
  replaceLvalue' _ _ U1 = U1 

                      
instance GenericOps a => GenericOps [a]
instance GenericOps a => GenericOps (Maybe a)
instance (GenericOps a, GenericOps b) => GenericOps (a,b)
instance GenericOps Int     where
   relocate   = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Integer where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Char    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Bool    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps Text    where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id
   
instance GenericOps B.ByteString where
   relocate = id
   markCStyle = const id
   tySubst    = const id
   replaceVar _ _ = id
   replaceLvalue _ _ = id   

instance GenericOps b => GenericOps (Map.Map a b) where
   relocate       = Map.map relocate 
   markCStyle s    = Map.map (markCStyle s)
   tySubst s      = Map.map (tySubst s)
   replaceVar o n = Map.map (replaceVar o n)
   replaceLvalue o n = Map.map (replaceLvalue o n)   

replaceList :: GenericOps a => [(Lvalue, Lvalue)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replaceLvalue old new a
    

--------------------------------------------------------------------------------------


makeLenses ''Variant
makeLenses ''Var
makeLenses ''Collection
makeLenses ''Fn


instance Semigroup Collection where
  (Collection f1 a1 t1)<> (Collection f2 a2 t2) =
    Collection (f1 ++ f2) (a1 ++ a2) (t1 ++ t2)
instance Monoid Collection where
  mempty = Collection [] [] []
  

--------------------------------------------------------------------------------------
--- aux functions ---
--------------------------------------------------------------------------------------

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


fromIntegerLit :: IntLit -> Integer
fromIntegerLit (U8 i) = i
fromIntegerLit (U16 i) = i
fromIntegerLit (U32 i) = i
fromIntegerLit (U64 i) = i
fromIntegerLit (Usize i) = i
fromIntegerLit (I8 i) = i
fromIntegerLit (I16 i) = i
fromIntegerLit (I32 i) = i
fromIntegerLit (I64 i) = i
fromIntegerLit (Isize i) = i


isMutRefTy :: Ty -> Bool
isMutRefTy (TyRef t m) = (m == Mut) || isMutRefTy t
isMutRefTy (TySlice t) = isMutRefTy t
isMutRefTy (TyArray t _) = isMutRefTy t
isMutRefTy (TyTuple ts) = foldl (\acc t -> acc || isMutRefTy t) False ts
isMutRefTy (TyCustom (BoxTy t)) = isMutRefTy t
isMutRefTy _ = False


-- Does this type contain any type parameters
isPoly :: Ty -> Bool
isPoly (TyParam _) = True
isPoly (TyTuple ts) = any isPoly ts
isPoly (TySlice ty) = isPoly ty
isPoly (TyArray ty _i) = isPoly ty
isPoly (TyRef ty _mut) = isPoly ty
isPoly (TyRawPtr ty _mut) = isPoly ty
isPoly (TyAdt _ (Substs params)) = any isPoly params
isPoly (TyFnDef _ (Substs params)) = any isPoly params
isPoly (TyClosure _ (Substs params)) = any isPoly params
isPoly (TyCustom (BoxTy ty)) = isPoly ty
isPoly (TyCustom (VecTy ty)) = isPoly ty
isPoly (TyCustom (IterTy ty)) = isPoly ty
isPoly _x = False           

isNever :: Ty -> Bool
isNever (TyAdt defId _) = fst (did_name defId) == "Never"
isNever _ = False

--------------------------------------------------------------------------------------
-- | arithType

data ArithType = Signed | Unsigned

class ArithTyped a where
    arithType :: a -> Maybe ArithType

instance ArithTyped Ty where
    arithType (TyInt _) = Just Signed
    arithType (TyUint _) = Just Unsigned
    arithType _ = Nothing

instance ArithTyped Var where
    arithType (Var _ _ ty _ _) = arithType ty

instance ArithTyped Lvalue where
    arithType (Local var) = arithType var
    arithType Static = Nothing
    arithType (LProjection (LvalueProjection _a (PField _f ty))) = arithType ty
    arithType _ = error "unimpl arithtype"

instance ArithTyped Operand where
    arithType (Move lv) = arithType lv
    arithType (Copy lv) = arithType lv
    arithType (OpConstant (Constant ty _)) = arithType ty

--------------------------------------------------------------------------------------
-- | TypeOf

class TypeOf a where
    typeOf :: a -> Ty

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

  
--------------------------------------------------------------------------------------

{-

-- SUBSUMED by generic version above

class Replace v a where
    replace :: v -> v -> a -> a

instance (Replace v [Var], Replace v MirBody) => Replace v Fn where
    replace old new (Fn fname1 args fretty fbody1) = Fn fname1 (replace old new args) fretty (replace old new fbody1)

instance (Replace v [Var], Replace v [BasicBlock]) => Replace v MirBody where
    replace old new (MirBody a blocks) = MirBody a $ replace old new blocks

instance Replace v a => Replace v (Map.Map b a) where
    replace old new = Map.map (replace old new)

instance Replace v a => Replace v [a] where
    replace old new = Data.List.map (replace old new)

instance (Replace v BasicBlockData) => Replace v BasicBlock where
    replace old new (BasicBlock bbi bbd) = BasicBlock bbi $ replace old new bbd

instance (Replace v [Statement], Replace v Terminator) => Replace v BasicBlockData where
    replace old new (BasicBlockData stmts term) = BasicBlockData (replace old new stmts) (replace old new term)

instance (Replace v Operand, Replace v Lvalue) => Replace v Terminator where
    replace old new (SwitchInt op ty vals targs) = SwitchInt (replace old new op) ty vals targs
    replace old new (Drop loc targ un) = Drop (replace old new loc) targ un
    replace old new (DropAndReplace loc val targ un) = DropAndReplace (replace old new loc) (replace old new val) targ un
    replace old new (Call f args (Just (d1, d2)) cl)
      = Call (replace old new f) (replace old new args) (Just (replace old new d1, d2)) cl
    replace old new (Assert cond exp1 m t cl) = Assert (replace old new cond) exp1 m t cl
    replace _old _new t = t

instance (Replace v Lvalue, Replace v Rvalue) => Replace v Statement where
    replace old new (Assign lv rv p) = Assign (replace old new lv) (replace old new rv) p
    replace old new (SetDiscriminant lv i) = SetDiscriminant (replace old new lv) i
    replace old new (StorageLive l) = StorageLive (replace old new l)
    replace old new (StorageDead l) = StorageDead (replace old new l)
    replace _old _new Nop = Nop

instance Replace Var Var where
    replace old new v = if _varname v == _varname old then new else v

instance Replace Lvalue Var where
    replace (Local old) (Local new) v = replace old new v
    replace _ _ v = v

instance Replace Var Lvalue where
    replace old new (Tagged lv t) = Tagged (replace old new lv) t
    replace old new (Local v) = Local $ replace old new v
    replace _old _new Static = Static
    replace old new (LProjection (LvalueProjection lbase lkind)) = LProjection $ LvalueProjection (replace old new lbase) lkind

instance Replace Lvalue Lvalue where
    replace old new v = fromMaybe v (repl_lv v)
      where
        repl_lv :: Lvalue -> Maybe Lvalue -- some light unification
        repl_lv v0 =
          case v0 of
            LProjection (LvalueProjection lb k)
              | Just ans <- repl_lv lb -> Just $ LProjection (LvalueProjection ans k)
            Tagged lb _ | Just ans <- repl_lv lb -> Just ans
            _ | v == old -> Just new
            _ -> Nothing


instance (Replace v Lvalue) => Replace v Operand where
    replace old new (Consume lv) = Consume (replace old new lv)
    replace _old _new o = o

instance (Replace v Operand, Replace v Lvalue, Replace v Var) => Replace v Rvalue where
    replace old new (Use o) = Use (replace old new o)
    replace old new (Repeat a b) = Repeat (replace old new a) b
    replace old new (Ref a b c) = Ref a (replace old new b) c
    replace old new (Len a) = Len (replace old new a)
    replace old new (Cast a b c) = Cast a (replace old new b) c
    replace old new (BinaryOp a b c) = BinaryOp a (replace old new b) (replace old new c)
    replace old new (CheckedBinaryOp a b c) = CheckedBinaryOp a (replace old new b) (replace old new c)
    replace old new (Discriminant v) = Discriminant (replace old new v)
    replace old new (Aggregate a bs) = Aggregate a (replace old new bs)
    replace old new (RCustom (CARange ty o1 o2)) = RCustom (CARange ty (replace old new o1) (replace old new o2))
    replace _old _new (UnaryOp a b) = UnaryOp a b
    replace _old _new t = error $ "bad replacevar: " ++ show t



replaceList :: (Replace v a) => [(v, v)] -> a -> a
replaceList [] a = a
replaceList ((old,new) : vs) a = replaceList vs $ replace old new a


replaceVar :: (Replace Var a) => Var -> Var -> a -> a
replaceVar = replace 

replaceLvalue :: (Replace Lvalue a) => Lvalue -> Lvalue -> a -> a
replaceLvalue = replace 

-}
    
{-
--------------------------------------------------------------------------------------
-- | Pretty printing instances

class PPrint a where
    pprint :: a -> String

pprint_fn1 :: (PPrint a) => String -> a -> String
pprint_fn1 fn a = fn ++ "(" ++ pprint a ++ ");"

pprint_fn2 :: (PPrint a, PPrint b) => String -> a -> b -> String
pprint_fn2 fn a b = fn ++ "(" ++ pprint a ++ ", " ++ pprint b ++ ");"

pprint_fn3 :: (PPrint a, PPrint b, PPrint c) => String -> a -> b -> c -> String
pprint_fn3 fn a b c = fn ++ "(" ++ pprint a ++ ", " ++ pprint b ++ ", " ++ pprint c ++ ");"

pprint_fn4 :: (PPrint a, PPrint b, PPrint c, PPrint d) => String -> a -> b -> c -> d -> String
pprint_fn4 fn a b c d = fn ++ "(" ++ pprint a ++ ", " ++ pprint b ++ ", " ++ pprint c ++ ", " ++ pprint d ++ ");"

instance PPrint a => PPrint (Maybe a) where
    pprint (Just a) = pprint a
    pprint Nothing = ""

instance PPrint Text where
    pprint = unpack

instance PPrint DefId where
    pprint = show 

instance PPrint Int where
    pprint = show

instance PPrint a => PPrint [a] where
    pprint as = "(" ++ pas ++ ")" where
        pas = mconcat $ Data.List.intersperse ", " (Prelude.map pprint as)

instance (PPrint a, PPrint b) => PPrint (a,b) where
    pprint (a,b) = "(" ++ pprint a ++ ", " ++ pprint b ++ ")"

instance PPrint Bool where
    pprint = show

instance PPrint BaseSize where
    pprint = show

instance PPrint FloatKind where
    pprint = show

instance PPrint Substs where
    pprint = show

instance PPrint Ty where
    pprint = show

instance PPrint Adt where
   pprint (Adt nm vs) = pprint_fn2 "Adt" nm vs
    
instance PPrint VariantDiscr where
  pprint (Explicit a) = pprint_fn1 "Explicit" a
  pprint (Relative a) = pprint_fn1 "Relative" a


instance PPrint CtorKind where
  pprint = show

instance PPrint Variant where
  pprint (Variant nm dscr flds knd) = pprint_fn4 "Variant" nm dscr flds knd

instance PPrint Field where
    pprint (Field nm ty sbs) = pprint_fn3 "Field" nm ty sbs

instance PPrint CustomTy where
    pprint = show

instance PPrint Mutability where
    pprint = show

instance PPrint Var where
    pprint (Var vn vm _vty _vs _) = j ++ unpack vn -- ++ ": " ++  pprint vty
        where
            j = case vm of
                  Mut -> "mut "
                  _ -> ""

instance PPrint Fn where
    pprint (Fn fname1 fargs1 fty fbody1 _ _) = pprint fname1 ++ "(" ++ pargs ++ ") -> " ++ pprint fty ++ " {\n" ++ pprint fbody1 ++ "}\n"
        where
            pargs = mconcat $ Data.List.intersperse "\n" (Prelude.map pprint fargs1)

instance PPrint MirBody where
    pprint (MirBody mvs mbs) = pvs ++ "\n" ++ pbs ++ "\n"
        where
            pvs = mconcat $ Data.List.intersperse "\n" (Prelude.map ((\s -> "alloc " ++ s) . pprint) mvs)
            pbs = mconcat $ Data.List.intersperse "\n" (Prelude.map pprint mbs)
    
instance PPrint BasicBlock where
    pprint (BasicBlock info dat) = pprint info ++ " { \n" ++ pprint dat ++ "} \n"

instance PPrint BasicBlockData where
    pprint (BasicBlockData bbds bbt) = pbs ++ "\n" ++ "\t" ++ pprint bbt ++ "\n"
        where
            a = Prelude.map pprint bbds
            b = Prelude.map (\v -> "\t" ++ v) a
            pbs = mconcat $ Data.List.intersperse "\n" b

instance PPrint Statement where
    pprint (Assign lhs rhs _) = pprint lhs ++ " = " ++ pprint rhs ++ ";"
    pprint (SetDiscriminant lhs rhs) = pprint lhs ++ " d= " ++ pprint rhs ++ ";"
    pprint (StorageLive l) = pprint_fn1 "StorageLive" l
    pprint (StorageDead l) = pprint_fn1 "StorageDead" l
    pprint Nop = "nop;"

instance PPrint Lvalue where
    pprint (Local v) = pprint v
    pprint Static = "STATIC"
    pprint (LProjection p) = pprint p
    pprint (Tagged lv t) = show t ++ "(" ++ pprint lv ++ ")"
    pprint (Promoted p _t) = pprint_fn1 "Promoted" p
    
instance PPrint Rvalue where
    pprint (Use a) = pprint_fn1 "Use" a
    pprint (Repeat a b) = pprint_fn2 "Repeat" a b
    pprint (Ref a b c) = pprint_fn3 "Ref" a b c
    pprint (Len a) = pprint_fn1 "Len" a
    pprint (Cast a b c) = pprint_fn3 "Cast" a b c
    pprint (BinaryOp a b c) = pprint_fn3 "BinaryOp" a b c
    pprint (CheckedBinaryOp a b c) = pprint_fn3 "CheckedBinaryOp" a b c
    pprint (NullaryOp a b) = pprint_fn2 "NullaryOp" a b
    pprint (UnaryOp a b) = pprint_fn2 "UnaryOp" a b
    pprint (Discriminant a) = pprint_fn1 "Discriminant" a
    pprint (Aggregate a b) = pprint_fn2 "Aggregate" a b
    pprint (RAdtAg a) = pprint_fn1 "RAdtAg" a
    pprint (RCustom a) = pprint_fn1 "RCustom" a

instance PPrint AdtAg where
  pprint (AdtAg adt i ops) = pprint_fn3 "AdtAg" adt i ops


instance PPrint Terminator where
    pprint (Goto g) = "goto " ++ pprint g ++ ";"
    pprint (SwitchInt op ty vs bs) = "switchint " ++ pprint op ++ ": " ++ pprint ty ++ " " ++ pprint vs ++ " -> " ++ pprint bs
    pprint Return = "return;"
    pprint Resume = "resume;"
    pprint Unreachable = "unreachable;"
    pprint (Drop _l _target _unwind) = "drop;"
    pprint DropAndReplace{} = "dropreplace;"
    pprint (Call f args dest _cleanup) = "call " ++ pprint f ++ pprint args ++ " -> " ++ pprint dest
    pprint (Assert op expect _msg target1 _cleanup) = "assert " ++ pprint op ++ " == " ++ pprint expect ++ " -> " ++ pprint target1



instance PPrint Operand where
    pprint (Move lv) = "Move(" ++ pprint lv ++ ")"
    pprint (Copy lv) = "Copy(" ++ pprint lv ++ ")"
    pprint (OpConstant c) = "Constant(" ++ pprint c ++ ")"


instance PPrint Constant where
    pprint (Constant _a b) = pprint b -- pprint_fn2 "Constant" a b

instance PPrint LvalueProjection where
    pprint (LvalueProjection lv le) = "Projection(" ++ pprint lv ++", " ++  pprint le ++ ")"

instance PPrint Lvpelem where
    pprint Deref = "Deref"
    pprint (PField a b) = pprint_fn2 "Field" a b
    pprint (Index a) = pprint_fn1 "Index" a
    pprint (ConstantIndex a b c) = pprint_fn3 "ConstantIndex" a b c
    pprint (Subslice a b) = pprint_fn2 "Subslice" a b
    pprint (Downcast a) = pprint_fn1 "Downcast" a

instance PPrint NullOp where
    pprint = show

instance PPrint BorrowKind where
    pprint = show

instance PPrint UnOp where
    pprint = show

instance PPrint BinOp where
    pprint = show

instance PPrint CastKind where
    pprint = show

instance PPrint Literal where
    pprint (Item a b) = pprint_fn2 "Item" a b
    pprint (Value a) = pprint_fn1 "Value" a
    pprint (LPromoted a) = pprint a

instance PPrint IntLit where
  pprint = show

instance PPrint FloatLit where
  pprint = show
  
instance PPrint ConstVal where
    pprint (ConstFloat i) = show i
    pprint (ConstInt i) = show i
    pprint (ConstStr i) = show i
    pprint (ConstByteStr i) = show i
    pprint (ConstBool i) = show i
    pprint (ConstChar i) = show i
    pprint (ConstVariant i) = pprint i
    pprint (ConstTuple cs) = "("++pcs++")" where
        pcs = mconcat $ Data.List.intersperse ", " (Prelude.map pprint cs)
    pprint (ConstArray cs) = "["++pcs++"]" where
        pcs = mconcat $ Data.List.intersperse ", " (Prelude.map pprint cs)
    pprint (ConstRepeat cv i) = "["++pprint cv++"; " ++ show i ++ "]"
    pprint (ConstFunction a _b) = show a
    pprint ConstStruct = "ConstStruct"

instance PPrint AggregateKind where
    pprint (AKArray t) = "[" ++ pprint t ++ "]"
    pprint AKTuple = "tup"
    pprint f = show f

instance PPrint CustomAggregate where
    pprint = show

instance PPrint Integer where
    pprint = show

instance PPrint (Map.Map Lvalue Lvalue) where
    pprint m = unwords $ Data.List.map (\(k,v) -> pprint k ++ " => " ++ pprint v ++ "\n") p
        where p = Map.toList m

instance PPrint FnSig where
  pprint (FnSig args ret) = pprint args ++ " -> " ++ pprint ret

instance PPrint TraitItem where
  pprint (TraitMethod name sig) = pprint name ++ ":" ++ pprint sig
  pprint (TraitType name) = "name "  ++ pprint name
  pprint (TraitConst name ty) = "const " ++ pprint name ++ ":" ++ pprint ty

instance PPrint Trait where
  pprint (Trait name items) =
    "trait " ++ pprint name ++ pprint items

instance PPrint Collection where
  pprint col =
    pprint (col^.functions) ++ "\n" ++
    pprint (col^.adts)      ++ "\n" ++
    pprint (col^.traits)    ++ "\n" 
-}


--------------------------------------------------------------------------------------------
