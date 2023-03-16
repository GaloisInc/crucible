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
{-# LANGUAGE DeriveGeneric #-}

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
)
-}
where

import           Data.Kind(Type)

import qualified Data.Aeson as Aeson
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import           Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Char(isDigit)
import           Data.Functor.Identity
import           GHC.Generics (Generic)

import           Control.Lens hiding (Empty, (:>), Index, view)
import           Control.Monad
import           Control.Monad.ST

import           Prettyprinter

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.Peano
import           Data.Parameterized.BoolRepr
import           Data.Parameterized.NatRepr

import qualified Lang.Crucible.FunctionHandle as FH
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.Expr as E
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Syntax as S



import           Mir.DefId
import           Mir.Mir
import           Mir.Intrinsics
import           Mir.PP

import           Unsafe.Coerce(unsafeCoerce)
import           Debug.Trace
import           GHC.Stack
import Control.Applicative ((<|>))


--------------------------------------------------------------------------------------
-- * Result of translating a collection
--
--
data RustModule = RustModule {
         _rmCS    :: CollectionState
       , _rmCFGs  :: Map Text (Core.AnyCFG MIR)
       , _rmTransInfo :: TransInfo
     }


---------------------------------------------------------------------------------

-- | The main data type for values, bundling the term-level
-- type ty along with a crucible expression of type ty
data MirExp s where
    MirExp :: C.TypeRepr ty -> R.Expr MIR s ty -> MirExp s

-- | MirExp, but with a static guarantee that it's a MirReference.  Used as the
-- result of lvalue evaluation.
data MirPlace s where
    MirPlace :: C.TypeRepr ty -> R.Expr MIR s (MirReferenceType ty) -> PtrMetadata s -> MirPlace s

-- | MIR supports a notion of "unsized places" - for example, it generates code
-- like `(*s)[i]` where `s` is a slice.  To handle this, we attach the metadata
-- of `s` to the `MirPlace` that represents `*s`.  This lets us apply the
-- correct offset and bounds checks in `(*s)[i]`, and the metadata is also used
-- to reconstruct the original `MirSliceType` in case of `&*s`.
--
-- rustc also supports "unsized rvalues".  Currently we don't support them, but
-- we may need to add `PtrMetadata` to `MirExp`s at some point as well.
data PtrMetadata s =
      NoMeta
    | SliceMeta (R.Expr MIR s UsizeType)

instance Show (PtrMetadata s) where
    show NoMeta = "NoMeta"
    show (SliceMeta _) = "SliceMeta"

---------------------------------------------------------------------------------

-- * The top-level generator type
-- h state monad token
-- s phantom parameter for CFGs
type MirGenerator h s ret = G.Generator MIR s FnState ret (ST h)

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
              _assertFalseOnError :: !Bool,
              _transInfo  :: !FnTransInfo
            }

-- | State about the entire collection used for the translation
data CollectionState
  = CollectionState {
      _handleMap      :: !HandleMap,
      _vtableMap      :: !VtableMap,
      _staticMap      :: !(Map DefId StaticVar),
      -- | For Enums, gives the discriminant value for each variant.
      _discrMap       :: !(Map AdtName [Integer]),
      _collection     :: !Collection
      }


---------------------------------------------------------------------------
-- ** Custom operations

data CustomOpMap = CustomOpMap
    { _opDefs :: Map ExplodedDefId CustomRHS
    , _fnPtrShimOp :: Ty -> CustomOp
    , _cloneShimOp :: Ty -> [DefId] -> CustomOp
    , _cloneFromShimOp :: Ty -> [DefId] -> CustomOp
    }

data CustomOp      =
    -- | Custom operation for [argument types] and [operand values]
    CustomOp (forall h s ret. HasCallStack
                 => [Ty]
                 -> [MirExp s]
                 -> MirGenerator h s ret (MirExp s))
  -- | Similar to CustomOp, but receives the name of the monomorphic function
  -- it's replacing.  This way, the implementation can look up the original
  -- definition of the function and extract details such as the return type.
  --
  -- Arguments:
  --   * The name of the monomorphized function
  --   * [operand values]
  | CustomOpNamed (forall h s ret. HasCallStack
                 => DefId
                 -> [MirExp s]
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
  StaticVar :: G.GlobalVar ty -> StaticVar


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

instance Show (VarInfo s tp) where
    showsPrec d (VarRegister r) = showParen (d > 10) $
        showString "VarRegister " . showsPrec 11 r
    showsPrec d (VarReference r) = showParen (d > 10) $
        showString "VarReference " . showsPrec 11 r
    showsPrec d (VarAtom a) = showParen (d > 10) $
        showString "VarAtom " . showsPrec 11 a
instance ShowF (VarInfo s)


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
-- *** VtableMap

-- | The VtableMap maps the name of each vtable to the MirHandles for the
-- vtable shims it contains.
type VtableMap = Map VtableName [MirHandle]




---------------------------------------------------------------------------
-- *** TransInfo

-- | Metadata from the translation that produced some Crucible block.
-- Currently, we just record detailed terminator info for some blocks.
-- Coverage reporting uses this info to turn Crucible-level branch coverage
-- data into a useful source-level coverage report.
data BranchTransInfo =
    -- | A two-way branch on a boolean value.  `BoolBranch trueDest falseDest
    -- span` represents a MIR branch on some input, which goes to `trueDest` on
    -- nonzero and `falseDest` on zero.  Both `dest` values are stringified
    -- `BlockID`s, which lets us avoid threading an extra type parameter `s`
    -- through a bunch of places.  The `span` is the Rust source location of
    -- the branch.
      BoolBranch Text Text Text
    -- | An integer switch.  `IntBranch vals dests span` represents a MIR
    -- switch terminator that compares its input to each value in `vals`,
    -- branching to the corresponding entry in `dests` if they're equal.  There
    -- is one more entry in `dests` than in `vals`, which gives the default
    -- destination if the input matches none of the `vals`.  The `span`
    -- argument gives the source location of the switch in the original Rust
    -- code.
    | IntBranch [Integer] [Text] Text
    -- | A two-way branch on a drop flag.  These branches are uninteresting; we
    -- include them in the translation info only to mark them as explicitly
    -- ignored.
    | DropFlagBranch
  deriving (Show, Generic)

instance Aeson.ToJSON BranchTransInfo where
    toEncoding = Aeson.genericToEncoding Aeson.defaultOptions

-- | Translation metadata for a function.  This is a map from block names to
-- translation info for that block.  Keys are the printed form of BlockID - we
-- don't store the actual BlockID because we'd have to add the `s` type
-- parameter to a bunch of things.
data FnTransInfo = FnTransInfo
    { _ftiBranches :: Seq BranchTransInfo
    , _ftiUnreachable :: Set Text
    }
  deriving (Generic)

instance Aeson.ToJSON FnTransInfo where
    toEncoding = Aeson.genericToEncoding Aeson.defaultOptions

instance Semigroup FnTransInfo where
    (FnTransInfo b1 u1) <> (FnTransInfo b2 u2) =
        FnTransInfo (b1 <> b2) (u1 <> u2)

instance Monoid FnTransInfo where
    mempty = FnTransInfo mempty mempty

-- | Translation info for the entire crate.  Keys are printed function DefIds,
-- since that's what's convenient in transCollection (and because the only
-- purpose of this type is to be JSON-serialized, which stringifies map keys
-- anyway).
type TransInfo = Map Text FnTransInfo






-------------------------------------------------------------------------------------------------------

makeLenses ''FnState
makeLenses ''MirHandle
makeLenses ''CollectionState
makeLenses ''RustModule
makeLenses ''CustomOpMap
makeLenses ''FnTransInfo

$(return [])

-------------------------------------------------------------------------------------------------------

-- ** Operations and instances

instance Semigroup RustModule where
  (RustModule cs1 cm1 ex1) <> (RustModule cs2 cm2 ex2) =
    RustModule (cs1 <> cs2) (cm1 <> cm2) (ex1 <> ex2)
instance Monoid RustModule where
  mempty  = RustModule mempty mempty mempty

instance Semigroup CollectionState  where
  (CollectionState hm1 vm1 sm1 dm1 col1) <> (CollectionState hm2 vm2 sm2 dm2 col2) =
      (CollectionState (hm1 <> hm2) (vm1 <> vm2) (sm1 <> sm2) (dm1 <> dm2) (col1 <> col2))
instance Monoid CollectionState where
  mempty  = CollectionState mempty mempty mempty mempty mempty


instance Show (MirExp s) where
    show (MirExp tr e) = (show e) ++ ": " ++ (show tr)

instance Show (MirPlace s) where
    show (MirPlace tr e m) = show e ++ ", " ++ show m ++ ": & " ++ show tr

instance Show MirHandle where
    show (MirHandle _nm sig c) =
      show c ++ ":" ++ show sig

instance Pretty MirHandle where
    pretty (MirHandle nm sig _c) =
      viaShow nm <> colon <> pretty sig


varInfoRepr :: VarInfo s tp -> C.TypeRepr tp
varInfoRepr (VarRegister reg0)  = R.typeOfReg reg0
varInfoRepr (VarReference reg0) =
  case R.typeOfReg reg0 of
    MirReferenceRepr tp -> tp
    _ -> error "impossible: varInfoRepr"
varInfoRepr (VarAtom a) = R.typeOfAtom a

findFn :: DefId -> MirGenerator h s ret Fn
findFn name = do
    optFn <- use $ cs . collection . functions . at name
    case optFn of
        Just x -> return x
        Nothing -> mirFail $ "unknown Fn " ++ show name

findAdt :: DefId -> MirGenerator h s ret Adt
findAdt name = do
    optAdt <- use $ cs . collection . adts . at name
    case optAdt of
        Just x -> return x
        Nothing -> mirFail $ "unknown ADT " ++ show name

-- Find the ADT definition that is monomorphized from `origName` with `substs`.
-- This should only be used on types that are known to be present in the crate
-- after dead code elimination - for example, because the type appears in the
-- signature of a function that's being translated.
findAdtInst :: DefId -> Substs -> MirGenerator h s ret Adt
findAdtInst origName substs = do
    insts <- use $ cs . collection . adtsOrig . at origName . to (Maybe.fromMaybe [])
    case List.find (\adt -> adt ^. adtOrigSubsts == substs) insts of
        Just x -> return x
        Nothing -> mirFail $ "unknown ADT " ++ show (origName, substs)

-- | What to do when the translation fails.
mirFail :: String -> MirGenerator h s ret a
mirFail str = do
  b  <- use assertFalseOnError
  db <- use debugLevel
  f  <- use currentFn
  let msg = "Translation error in " ++ show (f^.fname) ++ ": " ++ str
  if b then do
         when (db > 1) $ do
           traceM ("Translation failure: " ++ str)
         when (db > 2) $ do
           traceM (fmt f)
         G.reportError (S.litExpr (Text.pack msg))
       else fail msg


-------------------------------------------------------------------------------------------------------
--
-- | Determine whether a function call can be resolved via explicit name bound in the handleMap
--

resolveFn :: HasCallStack => MethName -> MirGenerator h s ret (Maybe MirHandle)
resolveFn nm = do
  hmap <- use (cs.handleMap)
  return $ Map.lookup nm hmap

---------------------------------------------------------------------------------------------------

-- The `DefId` refers to an entry in the `intrinsics` map, which contains the
-- original `DefId` and `Substs` used to produce the monomorphized instance.
-- Those are what we look up in `customOps`.
resolveCustom :: DefId -> MirGenerator h s ret (Maybe CustomOp)
resolveCustom instDefId = do
    optIntr <- use $ cs . collection . intrinsics . at instDefId
    case optIntr of
        Nothing -> return Nothing
        Just intr -> case intr ^. intrInst . inKind of
            IkFnPtrShim ty -> do
                f <- use $ customOps . fnPtrShimOp
                return $ Just $ f ty
            IkCloneShim ty parts
              | intr ^. intrInst . inDefId == textId "core::clone::Clone::clone" -> do
                f <- use $ customOps . cloneShimOp
                return $ Just $ f ty parts
              | intr ^. intrInst . inDefId == textId "core::clone::Clone::clone_from" -> do
                f <- use $ customOps . cloneFromShimOp
                return $ Just $ f ty parts
              | otherwise -> mirFail $
                    "don't know how to generate CloneShim for unknown method " ++
                    show (intr ^. intrInst . inDefId)
            _ -> do
                let origDefId = intr ^. intrInst . inDefId
                    origSubsts = intr ^. intrInst . inSubsts
                    edid = idKey origDefId
                    -- remove section numbers (if any)
                    removeSectionNumber w =
                      Maybe.fromMaybe w (Text.dropWhile isDigit <$> Text.stripPrefix "#" w)
                    stripSectionNumbers w =
                      let (part1, part2) = Text.breakOn "#" w
                      in  part1 <> removeSectionNumber part2

                    edidSimpl = stripSectionNumbers <$> edid
                optOp <- use $ customOps . opDefs .  at edid
                optOpSimpl <- use $ customOps . opDefs .  at edidSimpl
                case optOp <|> optOpSimpl of
                    Nothing -> return Nothing
                    Just f -> do
                        return $ f origSubsts


---------------------------------------------------------------------------------------------------
-- ** Adding new temporaries to the VarMap

freshVarName :: Text -> Map Text a -> Text
freshVarName base vm =
    head $ filter (\n -> not $ n `Map.member` vm) $
        base : [base <> "_" <> Text.pack (show i) | i <- [0 :: Integer ..]]

-- Generate a fresh name of the form `_temp123`
freshTempName :: Map Text a -> Text
freshTempName vm = freshVarName ("_temp" <> Text.pack (show $ Map.size vm)) vm

allocTempForAtom :: R.Atom s tp -> MirGenerator h s ret Text
allocTempForAtom atom = do
    name <- use $ varMap . to freshTempName
    varMap %= Map.insert name (Some $ VarAtom atom)
    return name

-- Store the value of an expression into a new temporary, and return the name
-- of that temporary.
makeTemp :: MirExp s -> MirGenerator h s ret Text
makeTemp (MirExp _ e) = do
    atom <- G.mkAtom e
    allocTempForAtom atom

makeTempLvalue :: Ty -> MirExp s -> MirGenerator h s ret Lvalue
makeTempLvalue ty exp = do
    name <- makeTemp exp
    -- varIsZST is used only for deciding whether to initialize the variable at
    -- the start of the function, which is not relevant for temporaries created
    -- mid-translation.
    let var = Var name Immut ty {-varIsZST-} False
    return $ LBase var

makeTempOperand :: Ty -> MirExp s -> MirGenerator h s ret Operand
makeTempOperand ty exp = do
    Move <$> makeTempLvalue ty exp


-----------------------------------------------------------------------
-- ** MIR intrinsics Generator interaction

newMirRef ::
  C.TypeRepr tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
newMirRef tp = G.extensionStmt (MirNewRef tp)

integerToMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s UsizeType ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
integerToMirRef tp i = G.extensionStmt (MirIntegerToRef tp i)

globalMirRef ::
  G.GlobalVar tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
globalMirRef gv = G.extensionStmt (MirGlobalRef gv)

constMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
constMirRef tpr v = G.extensionStmt (MirConstRef tpr v)

dropMirRef ::
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret ()
dropMirRef refExp = void $ G.extensionStmt (MirDropRef refExp)

readMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret (R.Expr MIR s tp)
readMirRef tp refExp = G.extensionStmt (MirReadRef tp refExp)

writeMirRef ::
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s tp ->
  MirGenerator h s ret ()
writeMirRef ref x = void $ G.extensionStmt (MirWriteRef ref x)

subanyRef ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType C.AnyType) ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subanyRef tpr ref = G.extensionStmt (MirSubanyRef tpr ref)

subfieldRef ::
  C.CtxRepr ctx ->
  R.Expr MIR s (MirReferenceType (C.StructType ctx)) ->
  Index ctx tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subfieldRef ctx ref idx = G.extensionStmt (MirSubfieldRef ctx ref idx)

subvariantRef ::
  C.CtxRepr ctx ->
  R.Expr MIR s (MirReferenceType (RustEnumType ctx)) ->
  Index ctx tp ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subvariantRef ctx ref idx = G.extensionStmt (MirSubvariantRef ctx ref idx)

subindexRef ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType (MirVectorType tp)) ->
  R.Expr MIR s UsizeType ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subindexRef tp ref idx = G.extensionStmt (MirSubindexRef tp ref idx)

subjustRef ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType (C.MaybeType tp)) ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
subjustRef tp ref = G.extensionStmt (MirSubjustRef tp ref)

mirRef_vectorAsMirVector ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType (C.VectorType tp)) ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType (MirVectorType tp)))
mirRef_vectorAsMirVector tpr ref = G.extensionStmt $ MirRef_VectorAsMirVector tpr ref

mirRef_arrayAsMirVector ::
  C.BaseTypeRepr btp ->
  R.Expr MIR s (MirReferenceType (UsizeArrayType btp)) ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType (MirVectorType (C.BaseToType btp))))
mirRef_arrayAsMirVector btpr ref = G.extensionStmt $ MirRef_ArrayAsMirVector btpr ref

mirRef_eq ::
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret (R.Expr MIR s C.BoolType)
mirRef_eq r1 r2 = G.extensionStmt $ MirRef_Eq r1 r2

mirRef_offset ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s IsizeType ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
mirRef_offset tpr ref offset = G.extensionStmt $ MirRef_Offset tpr ref offset

mirRef_offsetWrap ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s IsizeType ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType tp))
mirRef_offsetWrap tpr ref offset = G.extensionStmt $ MirRef_OffsetWrap tpr ref offset

mirRef_tryOffsetFrom ::
  R.Expr MIR s (MirReferenceType tp) ->
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret (R.Expr MIR s (C.MaybeType IsizeType))
mirRef_tryOffsetFrom r1 r2 = G.extensionStmt $ MirRef_TryOffsetFrom r1 r2

mirRef_peelIndex ::
  C.TypeRepr tp ->
  R.Expr MIR s (MirReferenceType tp) ->
  MirGenerator h s ret (R.Expr MIR s (MirReferenceType (MirVectorType tp)), R.Expr MIR s UsizeType)
mirRef_peelIndex tpr ref = do
    pair <- G.extensionStmt $ MirRef_PeelIndex tpr ref
    return (S.getStruct i1of2 pair, S.getStruct i2of2 pair)

-----------------------------------------------------------------------



vectorSnoc ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  R.Expr MIR s tp ->
  MirGenerator h s ret (R.Expr MIR s (C.VectorType tp))
vectorSnoc tp v e = G.extensionStmt $ VectorSnoc tp v e

vectorHead ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  MirGenerator h s ret (R.Expr MIR s (C.MaybeType tp))
vectorHead tp v = G.extensionStmt $ VectorHead tp v

vectorTail ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  MirGenerator h s ret (R.Expr MIR s (C.VectorType tp))
vectorTail tp v = G.extensionStmt $ VectorTail tp v

vectorInit ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  MirGenerator h s ret (R.Expr MIR s (C.VectorType tp))
vectorInit tp v = G.extensionStmt $ VectorInit tp v

vectorLast ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  MirGenerator h s ret (R.Expr MIR s (C.MaybeType tp))
vectorLast tp v = G.extensionStmt $ VectorLast tp v

vectorConcat ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  R.Expr MIR s (C.VectorType tp) ->
  MirGenerator h s ret (R.Expr MIR s (C.VectorType tp))
vectorConcat tp v e = G.extensionStmt $ VectorConcat tp v e

vectorTake ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  R.Expr MIR s C.NatType ->
  MirGenerator h s ret (R.Expr MIR s (C.VectorType tp))
vectorTake tp v e = G.extensionStmt $ VectorTake tp v e

vectorDrop ::
  C.TypeRepr tp ->
  R.Expr MIR s (C.VectorType tp) ->
  R.Expr MIR s C.NatType ->
  MirGenerator h s ret (R.Expr MIR s (C.VectorType tp))
vectorDrop tp v e = G.extensionStmt $ VectorDrop tp v e

arrayZeroed ::
  (1 <= w) =>
  Assignment C.BaseTypeRepr (idxs ::> idx) ->
  NatRepr w ->
  MirGenerator h s ret (R.Expr MIR s (C.SymbolicArrayType (idxs ::> idx) (C.BaseBVType w)))
arrayZeroed idxs w = G.extensionStmt $ ArrayZeroed idxs w


mirVector_uninit ::
    C.TypeRepr tp ->
    R.Expr MIR s UsizeType ->
    MirGenerator h s ret (R.Expr MIR s (MirVectorType tp))
mirVector_uninit tpr len = G.extensionStmt $ MirVector_Uninit tpr len

mirVector_fromVector ::
    C.TypeRepr tp ->
    R.Expr MIR s (C.VectorType tp) ->
    MirGenerator h s ret (R.Expr MIR s (MirVectorType tp))
mirVector_fromVector tpr v = G.extensionStmt $ MirVector_FromVector tpr v

mirVector_fromArray ::
    C.BaseTypeRepr btp ->
    R.Expr MIR s (UsizeArrayType btp) ->
    MirGenerator h s ret (R.Expr MIR s (MirVectorType (C.BaseToType btp)))
mirVector_fromArray tpr a = G.extensionStmt $ MirVector_FromArray tpr a

mirVector_resize ::
    C.TypeRepr tp ->
    R.Expr MIR s (MirVectorType tp) ->
    R.Expr MIR s UsizeType ->
    MirGenerator h s ret (R.Expr MIR s (MirVectorType tp))
mirVector_resize tpr vec len = G.extensionStmt $ MirVector_Resize tpr vec len




--  LocalWords:  ty ImplementTrait ctx vtable idx runtime struct
--  LocalWords:  vtblToStruct
