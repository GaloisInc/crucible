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
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DeriveGeneric #-}

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
import qualified Data.Foldable as F
import qualified Data.List as List
import           Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Maybe as Maybe
import           Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map
import           Data.Sequence (Seq)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Char(isDigit)
import           GHC.Generics (Generic)

import           Control.Lens hiding (Empty, (:>), Index, parts, view)
import           Control.Monad
import           Control.Monad.ST

import           Prettyprinter

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.Context
import           Data.Parameterized.NatRepr

import qualified Lang.Crucible.FunctionHandle as FH
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.CFG.Generator as G
import qualified Lang.Crucible.CFG.Reg as R
import qualified Lang.Crucible.CFG.Core as Core
import qualified Lang.Crucible.Panic as P
import qualified Lang.Crucible.Syntax as S



import           Mir.DefId
import           Mir.Mir
import           Mir.Intrinsics
import           Mir.PP

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
    MirPlace :: C.TypeRepr ty -> R.Expr MIR s MirReferenceType -> PtrMetadata s -> MirPlace s

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
    | SliceMeta (R.Expr MIR s UsizeType) -- ^ The slice length
    | DynMeta (R.Expr MIR s C.AnyType) -- ^ The trait object's vtable
  deriving Show

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
              _transContext :: !FnTransContext,
              _cs         :: !CollectionState,
              _customOps  :: !CustomOpMap,
              _assertFalseOnError :: !Bool,
              _transInfo  :: !FnTransInfo
            }

-- | The current translation context
data FnTransContext
  = FnContext Fn
    -- ^ We are translating a function definition.
  | StaticContext
    -- ^ We are translating the initializer for static values.
  | ShimContext
    -- ^ We are generating a shim function of some kind.

-- | State about the entire collection used for the translation
data CollectionState
  = CollectionState {
      _handleMap      :: !HandleMap,
      _vtableMap      :: !VtableMap,
      _staticMap      :: !(Map DefId StaticVar),
      -- | For Enums, gives the discriminant value for each variant.
      _discrMap       :: !(Map AdtName [Integer]),
      -- | Map crate names to their respective crate hashes, the latter of
      -- which are used to disambiguate identifier names. We consult this 'Map'
      -- when looking up wired-in names (e.g., 'Option' or 'MaybeUninit' in
      -- @core@) to determine what disambiguator to use.
      --
      -- Note that the range of the 'Map' is a 'NonEmpty' list because it is
      -- possible to depend on two different crates with the same crate name,
      -- but with different hashes. Most of the time, however, this list will
      -- contain exactly one disambiguator per crate name.
      _crateHashesMap :: !(Map Text (NonEmpty Text)),
      -- | Preallocated type IDs per instantiated type for dynamic casts
      -- which provides the answer for the @type_id@ operation. All types
      -- in the program should be represented.
      _tyIdMap        :: !(Map Ty Int),
      _collection     :: !Collection
      }


---------------------------------------------------------------------------
-- ** Custom operations

data CustomOpMap = CustomOpMap
    { _opDefs :: Map ExplodedDefId CustomRHS
    , _cloneShimOp :: Ty -> [DefId] -> CustomOp
    , _cloneFromShimOp :: Ty -> [DefId] -> CustomOp
    , _callOnceVirtShimOp :: Integer -> CustomOp
    -- ^ Implementation of the `IkVirtual` shim for @FnOnce::call_once@.  See
    -- the implementation `Mir.TransCustom.callOnceVirtShimDef` for more
    -- details.  The `Integer` is the index in the vtable of the @call_once@
    -- method.
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

-- | A 'VarMap' maps identifier names to registers.
type VarMap s = Map Text.Text (Some (VarInfo s))

-- | Information about an identifier's variable. Includes both the register for
-- the reference that stores the variable's value ('varInfoReg') and the type
-- of the value ('varInfoRepr').
data VarInfo s tp =
  VarInfo
    { varInfoRepr :: C.TypeRepr tp
    , varInfoReg :: R.Reg s MirReferenceType
    }

-- This is identical to what a derived Show instance would provide, except that
-- 'varInfoRepr' is not shown to make the output more compact.
instance Show (VarInfo s tp) where
    showsPrec d (VarInfo _ r) = showParen (d > 10) $
        showString "VarInfo " . showsPrec 11 r
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
      -- ^ Information about branches in the function
      -- (location in the original source, branch targets etc)
      -- Note that the order of the sequence is important, because during
      -- profiling we refer to branches by their index in this sequence.

    , _ftiUnreachable :: Set Text
      -- ^ These are basic blocks that have been marked as unreachable.
      -- That can happen as the "default" case for a `match` where
      -- all the cases were handled, for example.

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


instance Pretty FnTransContext where
    pretty (FnContext f) = pretty f
    pretty c = pretty (describeFnContext c)

describeFnContext :: FnTransContext -> String
describeFnContext c = case c of
  FnContext f -> show (f ^. fname)
  StaticContext -> "the static initializer"
  ShimContext -> "an auto-generated shim"

expectFnContext :: MirGenerator h s ret Fn
expectFnContext = do
  transCtxt <- use transContext
  case transCtxt of
    FnContext f -> pure f
    c -> mirFail $ "expected function when translating " ++ describeFnContext c


findFn :: DefId -> MirGenerator h s ret Fn
findFn name = do
    optFn <- use $ cs . collection . functions . at name
    case optFn of
        Just x -> return x
        Nothing -> mirFail $ "unknown Fn " ++ show name

-- | Look up an ADT by its monomorphized name, failing if it isn't found.
findAdt :: DefId -> MirGenerator h s ret Adt
findAdt name = do
    col <- use $ cs . collection
    case findAdt' col name of
        Just x -> return x
        Nothing -> mirFail $ "unknown ADT " ++ show name

-- | Look up an ADT by its monomorphized name.
findAdt' :: Collection -> DefId -> Maybe Adt
findAdt' col name = col ^. adts . at name

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

-- Like findAdtInst, but with an `ExplodedDefId` instead of a `DefId`. This uses
-- `findDefId` to compute the `DefId`.
findExplodedAdtInst :: ExplodedDefId -> Substs -> MirGenerator h s ret Adt
findExplodedAdtInst edid substs = do
    did <- findDefId edid
    findAdtInst did substs

-- Like findExplodedAdtInst, but returning a `TyAdt`.
findExplodedAdtTy :: ExplodedDefId -> Substs -> MirGenerator h s ret Ty
findExplodedAdtTy edid substs = do
    adt <- findExplodedAdtInst edid substs
    pure $ TyAdt (adt ^. adtname) (adt ^. adtOrigDefId) (adt ^. adtOrigSubsts)

-- | Find the 'DefId' corresponding to the supplied 'ExplodedDefId'. This
-- consults the 'crateHashesMap' to ensure that the crate's disambiguator is
-- correct. If a crate name is ambiguous (i.e., if there are multiple
-- disambiguators associated with the crate name), this will throw an error.
--
-- This also consults the 'langItems' in the 'Collection' so that if a user
-- looks up the original 'DefId' for a lang item (e.g., @core::option::Option@),
-- then this function will return the @$lang@-based 'DefId' instead (e.g.,
-- @$lang::Option@), as the latter 'DefId' is what will be used throughout the
-- rest of the MIR code.
findDefId :: ExplodedDefId -> MirGenerator h s ret DefId
findDefId edid = do
    crateDisambigs <- use $ cs . crateHashesMap
    langItemDefIds <- use $ cs . collection . langItems
    (crate, path) <-
      case edid of
        crate:path -> pure (crate, path)
        [] -> mirFail "findDefId: DefId with no crate"
    let crateStr = Text.unpack crate
    origDefId <-
      case Map.lookup crate crateDisambigs of
          Just allDisambigs@(disambig :| otherDisambigs)
            |  F.null otherDisambigs
            -> pure $ textId $ Text.intercalate "::"
                    $ (crate <> "/" <> disambig) : path
            |  otherwise
            -> mirFail $ unlines $
                 [ "ambiguous crate " ++ crateStr
                 , "crate disambiguators:"
                 ] ++ F.toList (Text.unpack <$> allDisambigs)
          Nothing -> mirFail $ "unknown crate " ++ crateStr
    pure $ Map.findWithDefault origDefId origDefId langItemDefIds

-- | What to do when the translation fails.
mirFail :: String -> MirGenerator h s ret a
mirFail str = do
  b  <- use assertFalseOnError
  db <- use debugLevel
  transCtxt <- use transContext
  let msg = "Translation error in " ++ describeFnContext transCtxt ++ ": " ++ str
  if b then do
         when (db > 1) $ do
           traceM ("Translation failure: " ++ str)
         when (db > 2) $ do
           traceM (fmt transCtxt)
         G.reportError (S.litExpr (Text.pack msg))
       else error msg


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
            IkCloneShim ty parts
              | idKey (intr ^. intrInst . inDefId) == ["core", "clone", "Clone", "clone"] -> do
                f <- use $ customOps . cloneShimOp
                return $ Just $ f ty parts
              | idKey (intr ^. intrInst . inDefId) == ["core", "clone", "Clone", "clone_from"] -> do
                f <- use $ customOps . cloneFromShimOp
                return $ Just $ f ty parts
              | otherwise -> mirFail $
                    "don't know how to generate CloneShim for unknown method " ++
                    show (intr ^. intrInst . inDefId)
            IkVirtual _traitDefId idx
              | idKey (intr ^. intrInst . inDefId) == ["core", "ops", "function", "FnOnce", "call_once"] -> do
                f <- use $ customOps . callOnceVirtShimOp
                return $ Just $ f idx
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


-----------------------------------------------------------------------
-- ** MIR intrinsics Generator interaction

newMirRef ::
  C.TypeRepr tp ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
newMirRef tp = G.extensionStmt (MirNewRef tp)

integerToMirRef ::
  R.Expr MIR s UsizeType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
integerToMirRef i = G.extensionStmt (MirIntegerToRef i)

globalMirRef ::
  G.GlobalVar tp ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
globalMirRef gv = G.extensionStmt (MirGlobalRef gv)

constMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s tp ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
constMirRef tpr v = G.extensionStmt (MirConstRef tpr v)

dropMirRef ::
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret ()
dropMirRef refExp = void $ G.extensionStmt (MirDropRef refExp)

readMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s tp)
readMirRef tp refExp = G.extensionStmt (MirReadRef tp refExp)

writeMirRef ::
  C.TypeRepr tp ->
  R.Expr MIR s MirReferenceType ->
  R.Expr MIR s tp ->
  MirGenerator h s ret ()
writeMirRef tp ref x = void $ G.extensionStmt (MirWriteRef tp ref x)

subfieldRef ::
  C.CtxRepr ctx ->
  R.Expr MIR s MirReferenceType ->
  Index ctx tp ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
subfieldRef ctx ref idx = G.extensionStmt (MirSubfieldRef ctx ref idx)

-- | Extend the reference path encapsulated in the provided @Expr MIR s
-- MirReferenceType@ (i.e. @ref@), which should terminate in a struct, to
-- terminate at the @fieldNum@th field of that struct. If @expectedTy@ is
-- provided, then it will be asserted (via `subfieldMirRef_UntypedLeaf`) to
-- match the observed type of the field during simulation.
--
-- Essentially an untyped/dynamically-typed version of `subfieldRef` that infers
-- the appropriate struct context and field type when they aren't statically
-- known/knowable - e.g. for structs containing trait objects.
subfieldRef_Untyped ::
  R.Expr MIR s MirReferenceType ->
  Int ->
  Maybe (Some C.TypeRepr) ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
subfieldRef_Untyped ref fieldNum expectedTy = G.extensionStmt (MirSubfieldRef_Untyped ref fieldNum expectedTy)

subvariantRef ::
  C.TypeRepr discrTp ->
  C.CtxRepr variantsCtx ->
  R.Expr MIR s MirReferenceType ->
  Index variantsCtx tp ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
subvariantRef tp ctx ref idx = G.extensionStmt (MirSubvariantRef tp ctx ref idx)

subindexRef ::
  C.TypeRepr tp ->
  R.Expr MIR s MirReferenceType ->
  R.Expr MIR s UsizeType ->
  -- | Size of the element, in bytes
  Word ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
subindexRef tp ref idx elemSize = G.extensionStmt (MirSubindexRef tp ref idx elemSize)

subjustRef ::
  C.TypeRepr tp ->
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
subjustRef tp ref = G.extensionStmt (MirSubjustRef tp ref)

mirRef_agElem ::
  R.Expr MIR s UsizeType ->
  Word ->
  C.TypeRepr tp ->
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
mirRef_agElem off sz tpr ref = G.extensionStmt $ MirRef_AgElem off sz tpr ref

mirRef_agElem_constOffset ::
  Word ->
  Word ->
  C.TypeRepr tp ->
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
mirRef_agElem_constOffset off sz tpr ref =
  mirRef_agElem (R.App $ usizeLit $ fromIntegral off) sz tpr ref

mirRef_eq ::
  R.Expr MIR s MirReferenceType ->
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s C.BoolType)
mirRef_eq r1 r2 = G.extensionStmt $ MirRef_Eq r1 r2

mirRef_offset ::
  R.Expr MIR s MirReferenceType ->
  R.Expr MIR s IsizeType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
mirRef_offset ref offset = G.extensionStmt $ MirRef_Offset ref offset

mirRef_offsetWrap ::
  R.Expr MIR s MirReferenceType ->
  R.Expr MIR s IsizeType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType)
mirRef_offsetWrap ref offset = G.extensionStmt $ MirRef_OffsetWrap ref offset

mirRef_tryOffsetFrom ::
  R.Expr MIR s MirReferenceType ->
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s (C.MaybeType IsizeType))
mirRef_tryOffsetFrom r1 r2 = G.extensionStmt $ MirRef_TryOffsetFrom r1 r2

mirRef_peelIndex ::
  R.Expr MIR s MirReferenceType ->
  MirGenerator h s ret (R.Expr MIR s MirReferenceType, R.Expr MIR s UsizeType)
mirRef_peelIndex ref = do
    pair <- G.extensionStmt $ MirRef_PeelIndex ref
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


mirAggregate_uninit ::
  R.Expr MIR s UsizeType ->
  MirGenerator h s ret (R.Expr MIR s MirAggregateType)
mirAggregate_uninit sz = G.extensionStmt $ MirAggregate_Uninit sz

mirAggregate_uninit_constSize ::
  Word ->
  MirGenerator h s ret (R.Expr MIR s MirAggregateType)
mirAggregate_uninit_constSize sz = mirAggregate_uninit (R.App $ usizeLit $ fromIntegral sz)

-- | Construct a 'MirAggregate' value representing a zero-sized type (ZST) such
-- as an empty tuple or array.
mirAggregate_zst ::
  MirGenerator h s ret (R.Expr MIR s MirAggregateType)
mirAggregate_zst = mirAggregate_uninit_constSize 0

mirAggregate_replicate ::
  Word ->
  C.TypeRepr tp ->
  R.Expr MIR s tp ->
  R.Expr MIR s UsizeType ->
  MirGenerator h s ret (R.Expr MIR s MirAggregateType)
mirAggregate_replicate elemSz elemTpr elemVal lenSym =
  G.extensionStmt $ MirAggregate_Replicate elemSz elemTpr elemVal lenSym

mirAggregate_resize ::
  R.Expr MIR s MirAggregateType ->
  R.Expr MIR s UsizeType ->
  MirGenerator h s ret (R.Expr MIR s MirAggregateType)
mirAggregate_resize ag sz =
  G.extensionStmt $ MirAggregate_Resize ag sz

mirAggregate_get ::
  Word ->
  Word ->
  C.TypeRepr tp ->
  R.Expr MIR s MirAggregateType ->
  MirGenerator h s ret (R.Expr MIR s tp)
mirAggregate_get off sz tpr ag = G.extensionStmt $ MirAggregate_Get off sz tpr ag

mirAggregate_set ::
  Word ->
  Word ->
  C.TypeRepr tp ->
  R.Expr MIR s tp ->
  R.Expr MIR s MirAggregateType ->
  MirGenerator h s ret (R.Expr MIR s MirAggregateType)
mirAggregate_set off sz tpr val ag = G.extensionStmt $ MirAggregate_Set off sz tpr val ag

getTypeId :: Ty -> MirGenerator h s ret Int
getTypeId ty = do
    m <- use (cs . tyIdMap)
    case Map.lookup ty m of
      Just tyId -> pure tyId
      Nothing -> P.panic
            "getTypeId"
            ["No type_id allocated for type: " ++ show ty]

getNeedsDrop :: Ty -> MirGenerator h s ret Bool
getNeedsDrop ty = do
    s <- use (cs . collection . needDrops)
    pure (Set.member ty s)

--  LocalWords:  ty ImplementTrait ctx vtable idx runtime struct
--  LocalWords:  vtblToStruct
