{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

{-
Module       : UCCrux.LLVM.Postcondition.Type
Description  : Postconditions for LLVM functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional

A postcondition for a function summarizes its return value and its effect of a
function on LLVM memory. Of course, the most complete summary of a function is
semantically equivalent to its implementation. The postconditions in this module
are significantly less expressive than that. The aims are to support
postcondition inference, and to support partial (user- or programmer-supplied)
specifications of external functions.

'ClobberGlobal' and 'ClobberArg' can explicitly set a type of data to generate,
which may or may not actually match the declared type of the data in question.
This is useful for clobbering e.g. a @char*@ or @void*@ with structured data.
However, it yields some API and implementation complexity due to possible type
mismatches (see 'OpaquePointers').
-}

module UCCrux.LLVM.Postcondition.Type
  ( ClobberValue(..)
  , SomeClobberValue(..)
  , ppClobberValue
  , ClobberArg(..)
  , SomeClobberArg(..)
  , UPostcond(..)
  , uArgClobbers
  , uGlobalClobbers
  , uReturnValue
  , emptyUPostcond
  , minimalUPostcond
  , ppUPostcond
  , Postcond(..)
  , PostcondTypeError
  , ppPostcondTypeError
  , typecheckPostcond
  , ReturnValue(..)
  )
where

import           Control.Lens (Lens', (^.))
import qualified Control.Lens as Lens
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Type.Equality ((:~:)(Refl), testEquality)
import           Data.Void (Void)

import qualified Prettyprinter as PP

import           Data.Parameterized.Classes (IxedF'(ixF'))
import           Data.Parameterized.Context (Assignment)
import qualified Data.Parameterized.Context as Ctx

import           UCCrux.LLVM.Constraints (ConstrainedShape, ConstrainedTypedValue (ConstrainedTypedValue), minimalConstrainedShape, ppConstrainedShape)
import           UCCrux.LLVM.Cursor (Cursor, ppCursor)
import           UCCrux.LLVM.FullType.FuncSig (FuncSig, FuncSigRepr, ReturnTypeRepr)
import qualified UCCrux.LLVM.FullType.FuncSig as FS
import           UCCrux.LLVM.FullType.PP (ppFullTypeRepr)
import           UCCrux.LLVM.FullType.Type (FullType(FTPtr), FullTypeRepr, OpaquePointers, testOpaquePointers)
import           UCCrux.LLVM.FullType.VarArgs (VarArgsRepr)
import           UCCrux.LLVM.Module (GlobalSymbol, getGlobalSymbol)

-- | Specification of how a (part of a) value is clobbered, i.e., which parts to
-- write to and with what data.
--
-- Note that the freshly-generated value may be of a different type (@realTy@)
-- than the value being overwritten, see the module comment.
data ClobberValue m (inTy :: FullType m) =
  forall realTy atTy.
  OpaquePointers realTy ~ OpaquePointers inTy =>
  ClobberValue
  { -- | Location of pointer within container value
    clobberValueCursor :: Cursor m realTy ('FTPtr atTy),
    -- | Specification of value to write to the pointer
    clobberValue :: ConstrainedShape m atTy,
    -- | Type of the container value
    clobberValueType :: FullTypeRepr m realTy
  }

data SomeClobberValue m = forall inTy. SomeClobberValue (ClobberValue m inTy)

ppClobberValue :: ClobberValue m inTy -> PP.Doc ann
ppClobberValue (ClobberValue cur val ty) =
  PP.hsep
    [ ppCursor (show (ppConstrainedShape val)) cur
    , ":"
    , ppFullTypeRepr ty
    ]

-- | Specification of how a (part of a) pointer argument is clobbered, i.e.,
-- which parts to write to and with what data.
data ClobberArg m (inTy :: FullType m) where
  DontClobberArg :: ClobberArg m inTy
  DoClobberArg :: ClobberValue m inTy -> ClobberArg m inTy

data SomeClobberArg m = forall inTy. SomeClobberArg (ClobberArg m inTy)

-- | Untyped postcondition of an LLVM function.
--
-- The U stands for untyped, see 'Postcond'.
--
-- NOTE(lb): The explicit kind signature here is necessary for GHC 8.8
-- compatibility.
data UPostcond m = UPostcond
  { -- | Specifications of which pointer arguments are written to, and how
    _uArgClobbers :: IntMap (SomeClobberArg m),
    -- | Specifications of which global variables are written to, and how
    _uGlobalClobbers :: Map (GlobalSymbol m) (SomeClobberValue m),
    -- | Specification of the return value
    _uReturnValue :: Maybe (ConstrainedTypedValue m)
  }

uArgClobbers :: Lens' (UPostcond m) (IntMap (SomeClobberArg m))
uArgClobbers = Lens.lens _uArgClobbers (\s v -> s { _uArgClobbers = v })

uGlobalClobbers :: Lens' (UPostcond m) (Map (GlobalSymbol m) (SomeClobberValue m))
uGlobalClobbers = Lens.lens _uGlobalClobbers (\s v -> s { _uGlobalClobbers = v })

uReturnValue :: Lens' (UPostcond m) (Maybe (ConstrainedTypedValue m))
uReturnValue = Lens.lens _uReturnValue (\s v -> s { _uReturnValue = v })

-- | A postcondition which imposes no constraints and has a no return value (is
-- void).
emptyUPostcond :: UPostcond m
emptyUPostcond =
  UPostcond
    { _uArgClobbers = IntMap.empty,
      _uGlobalClobbers = Map.empty,
      _uReturnValue = Nothing
    }

-- | A postcondition which imposes no constraints and has some
-- minimally-constrained return value.
minimalUPostcond :: ReturnTypeRepr m ft -> UPostcond m
minimalUPostcond retRepr =
  UPostcond
    { _uArgClobbers = IntMap.empty,
      _uGlobalClobbers = Map.empty,
      _uReturnValue =
        case retRepr of
          FS.VoidRepr -> Nothing
          FS.NonVoidRepr ft ->
            Just (ConstrainedTypedValue ft (minimalConstrainedShape ft))
    }

ppUPostcond :: UPostcond m -> PP.Doc Void
ppUPostcond post =
  PP.vsep $ bullets
    [ "Return value:" PP.<+>
        case _uReturnValue post of
          Just (ConstrainedTypedValue _type shape) -> ppConstrainedShape shape
          Nothing -> "<void>"
    , header
        "Argument clobbers:"
        (map (uncurry ppArg) (IntMap.toList (_uArgClobbers post)))
    , header
        "Global clobbers:"
        (map (uncurry ppGlob) (Map.toList (_uGlobalClobbers post)))
    ]
  where
    bullets = map ("-" PP.<+>)
    header hd items = PP.nest 2 (PP.vsep (hd : bullets items))

    ppArg i (SomeClobberArg ca) =
      (PP.viaShow i <> ":") PP.<+>
        case ca of
          DontClobberArg -> "no clobbering"
          DoClobberArg cv -> ppClobberValue cv

    ppGlob gSymb (SomeClobberValue cv) =
      (PP.viaShow (getGlobalSymbol gSymb) <> ":") PP.<+> ppClobberValue cv

data ReturnValue m mft f where
  ReturnVoid :: ReturnValue m 'Nothing f
  ReturnValue :: f ft -> ReturnValue m ('Just ft) f

-- | A more strongly typed version of 'UPostcond'.
data Postcond m (fs :: FuncSig m) where
  Postcond ::
    { pVarArgs :: VarArgsRepr va,
      -- | Specifications of which pointer arguments are written to, and how
      pArgClobbers :: Assignment (ClobberArg m) argTypes,
      -- | Specifications of which global variables are written to, and how
      pGlobalClobbers :: Map (GlobalSymbol m) (SomeClobberValue m),
      -- | Specification of the return value
      pReturnValue :: ReturnValue m mft (ConstrainedShape m)
    } ->
    Postcond m ('FS.FuncSig va mft argTypes)

data PostcondTypeError
  = PostcondMismatchedSize
  | PostcondMismatchedType
  | PostcondMismatchedRet
  deriving (Eq, Ord)

ppPostcondTypeError :: PostcondTypeError -> PP.Doc ann
ppPostcondTypeError =
  \case
    PostcondMismatchedSize ->
      PP.hsep
        [ "Specification for values clobbered by the skipped function",
          "included an argument index that is out of range for that function."
        ]
    PostcondMismatchedType ->
      PP.hsep
        [ "Specification for values clobbered by the skipped function",
          "included a value that was ill-typed with respect to that function's",
          "arguments."
        ]
    PostcondMismatchedRet ->
        "Specification for return value of the skipped function was ill-typed."

-- | Check that the given untyped postcondition ('UPostcond') matches the
-- given function signature ('FuncSigRepr'), returning a strongly typed
-- postcondition ('Postcond') if so or an error if not.
typecheckPostcond ::
  (fs ~ 'FS.FuncSig va mft args) =>
  UPostcond m ->
  FuncSigRepr m fs ->
  Either PostcondTypeError (Postcond m fs)
typecheckPostcond post fs =
  do -- For each argument, check that the specified value has the right type.
     let argTypes = FS.fsArgTypes fs
     let uArgs = _uArgClobbers post
     args <-
       Ctx.generateM
       (Ctx.size argTypes)
       (\idx ->
          case IntMap.lookup (Ctx.indexVal idx) uArgs of
            Nothing -> Right DontClobberArg
            Just (SomeClobberArg DontClobberArg) -> Right DontClobberArg
            Just (SomeClobberArg (DoClobberArg (ClobberValue cur val ty))) ->
              let argType = argTypes ^. ixF' idx
              in case testOpaquePointers argType ty of
                   Just Refl -> Right (DoClobberArg (ClobberValue cur val ty))
                   Nothing -> Left PostcondMismatchedType)

     -- Check that the correct number of arguments were specified
     () <-
       if not (IntMap.null uArgs) &&
            maximum (IntMap.keys uArgs) > Ctx.sizeInt (Ctx.size argTypes)
       then Left PostcondMismatchedSize
       else Right ()

     -- Check that the return value has the right type
     ret <-
       case (FS.fsRetType fs, _uReturnValue post) of
         (FS.NonVoidRepr{}, Nothing) -> Left PostcondMismatchedRet
         (FS.VoidRepr{}, Just{}) -> Left PostcondMismatchedRet
         (FS.VoidRepr, Nothing) -> Right ReturnVoid
         (FS.NonVoidRepr ft, Just (ConstrainedTypedValue ty val)) ->
           case testEquality ft ty of
             Just Refl -> Right (ReturnValue val)
             Nothing -> Left PostcondMismatchedRet

     return $
       Postcond
         { pVarArgs = FS.fsVarArgs fs,
           pArgClobbers = args,
           pGlobalClobbers = _uGlobalClobbers post,
           pReturnValue = ret
         }
