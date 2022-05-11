{-
Module           : UCCrux.LLVM.FullType.FuncSig
Description      : Typing function signatures
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

By having a separate notion of \"return type\", 'FullType' doesn't need to have
a \"void\" constructor, which avoids some de-normalization/partiality
elsewhere.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.FullType.FuncSig
  ( -- * Return type
    type ReturnType (..),
    ReturnTypeToCrucibleType,
    ReturnTypeRepr (..),
    mkReturnTypeRepr,
    -- * Function signatures
    FuncSig,
    FuncSigRepr(..),
  )
where

{- ORMOLU_DISABLE -}
import           Data.Kind (Type)

import           Data.Parameterized.Classes (OrdF(compareF))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TH.GADT as U
import           Data.Type.Equality (TestEquality(testEquality))

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           UCCrux.LLVM.FullType.Type
import           UCCrux.LLVM.FullType.VarArgs
{- ORMOLU_ENABLE -}

-- | Type-level only
data ReturnType (m :: Type) (mft :: Maybe (FullType m)) where
  Void :: ReturnType m 'Nothing
  NonVoid :: FullTypeRepr m ft -> ReturnType m ('Just ft)

type family ReturnTypeToCrucibleType arch (mft :: Maybe (FullType m)) where
  ReturnTypeToCrucibleType arch 'Nothing = CrucibleTypes.UnitType
  ReturnTypeToCrucibleType arch ('Just ft) = ToCrucibleType arch ft

data ReturnTypeRepr (m :: Type) (mft :: Maybe (FullType m)) where
  VoidRepr :: ReturnTypeRepr m 'Nothing
  NonVoidRepr :: FullTypeRepr m ft -> ReturnTypeRepr m ('Just ft)

mkReturnTypeRepr :: Maybe (Some (FullTypeRepr m)) -> Some (ReturnTypeRepr m)
mkReturnTypeRepr =
  \case
    Nothing -> Some VoidRepr
    Just (Some ftRepr) -> Some (NonVoidRepr ftRepr)

-- | Type-level only
data FuncSig m where
  FuncSig ::
    IsVarArgs ->
    Maybe (FullType m) ->
    Ctx.Ctx (FullType m) ->
    FuncSig m

data FuncSigRepr m (fs :: FuncSig m) where
  FuncSigRepr ::
    VarArgsRepr varArgs ->
    Ctx.Assignment (FullTypeRepr m) args ->
    ReturnTypeRepr m ret ->
    FuncSigRepr m ('FuncSig varArgs ret args)

-- ------------------------------------------------------------------------------
-- Instances

$(return [])

instance TestEquality (ReturnTypeRepr m) where
  testEquality =
    $( U.structuralTypeEquality
         [t|ReturnTypeRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 )
               ]
         )
     )

instance OrdF (ReturnTypeRepr m) where
  compareF =
    $( U.structuralTypeOrd
         [t|ReturnTypeRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 )
               ]
         )
     )

instance TestEquality (FuncSigRepr m) where
  testEquality =
    $( U.structuralTypeEquality
         [t|FuncSigRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|ReturnTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (U.ConType [t|VarArgsRepr|]),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|testEquality|]
                 )
               ]
         )
     )

instance OrdF (FuncSigRepr m) where
  compareF =
    $( U.structuralTypeOrd
         [t|FuncSigRepr|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (U.ConType [t|VarArgsRepr|]),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|ReturnTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (U.ConType [t|Ctx.Assignment|])),
                   [|compareF|]
                 )
               ]
         )
     )
