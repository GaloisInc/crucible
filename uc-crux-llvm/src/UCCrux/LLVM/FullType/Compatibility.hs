{-
Module           : UCCrux.LLVM.FullType.Compatibility
Description      : Type compatibility
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.FullType.Compatibility
  ( CompatTypes(..),
  )
where

{- ORMOLU_DISABLE -}
import           Data.Maybe (isJust)
import           Data.Type.Equality (TestEquality(testEquality))

import           Data.Parameterized.Classes (OrdF(compareF))
import           Data.Parameterized.NatRepr (knownNat)
import qualified Data.Parameterized.TH.GADT as U

import           UCCrux.LLVM.FullType.Type (FullType(FTInt, FTPtr), FullTypeRepr)
import qualified UCCrux.LLVM.FullType.Type as FT
{- ORMOLU_ENABLE -}

data CompatTypes m (ft1 :: FullType m) (ft2 :: FullType m) where
  -- Base case

  CompatRefl :: FullTypeRepr m ft -> CompatTypes m ft ft

  -- Boring recursive cases

  CompatPtr ::
    CompatTypes m ft1 ft2 ->
    CompatTypes m ('FTPtr ft1) ('FTPtr ft2)

  -- Interesting cases

  -- | Any pointer is compatible with a @void*@ or @char*@
  CompatBytes ::
    FullTypeRepr m ft ->
    CompatTypes m ('FTPtr ('FTInt 8)) ('FTPtr ft)

instance Eq (CompatTypes m ft1 ft2) where
  ct1 == ct2 = isJust (testEquality ct1 ct2)

compatReprL ::
  CompatTypes m ft1 ft2 ->
  FullTypeRepr m ft1
compatReprL =
  \case
    CompatRefl repr -> repr
    CompatPtr compat ->
      FT.FTPtrRepr (FT.toPartType (compatReprL compat))
    CompatBytes _ ->
      FT.FTPtrRepr (FT.toPartType (FT.FTIntRepr knownNat))

compatReprR ::
  CompatTypes m ft1 ft2 ->
  FullTypeRepr m ft2
compatReprR =
  \case
    CompatRefl repr -> repr
    CompatPtr compat ->
      FT.FTPtrRepr (FT.toPartType (compatReprR compat))
    CompatBytes repr -> FT.FTPtrRepr (FT.toPartType repr)

$(return [])

instance TestEquality (CompatTypes m ft1) where
  testEquality =
    $( U.structuralTypeEquality
         [t|CompatTypes|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|testEquality|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|CompatTypes|]))),
                   [|testEquality|]
                 )
               ]
         )
     )

instance OrdF (CompatTypes m ft1) where
  compareF =
    $( U.structuralTypeOrd
         [t|CompatTypes|]
         ( let appAny con = U.TypeApp con U.AnyType
            in [ ( appAny (appAny (U.ConType [t|FullTypeRepr|])),
                   [|compareF|]
                 ),
                 ( appAny (appAny (appAny (U.ConType [t|CompatTypes|]))),
                   [|compareF|]
                 )
               ]
         )
     )
