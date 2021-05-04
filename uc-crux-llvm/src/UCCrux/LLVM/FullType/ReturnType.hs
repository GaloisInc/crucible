{-
Module           : UCCrux.LLVM.FullType.ReturnType
Description      : TODO
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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module UCCrux.LLVM.FullType.ReturnType
  ( ReturnType (..),
    ReturnTypeToCrucibleType,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Kind (Type)

import qualified Lang.Crucible.Types as CrucibleTypes hiding ((::>))

import           UCCrux.LLVM.FullType.Type
{- ORMOLU_ENABLE -}

data ReturnType (m :: Type) (ft :: Maybe (FullType m)) where
  Void :: ReturnType m 'Nothing
  NonVoid :: FullTypeRepr m ft -> ReturnType m ('Just ft)

type family ReturnTypeToCrucibleType arch (ft :: Maybe (FullType m)) where
  ReturnTypeToCrucibleType arch 'Nothing = CrucibleTypes.UnitType
  ReturnTypeToCrucibleType arch ('Just ft) = ToCrucibleType arch ft
