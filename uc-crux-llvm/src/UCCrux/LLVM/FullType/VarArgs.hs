{-
Module           : UCCrux.LLVM.FullType.VarArgs
Description      : Type-level indication of whether a function is variadic
Copyright        : (c) Galois, Inc 2021
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module UCCrux.LLVM.FullType.VarArgs
  ( type IsVarArgs (..),
    VarArgsRepr (..),
    boolToVarArgsRepr,
    varArgsReprToBool,
  )
where

{- ORMOLU_DISABLE -}
import           Data.Type.Equality (TestEquality(testEquality))

import           Data.Parameterized.Classes (OrdF(compareF))
import           Data.Parameterized.Some (Some(Some))
import qualified Data.Parameterized.TH.GADT as U
{- ORMOLU_ENABLE -}

-- | Type level only.
data IsVarArgs
  = IsVarArgs
  | NotVarArgs

data VarArgsRepr (varArgs :: IsVarArgs) where
  IsVarArgsRepr :: VarArgsRepr 'IsVarArgs
  NotVarArgsRepr :: VarArgsRepr 'NotVarArgs

boolToVarArgsRepr :: Bool -> Some VarArgsRepr
boolToVarArgsRepr True = Some IsVarArgsRepr
boolToVarArgsRepr False = Some NotVarArgsRepr

varArgsReprToBool :: VarArgsRepr varArgs -> Bool
varArgsReprToBool IsVarArgsRepr = True
varArgsReprToBool NotVarArgsRepr = False

-- ------------------------------------------------------------------------------
-- Instances

$(return [])

instance TestEquality VarArgsRepr where
  testEquality = $(U.structuralTypeEquality [t|VarArgsRepr|] [])

instance OrdF VarArgsRepr where
  compareF = $(U.structuralTypeOrd [t|VarArgsRepr|] [])
