{-
Module       : UCCrux.LLVM.Newtypes.FunctionName
Description  : Newtype for names of functions
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module UCCrux.LLVM.Newtypes.FunctionName
  ( FunctionName
  , functionNameToString
  , functionNameFromString
  )
where

import qualified Data.Aeson as Aeson
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Data (Data)
import           GHC.Generics (Generic)

newtype FunctionName = FunctionName { functionNameToString :: String }
  deriving (Data, Eq, Aeson.FromJSONKey, Generic, Ord, Show)

-- | Inverse of 'functionNameToString'
functionNameFromString :: String -> FunctionName
functionNameFromString = FunctionName

$(Aeson.TH.deriveJSON Aeson.defaultOptions ''FunctionName)
