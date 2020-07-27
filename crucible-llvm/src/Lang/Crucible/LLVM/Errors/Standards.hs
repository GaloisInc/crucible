-- |
-- Module           : Lang.Crucible.LLVM.Errors.Standards
-- Description      : Standards documents
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Langston Barrett <lbarrett@galois.com>
-- Stability        : provisional
--
--------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE Safe #-}

module Lang.Crucible.LLVM.Errors.Standards
  ( Standard(..)
  , CStdVer(..)
  , CXXStdVer(..)
  , LLVMRefVer(..)
  , ppStd
  , stdURL
  ) where

import           Prelude hiding (unwords, unlines)

import           Data.Data (Data)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)

import           Data.Text (Text, pack)

-- | The various standards that prohibit certain behaviors
data Standard =
    CStd    CStdVer    -- ^ The C language standard
  | CXXStd  CXXStdVer  -- ^ The C++ language standard
  | LLVMRef LLVMRefVer -- ^ The LLVM language reference
  deriving (Data, Eq, Generic, Ord, Read, Show, Typeable)

-- | Versions of the C standard
data CStdVer =
    C99
  | C11
  | C18
  deriving (Data, Eq, Enum, Generic, Ord, Read, Show, Typeable)

-- | Versions of the C++ standard
data CXXStdVer =
    CXX03
  | CXX11
  | CXX14
  | CXX17
  deriving (Data, Eq, Enum, Generic, Ord, Read, Show, Typeable)

ppCXXStdVer :: CXXStdVer -> Text
ppCXXStdVer CXX03 = "C++03"
ppCXXStdVer CXX11 = "C++11"
ppCXXStdVer CXX14 = "C++14"
ppCXXStdVer CXX17 = "C++17"

-- | Versions of the LLVM Language Reference
data LLVMRefVer =
    LLVM38
  | LLVM4
  | LLVM5
  | LLVM6
  | LLVM7
  | LLVM8
  deriving (Data, Eq, Enum, Generic, Ord, Read, Show, Typeable)

ppLLVMRefVer :: LLVMRefVer -> Text
ppLLVMRefVer LLVM38 = "3.8"
ppLLVMRefVer LLVM4  = "4"
ppLLVMRefVer LLVM5  = "5"
ppLLVMRefVer LLVM6  = "6"
ppLLVMRefVer LLVM7  = "7"
ppLLVMRefVer LLVM8  = "8"

stdURL :: Standard -> Maybe Text
stdURL (CStd   C99)     = Just "http://www.iso-9899.info/n1570.html"
stdURL (CXXStd CXX17)   = Just "http://www.open-std.org/jtc1/sc22/wg14/www/abq/c17_updated_proposed_fdis.pdf"
stdURL (LLVMRef LLVM38) = Just "https://releases.llvm.org/3.8.0/docs/LangRef.html"
stdURL (LLVMRef LLVM4)  = Just "https://releases.llvm.org/4.0.1/docs/LangRef.html"
stdURL (LLVMRef LLVM5)  = Just "https://releases.llvm.org/5.0.0/docs/LangRef.html"
stdURL (LLVMRef LLVM6)  = Just "https://releases.llvm.org/6.0.0/docs/LangRef.html"
stdURL (LLVMRef LLVM7)  = Just "https://releases.llvm.org/7.0.0/docs/LangRef.html"
stdURL (LLVMRef LLVM8)  = Just "https://releases.llvm.org/8.0.0/docs/LangRef.html"
stdURL _                = Nothing

ppStd :: Standard -> Text
ppStd =
  \case
    CStd    ver -> "The C language standard, version "     <> pack (show ver)
    CXXStd  ver -> "The C++ language standard, version "   <> ppCXXStdVer ver
    LLVMRef ver -> "The LLVM language reference, version " <> ppLLVMRefVer ver
