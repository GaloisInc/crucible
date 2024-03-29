{-
Module           : Lang.Crucible.LLVM.Syntax.TypeAlias
Copyright        : (c) Galois, Inc 2023
Maintainer       : Langston Barrett <langston@galois.com>
License          : BSD3

This module provides facilities for parsing C-like types and translating them
to appropriate Crucible-LLVM types, given a target triple. For example, the
syntax @Long@ is parsed as the Crucible-LLVM 64-bit bitvector type for the
x86_64 Linux target ('x86_64LinuxTypes'), but the 32-bit bitvector type for 
32-bit ARM Linux targets ('aarch32LinuxTypes'). This can be useful if you want
to write Crucible CFGs that can be simulated in the context of LLVM modules
for several different architectures, for example if you want to override system
calls.
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Lang.Crucible.LLVM.Syntax.TypeAlias
  ( TypeAlias(..)
  , TypeLookup(..)
  , aarch32LinuxTypes
  , x86_64LinuxTypes
  , typeAliasParser
  , typeAliasParserHooks
  ) where

import           Control.Applicative ( Alternative(empty) )
import qualified Data.Map as Map
import qualified Data.Text as Text

import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )

import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.Monad as LCSM
import qualified Lang.Crucible.Types as LCT

-- | Additional types beyond those built into crucible-llvm-syntax.
data TypeAlias = Byte | Int | Long | PidT | Pointer | Short | SizeT | UidT
  deriving (Bounded, Enum, Eq, Show)

-- | Lookup function from a 'TypeAlias' to the underlying crucible type it
-- represents.
newtype TypeLookup = TypeLookup (TypeAlias -> (Some LCT.TypeRepr))

-- | A lookup function from 'TypeAlias' to types with the appropriate width
-- on Arm32 Linux.
aarch32LinuxTypes :: TypeLookup
aarch32LinuxTypes = 
  TypeLookup $
    \case
      Byte -> Some (LCT.BVRepr (PN.knownNat @8))
      Int -> Some (LCT.BVRepr (PN.knownNat @32))
      Long -> Some (LCT.BVRepr (PN.knownNat @32))
      PidT -> Some (LCT.BVRepr (PN.knownNat @32))
      Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @32))
      Short -> Some (LCT.BVRepr (PN.knownNat @16))
      SizeT -> Some (LCT.BVRepr (PN.knownNat @32))
      UidT -> Some (LCT.BVRepr (PN.knownNat @32))

-- | A lookup function from 'TypeAlias' to types with the appropriate width on
-- X86_64 Linux.
x86_64LinuxTypes :: TypeLookup
x86_64LinuxTypes =
  TypeLookup $
    \case
      Byte -> Some (LCT.BVRepr (PN.knownNat @8))
      Int -> Some (LCT.BVRepr (PN.knownNat @32))
      Long -> Some (LCT.BVRepr (PN.knownNat @64))
      PidT -> Some (LCT.BVRepr (PN.knownNat @32))
      Pointer -> Some (LCLM.LLVMPointerRepr (PN.knownNat @64))
      Short -> Some (LCT.BVRepr (PN.knownNat @16))
      SizeT -> Some (LCT.BVRepr (PN.knownNat @64))
      UidT -> Some (LCT.BVRepr (PN.knownNat @32))
      
-- | Parser for type extensions to Crucible syntax
typeMapParser :: 
  LCSM.MonadSyntax LCSA.Atomic m =>
  -- | A mapping from type names to the crucible types they represent
  Map.Map LCSA.AtomName (Some LCT.TypeRepr) ->
  m (Some LCT.TypeRepr)
typeMapParser types = do
  name <- LCSC.atomName
  case Map.lookup name types of
    Just someTypeRepr -> return someTypeRepr
    Nothing -> empty

-- | Parser for type aliases for the Crucible-LLVM syntax
typeAliasParser :: 
  LCSM.MonadSyntax LCSA.Atomic m =>
  TypeLookup ->
  m (Some LCT.TypeRepr)
typeAliasParser (TypeLookup lookupFn) =
  typeMapParser $
    Map.fromList
      [ (LCSA.AtomName (Text.pack (show t)), lookupFn t)
      | t <- [minBound..maxBound]
      ]

-- | Parser hooks with 'LCSC.extensionTypeParser' set to 'typeAliasParser'
typeAliasParserHooks :: TypeLookup -> LCSC.ParserHooks ext
typeAliasParserHooks lookupFn =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser = typeAliasParser lookupFn
  , LCSC.extensionParser = empty
  }
