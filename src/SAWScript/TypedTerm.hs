{- |
Module           : $Header$
Description      :
License          : Free for non-commercial use. See LICENSE.
Stability        : provisional
Point-of-contact : huffman
-}
module SAWScript.TypedTerm where

import Data.Map (Map)
import qualified Data.Map as Map

import Cryptol.ModuleSystem.Name (nameIdent)
import qualified Cryptol.TypeCheck.AST as C
import Cryptol.Utils.PP (pretty)

import Verifier.SAW.Cryptol (scCryptolType)
import Verifier.SAW.SharedTerm

-- Typed terms -----------------------------------------------------------------

{- Within SAWScript, we represent an object language term as a SAWCore
shared term paired with a Cryptol type schema. The Cryptol type is
used for type inference/checking of inline Cryptol expressions. -}

data TypedTerm s =
  TypedTerm
  { ttSchema :: C.Schema
  , ttTerm :: SharedTerm s
  }

mkTypedTerm :: SharedContext s -> SharedTerm s -> IO (TypedTerm s)
mkTypedTerm sc trm = do
  ty <- scTypeOf sc trm
  ct <- scCryptolType sc ty
  return $ TypedTerm (C.Forall [] [] ct) trm

-- Typed modules ---------------------------------------------------------------

{- In SAWScript, we can refer to a Cryptol module as a first class
value. These are represented simply as maps from names to typed
terms. -}

newtype CryptolModule s = CryptolModule (Map C.Name (TypedTerm s))

showCryptolModule :: CryptolModule s -> String
showCryptolModule (CryptolModule m) =
  unlines ("Symbols" : "=======" : map showBinding (Map.assocs m))
  where
    showBinding (name, TypedTerm schema _) =
      "    " ++ pretty (nameIdent name) ++ " : " ++ pretty schema
