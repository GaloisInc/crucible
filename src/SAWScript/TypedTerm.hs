module SAWScript.TypedTerm where

import Data.Map (Map)

import qualified Cryptol.TypeCheck.AST as C

import Verifier.SAW.Cryptol (scCryptolType)
import Verifier.SAW.SharedTerm

-- Typed terms -----------------------------------------------------------------

{- Within SAWScript, we represent an object language term as a SAWCore
shared term paired with a Cryptol type schema. The Cryptol type is
used for type inference/checking of inline Cryptol expressions. -}

data TypedTerm s = TypedTerm C.Schema (SharedTerm s)

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
