module SAWScript.TypedTerm where

import qualified Cryptol.TypeCheck.AST as C

import Verifier.SAW.Cryptol (scCryptolType)
import Verifier.SAW.SharedTerm


data TypedTerm s = TypedTerm C.Schema (SharedTerm s)

mkTypedTerm :: SharedContext s -> SharedTerm s -> IO (TypedTerm s)
mkTypedTerm sc trm = do
  ty <- scTypeOf sc trm
  ct <- scCryptolType sc ty
  return $ TypedTerm (C.Forall [] [] ct) trm
