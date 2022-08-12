{-
Module           : UCCrux.LLVM.View.TH
Description      : Helpers for deriving JSON instances with TemplateHaskell
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

module UCCrux.LLVM.View.TH
  ( deriveMutualJSON
  )
where

import           Control.Monad (foldM)
import qualified Data.Aeson.TH as Aeson.TH
import           Data.Aeson.TH (Options)
import           Language.Haskell.TH (Dec, Q, Name)

-- | Like 'Aeson.TH.deriveJSON' but processes mutliple types in the same splice,
-- and so can be used for mutually recursive types.
deriveMutualJSON ::
  [(Options, Name)] ->
  Q [Dec]
deriveMutualJSON =
  foldM (\decs (opts, nm) -> (decs ++) <$> Aeson.TH.deriveJSON opts nm) []
