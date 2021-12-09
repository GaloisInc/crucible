{-
Module           : UCCrux.LLVM.Newtypes.PreSimulationMem
Copyright        : (c) Galois, Inc 2020
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

module UCCrux.LLVM.Newtypes.PreSimulationMem
  ( PreSimulationMem
  , makePreSimulationMem
  , getPreSimulationMem
  ) where

import           Lang.Crucible.LLVM.MemModel (MemImpl)

-- | LLVM memory just before symbolic execution. Populated with globals, defined
-- functions, and arguments to the entry point.
newtype PreSimulationMem sym =
  PreSimulationMem { getPreSimulationMem :: MemImpl sym }

makePreSimulationMem :: MemImpl sym -> PreSimulationMem sym
makePreSimulationMem = PreSimulationMem
