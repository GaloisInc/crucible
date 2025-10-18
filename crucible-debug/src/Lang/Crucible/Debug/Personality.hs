{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Lang.Crucible.Debug.Personality
  ( HasContext(..)
  , prepend
  , quit
  , stop
  ) where

import Control.Lens qualified as Lens
import Data.Function ((&))
import Lang.Crucible.Debug.Context (Context)
import Lang.Crucible.Debug.Context qualified as Ctxt
import Lang.Crucible.Debug.Inputs qualified as Inps
import Lang.Crucible.Debug.Statement (Statement)
import Lang.Crucible.Simulator.ExecutionTree qualified as C

-- | A class for Crucible personality types @p@ (see
-- 'Lang.Crucible.Simulator.ExecutionTree.cruciblePersonality') which contain a
-- 'Context'. This execution feature is polymorphic over the personality so that
-- downstream users can supply their own personality types that extend 'Context'
-- further.
class HasContext p cExt sym ext t | p -> cExt sym ext t where
  context :: Lens.Lens' p (Context cExt sym ext t)

instance HasContext (Context cExt sym ext t) cExt sym ext t where
  context = id
  {-# INLINE context #-}

-- | 'Inps.prepend' some 'Statements' to the debugger inputs
prepend ::
  HasContext p cExt sym ext t =>
  [Statement cExt] ->
  C.SimContext p sym ext ->
  IO (C.SimContext p sym ext)
prepend stmts simCtx = do
  let inps =
        simCtx Lens.^. C.cruciblePersonality . context . Lens.to Ctxt.dbgInputs
  inps' <- Inps.prepend stmts inps
  pure $
    simCtx &
      C.cruciblePersonality . context Lens.%~
      \c -> c { Ctxt.dbgInputs = inps' }

-- | Cause the debugger to transition to the 'Ctxt.Quit' state.
quit ::
  HasContext p cExt sym ext t =>
  C.SimContext p sym ext ->
  C.SimContext p sym ext
quit simCtx =
  simCtx &
    C.cruciblePersonality . context Lens.%~
    \c -> c { Ctxt.dbgState = Ctxt.Quit }

-- | Cause the debugger to transition to the 'Ctxt.Stopped' state.
--
-- This can be used to reactive the debugger after it has been quit.
stop ::
  HasContext p cExt sym ext t =>
  C.SimContext p sym ext ->
  C.SimContext p sym ext
stop simCtx =
  simCtx &
    C.cruciblePersonality . context Lens.%~
    \c -> c { Ctxt.dbgState = Ctxt.Stopped }
