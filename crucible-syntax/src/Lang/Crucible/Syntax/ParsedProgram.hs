module Lang.Crucible.Syntax.ParsedProgram
  ( ParsedProgram(..)
  , parsedProgramFnBindings
  ) where

import Data.Map.Strict (Map)
import Data.Parameterized.Some (Some)
import Lang.Crucible.Analysis.Postdom (postdomInfo)
import Lang.Crucible.CFG.Core (SomeCFG(SomeCFG), cfgHandle)
import Lang.Crucible.CFG.Extension (IsSyntaxExtension)
import Lang.Crucible.CFG.Generator (GlobalVar)
import Lang.Crucible.CFG.Reg (AnyCFG(AnyCFG))
import Lang.Crucible.CFG.SSAConversion (toSSA)
import Lang.Crucible.FunctionHandle (SomeHandle)
import Lang.Crucible.Simulator (FnBinding (FnBinding))
import Lang.Crucible.Simulator.ExecutionTree (FnState(UseCFG))
import Lang.Crucible.Syntax.Atoms (GlobalName)
import What4.FunctionName (FunctionName)

-- | The results of parsing a program.
data ParsedProgram ext = ParsedProgram
  { parsedProgGlobals :: Map GlobalName (Some GlobalVar)
    -- ^ The parsed @defglobal@s.
  , parsedProgExterns :: Map GlobalName (Some GlobalVar)
    -- ^ For each parsed @extern@, map its name to its global variable. It is
    --   the responsibility of the caller to insert each global variable into
    --   the 'SymGlobalState' alongside an appropriate 'RegValue'.
  , parsedProgCFGs :: [AnyCFG ext]
    -- ^ The CFGs for each parsed @defun@.
  , parsedProgForwardDecs :: Map FunctionName SomeHandle
    -- ^ For each parsed @declare@, map its name to its function handle. It is
    --   the responsibility of the caller to register each handle with an
    --   appropriate 'FnState'.
  }

-- | Create a 'FnBinding' for each @defun@ CFG in the 'ParsedProgram'.
parsedProgramFnBindings ::
  IsSyntaxExtension ext =>
  ParsedProgram ext ->
  [FnBinding p sym ext]
parsedProgramFnBindings prog = map mkBinding (parsedProgCFGs prog)
  where
    mkBinding (AnyCFG defCfg) =
      case toSSA defCfg of
        SomeCFG defSsa ->
          FnBinding (cfgHandle defSsa) (UseCFG defSsa (postdomInfo defSsa))
