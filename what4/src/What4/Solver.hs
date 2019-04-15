{-|
Module      : What4.Solver
Copyright   : (c) Galois, Inc 2015-2018
License     : BSD3
Maintainer  : Rob Dockins <rdockins@galois.com>

The module reexports the most commonly used types
and operations for interacting with solvers.
-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}

module What4.Solver
  ( -- * Solver Adapters
    SolverAdapter(..)
  , ExprRangeBindings
  , defaultSolverAdapter
  , solverAdapterOptions
  , LogData(..)
  , logCallback
  , defaultLogData

    -- * Boolector
  , boolectorAdapter
  , boolectorPath
  , runBoolectorInOverride

    -- * CVC4
  , cvc4Adapter
  , cvc4Path
  , runCVC4InOverride
  , writeCVC4SMT2File
  , withCVC4

    -- * DReal
  , DRealBindings
  , drealAdapter
  , drealPath
  , runDRealInOverride
  , writeDRealSMT2File

    -- * STP
  , stpAdapter
  , stpPath
  , runSTPInOverride
  , withSTP

    -- * Yices
  , yicesAdapter
  , yicesPath
  , runYicesInOverride
  , writeYicesFile

    -- * Z3
  , z3Path
  , z3Adapter
  , runZ3InOverride
  , withZ3
  ) where

import           What4.Solver.Adapter
import           What4.Solver.Boolector
import           What4.Solver.CVC4
import           What4.Solver.DReal
import           What4.Solver.STP
import           What4.Solver.Yices
import           What4.Solver.Z3

import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Versions (Version(..))
import qualified Data.Versions as Versions
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           What4.Protocol.SMTWriter as SMT
import           What4.Protocol.SExp (stringToSExp)

-----------------------------------------------------------------
-- ** Checking solver version bounds

mkChunks :: [Word] -> [Versions.VChunk]
mkChunks = map ((:[]) . Versions.Digits)

-- | The minimum (inclusive) version bound for a given solver.
-- 
-- The keys come from @'smtWriterName'@ in @'WriterConn'@.
-- See also https://github.com/GaloisInc/crucible/issues/194
solverMinVersions :: Map String Version
solverMinVersions =
  [ ( "yices"
    , Version { _vEpoch = Nothing, _vChunks = mkChunks [2, 6, 1], _vRel = []}
    )
  ]

-- | The maximum (non-inclusive) version bound for a given solver.
--
-- The keys come from @'smtWriterName'@ in @'WriterConn'@.
solverMaxVersions :: Map String Version
solverMaxVersions = []

-- | Things that can go wrong while checking which solver version we've got
data SolverVersionCheckError =
    UnexpectedSolverResponse String
  | UnparseableVersion String

ppSolverVersionCheckError :: SolverVersionCheckError -> PP.Doc
ppSolverVersionCheckError =
  (PP.text "Unexpected error while checking solver version: " PP.<$$>) .
  \case
    UnexpectedSolverResponse resp -> PP.vcat $ map PP.text
      [ "Expected solver to respond with version number, but got: "
      , resp
      ]
    UnparseableVersion versionStr -> PP.cat $ map PP.text
      [ "Couldn't parse solver version number: "
      , versionStr
      ]

data SolverVersionError =
  SolverVersionError
  { min :: Maybe Version
  , max :: Maybe Version
  , actual :: String
  }
  deriving (Eq, Ord)

ppSolverVersionError :: SolverVersionError -> PP.Doc
ppSolverVersionError (SolverVersionError min max act) = PP.vcat $ map PP.text
  [ "Solver did not meet version bound restrictions: "
  , "Lower bound (inclusive): " ++ na (show <$> min)
  , "Upper bound (non-inclusive): " ++ na (show <$> max)
  ]
  where na (Just s) = s
        na Nothing  = "n/a"

-- | Ensure the solver's verion falls within a known-good range.
checkSolverVersion ::
  SMT.WriterConn t h ->
  IO (Either SolverVersionCheckError (Maybe SolverVersionError))
checkSolverVersion conn =
  let name = smtWriterName conn
      min0 = Map.lookup name solverMinVersions
      max0 = Map.lookup name solverMaxVersions
      err  = SolverVersionError min0 max0
  in
    case (min0, max0) of
      (Nothing, Nothing) -> pure (Right Nothing)
      (Nothing, Just max) -> _
      (Just min, Nothing) -> _
      (Just min, Just max) -> _
  
  -- (smtWriterName conn)
