{-
Module       : UCCrux.LLVM.Run.EntryPoints
Description  : Newtype for entry points, i.e., functions to be simulated
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}

module UCCrux.LLVM.Run.EntryPoints
  ( EntryPoints,
    makeEntryPoints,
    getEntryPoints,
    tryMakeEntryPoints,
    makeEntryPointsOrThrow
  )
where

import           Data.Either (partitionEithers)
import           Data.List.NonEmpty (NonEmpty, nonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import qualified Text.LLVM.AST as L

import           Crux.LLVM.Config (throwCError, CError(MissingFun))

import           UCCrux.LLVM.Newtypes.FunctionName (FunctionName, functionNameToString)
import           UCCrux.LLVM.FullType.Translation (DeclMap, DeclSymbol, makeDeclSymbol)

-- | A list of function names to be explored by the simulator.
newtype EntryPoints m = EntryPoints { runEntryPoints :: [DeclSymbol m] }
  deriving (Eq, Ord)

-- | This function is inverse to 'getEntryPoints'.
makeEntryPoints :: [DeclSymbol m] -> EntryPoints m
makeEntryPoints = EntryPoints

-- | This function is inverse to 'makeEntryPoints'.
getEntryPoints :: EntryPoints m -> [DeclSymbol m]
getEntryPoints = runEntryPoints

tryMakeEntryPoints ::
  DeclMap m a ->
  [FunctionName] ->
  Either (NonEmpty FunctionName) (EntryPoints m)
tryMakeEntryPoints declMap funs =
  let (failures, successes) =
        partitionEithers
          (map
            (\nm ->
              case makeDeclSymbol (L.Symbol (functionNameToString nm)) declMap of
                Nothing -> Left nm
                Just d -> Right d)
            funs)
  in case nonEmpty failures of
       Just nonEmptyFailures -> Left nonEmptyFailures
       Nothing -> Right (makeEntryPoints successes)

-- | Construct a 'EntryPoints' out of a user-supplied list of function names. If
-- a function can't be found, throw a user error.
makeEntryPointsOrThrow :: DeclMap m a -> [FunctionName] -> IO (EntryPoints m)
makeEntryPointsOrThrow declMap funs =
  case tryMakeEntryPoints declMap funs of
    Left errs ->
      throwCError (MissingFun (functionNameToString (NonEmpty.head errs)))
    Right entries -> return entries
