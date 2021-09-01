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
    makeEntryPointsOrThrow
  )
where

import qualified Text.LLVM.AST as L

import           Crux.LLVM.Config (throwCError, CError(MissingFun))

import           UCCrux.LLVM.FullType.Translation (DeclMap, DeclSymbol, makeDeclSymbol)

-- | A list of function names to be explored by the simulator.
newtype EntryPoints m = EntryPoints { doGetEntryPoints :: [DeclSymbol m] }
  deriving (Eq, Ord)

-- | This function is inverse to 'getEntryPoints'.
makeEntryPoints :: [DeclSymbol m] -> EntryPoints m
makeEntryPoints = EntryPoints

-- | This function is inverse to 'makeEntryPoints'.
getEntryPoints :: EntryPoints m -> [DeclSymbol m]
getEntryPoints = doGetEntryPoints

-- | Construct a 'EntryPoints' out of a user-supplied list of function names. If
-- a function can't be found, throw a user error.
makeEntryPointsOrThrow :: DeclMap m a -> [String] -> IO (EntryPoints m)
makeEntryPointsOrThrow declMap =
  fmap makeEntryPoints .
    mapM
      (\nm ->
        case makeDeclSymbol (L.Symbol nm) declMap of
          Nothing -> throwCError (MissingFun nm)
          Just d -> pure d)
