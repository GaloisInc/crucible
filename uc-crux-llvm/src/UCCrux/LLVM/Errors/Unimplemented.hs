{-
Module       : UCCrux.LLVM.Errors.Unimplemented
Description  : Dealing with unimplemented features
Copyright    : (c) Galois, Inc 2021
License      : BSD3
Maintainer   : Langston Barrett <langston@galois.com>
Stability    : provisional
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}

module UCCrux.LLVM.Errors.Unimplemented
  ( Unimplemented (..),
    ppUnimplemented,
    unimplemented,
    catchUnimplemented,
    assertUnimplemented,
  )
where

{- ORMOLU_DISABLE -}
import Control.Exception (SomeException, try, displayException)
import Panic hiding (panic)
import qualified Panic
{- ORMOLU_ENABLE -}

data Unimplemented
  = VarArgsFunction
  | VarArgsFunctionType
  | VoidType
  | OpaqueType
  | UnsupportedType
  | MetadataType
  | GeneratingArrays
  | IndexCursor
  | ConstrainGlobal
  deriving (Bounded, Enum, Eq, Ord)

ppUnimplemented :: Unimplemented -> String
ppUnimplemented =
  \case
    VarArgsFunction -> "Exploring variable-arity functions"
    VarArgsFunctionType -> "Variable-arity function (pointer) types in globals or arguments"
    VoidType -> "Void types in globals or arguments"
    OpaqueType -> "Opaque (undefined) types in globals or arguments"
    UnsupportedType -> "Unsupported types in globals or arguments"
    MetadataType -> "LLVM metadata types in globals or arguments"
    GeneratingArrays -> "Arrays in globals or arguments"
    IndexCursor -> "Deduced preconditions on array elements"
    ConstrainGlobal -> "Constraints on a global variable"

instance PanicComponent Unimplemented where
  panicComponentName _ = "uc-crux-llvm"
  panicComponentIssues _ = "https://github.com/GaloisInc/crucible/issues"

  {-# NOINLINE panicComponentRevision #-}
  panicComponentRevision = $useGitRevision

unimplemented ::
  HasCallStack =>
  -- | Short name of where the error occured
  String ->
  -- | What's the not-yet supported thing?
  Unimplemented ->
  a
unimplemented where_ what =
  Panic.panic
    what
    where_
    [ ppUnimplemented what,
      "is not yet implemented as a feature of crux-llvm bugfinding mode.",
      "If this feature would be useful to you, please report this error."
    ]

catchUnimplemented :: IO a -> IO (Either (Panic.Panic Unimplemented) a)
catchUnimplemented computation =
  either
    (\panic@(Panic (_ :: Unimplemented) _ _ _) -> Left panic)
    pure
    <$> try computation

assertUnimplemented :: IO a -> IO (Either String String)
assertUnimplemented computation =
  either
    (\(exc :: SomeException) -> Left (displayException exc))
    (either (Right . show) (\_ -> Left "No exception was raised!"))
    <$> try (catchUnimplemented computation)
