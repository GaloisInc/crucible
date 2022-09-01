{-
Module           : UCCrux.LLVM.Soundness
Description      : Soundness criteria, see @doc/soundness.md@
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional
-}

{-# LANGUAGE LambdaCase #-}

module UCCrux.LLVM.Soundness
  ( Soundness(..),
    stringToSoundness,
    atLeastAsSound
  )
where

-- | Description of the soundness of a feature of the analysis.
--
-- This type forms a partial order with the following Hasse diagram (of which
-- its 'Ord' instance is one of two compatible total orderings):
--
-- >        Indefinite
-- >       /         \
-- > Overapprox    Underapprox
-- >       \         /
-- >         Precise
--
-- The ordering means: Anything that is 'Precise' can also be counted as either
-- 'Overapprox' or 'Underapprox', and if you're willing to accept 'Indefinite',
-- then you would be willing to accept any other degree of soundness as well.
--
-- For how these criteria apply to user-provided specifications of external
-- functions, see @doc/specs.md@.
data Soundness
  = -- | Both over-approximate and under-approximate
    Precise
  | Overapprox
  | Underapprox
  -- | Not necessarily over-approximate nor under-approximate
  | Indefinite
  deriving (Eq, Ord, Show)

stringToSoundness :: String -> Maybe Soundness
stringToSoundness =
  \case
    "precise" -> Just Precise
    "overapprox" -> Just Overapprox
    "underapprox" -> Just Underapprox
    "indefinite" -> Just Indefinite
    _ -> Nothing

-- | The partial order on 'Soundness', asks whether the first 'Soundness' is at
-- least as sound as the second.
atLeastAsSound :: Soundness -> Soundness -> Bool
atLeastAsSound feat criterion =
  case (feat, criterion) of
    (Precise, _) -> True
    (_, Precise) -> False
    (Overapprox, Overapprox) -> True
    (_, Overapprox) -> False
    (Underapprox, Underapprox) -> True
    (_, Underapprox) -> False
    (_, Indefinite) -> True
