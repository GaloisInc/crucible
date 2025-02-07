{-|
Copyright        : (c) Galois, Inc. 2025
Maintainer       : Langston Barrett <langston@galois.com>
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Lang.Crucible.Debug.Regex
  ( type Regex
  , type Empty
  , type Lit
  , type (:|)
  , type Then
  , type Star
  , RegexRepr(..)
  , AcceptsEmpty
  , acceptsEmpty
  , DerivativeResult(..)
  , derivative
  , Match(..)
  , MatchError(..)
  , TokenParser(..)
  , match
  , nextLits
  , liftOrs
  , Sugar(..)
  , sugar
  , prettySugar
  ) where

import Data.Bifunctor (first)
import Data.Foldable qualified as Foldable
import Data.Kind (Type)
import Data.Parameterized.BoolRepr (BoolRepr (..), (%||), (%&&))
import Data.Parameterized.Classes (KnownRepr(knownRepr))
import Data.Parameterized.Some (Some (Some))
import Data.Parameterized.TraversableFC qualified as TFC
import Data.Sequence qualified as Seq
import Data.Sequence (Seq)
import Data.Type.Bool (type (||), type (&&))
import Data.Type.Equality (TestEquality (testEquality), type (:~:)(Refl))
import Prettyprinter qualified as PP

-- | Type-level only
data Regex a
  = TFail
  | TEmpty
  | TLit a
  | TOr (Regex a) (Regex a)
  | TThen (Regex a) (Regex a)
  | TStar (Regex a)

type Empty = 'TEmpty
type Lit = 'TLit
type a :| b = 'TOr a b
type Then = 'TThen
type Star = 'TStar

-- | Value-level representative of 'Regex'
--
-- The order of the type parameters is a bit arbitrary... This order gives
-- 'KnownRepr' and 'TestEquality' instances but requires flipping the type
-- parameters to get 'TraversableF'.
type RegexRepr :: (k -> Type) -> Regex k -> Type
data RegexRepr f r where
  Empty :: RegexRepr f 'TEmpty
  Fail :: RegexRepr f 'TFail
  Lit :: f t -> RegexRepr f ('TLit t)
  Or :: RegexRepr f l -> RegexRepr f r -> RegexRepr f ('TOr l r)
  Star :: RegexRepr f r -> RegexRepr f ('TStar r)
  Then :: RegexRepr f l -> RegexRepr f r -> RegexRepr f ('TThen l r)

instance TestEquality f => TestEquality (RegexRepr f) where
  testEquality rgx rgx' =
    case (rgx, rgx') of
      (Empty, Empty) -> Just Refl
      (Empty, _) -> Nothing
      (Fail, Fail) -> Just Refl
      (Fail, _) -> Nothing
      (Lit l, Lit l') ->
        case testEquality l l' of
          Just Refl -> Just Refl
          Nothing -> Nothing
      (Lit {}, _) -> Nothing
      (Or l r, Or l' r') ->
        case (testEquality l l', testEquality r r') of
          (Just Refl, Just Refl) -> Just Refl
          _ -> Nothing
      (Or {}, _) -> Nothing
      (Star r, Star r') ->
        case testEquality r r' of
          Just Refl -> Just Refl
          Nothing -> Nothing
      (Star {}, _) -> Nothing
      (Then l r, Then l' r') ->
        case (testEquality l l', testEquality r r') of
          (Just Refl, Just Refl) -> Just Refl
          _ -> Nothing
      (Then {}, _) -> Nothing

instance KnownRepr (RegexRepr f) 'TEmpty where
  knownRepr = Empty

instance KnownRepr (RegexRepr f) 'TFail where
  knownRepr = Fail

instance KnownRepr f t => KnownRepr (RegexRepr f) ('TLit t) where
  knownRepr = Lit knownRepr

instance
  ( KnownRepr (RegexRepr f) l
  , KnownRepr (RegexRepr f) r
  ) => KnownRepr (RegexRepr f) ('TOr l r) where
  knownRepr = Or knownRepr knownRepr

instance
  ( KnownRepr (RegexRepr f) l
  , KnownRepr (RegexRepr f) r
  ) => KnownRepr (RegexRepr f) ('TThen l r) where
  knownRepr = Then knownRepr knownRepr

instance KnownRepr (RegexRepr f) r => KnownRepr (RegexRepr f) ('TStar r) where
  knownRepr = Star knownRepr

instance TFC.FunctorFC RegexRepr where
  fmapFC f =
    \case
      Empty -> Empty
      Fail -> Fail
      Lit l -> Lit (f l)
      Or l r -> Or (TFC.fmapFC f l) (TFC.fmapFC f r)
      Star r -> Star (TFC.fmapFC f r)
      Then l r -> Then (TFC.fmapFC f l) (TFC.fmapFC f r)

instance TFC.FoldableFC RegexRepr where
  foldMapFC f =
    \case
      Empty -> mempty
      Fail -> mempty
      Lit l -> f l
      Or l r -> TFC.foldMapFC f l <> TFC.foldMapFC f r
      Star r -> TFC.foldMapFC f r
      Then l r -> TFC.foldMapFC f l <> TFC.foldMapFC f r

instance TFC.TraversableFC RegexRepr where
  traverseFC f =
    \case
      Empty -> pure Empty
      Fail -> pure Fail
      Lit l -> Lit <$> f l
      Or l r -> Or <$> TFC.traverseFC f l <*> TFC.traverseFC f r
      Star r -> Star <$> TFC.traverseFC f r
      Then l r -> Then <$> TFC.traverseFC f l <*> TFC.traverseFC f r

type AcceptsEmpty :: Regex k -> Bool
type family AcceptsEmpty r where
  AcceptsEmpty 'TFail = 'False
  AcceptsEmpty 'TEmpty  = 'True
  AcceptsEmpty ('TLit _) = 'False
  AcceptsEmpty ('TOr l r) = AcceptsEmpty l || AcceptsEmpty r
  AcceptsEmpty ('TThen l r) = AcceptsEmpty l && AcceptsEmpty r
  AcceptsEmpty ('TStar r) = 'True

acceptsEmpty :: RegexRepr f r -> BoolRepr (AcceptsEmpty r)
acceptsEmpty =
  \case
    Empty -> TrueRepr
    Fail -> FalseRepr
    Lit {} -> FalseRepr
    Or l r -> acceptsEmpty l %|| acceptsEmpty r
    Star _ -> TrueRepr
    Then l r -> acceptsEmpty l %&& acceptsEmpty r

-- | Type-level version of 'nu'.
--
-- See Wikipedia on "Brzozowski derivative"
type Nu :: Regex k -> Regex k
type family Nu r where
  Nu 'TFail = 'TFail
  Nu 'TEmpty  = 'TEmpty
  Nu ('TLit _) = 'TFail
  Nu ('TOr l r) = 'TOr (Nu l) (Nu r)
  Nu ('TThen l r) = 'TThen (Nu l) (Nu r)
  Nu ('TStar r) = 'TEmpty

-- | Auxiliary function for 'derivative'.
--
-- Value-level version of 'Nu'.
--
-- See Wikipedia on "Brzozowski derivative"
nu :: RegexRepr f r -> RegexRepr f (Nu r)
nu =
  \case
    Empty -> Empty
    Fail -> Fail
    Lit {} -> Fail
    Or l r -> Or (nu l) (nu r)
    Star _ -> Empty
    Then l r -> Then (nu l) (nu r)

-- | The result of 'derivative'
data DerivativeResult f g
  = DerivativeResult
    { -- | The remaining regex after matching that token
      derivativeRegex :: Some (RegexRepr f)
      -- | All the literals the token was matched at
    , derivativeMatched :: Seq (Some g)
    }

-- | See Wikipedia on "Brzozowski derivative"
derivative ::
  (forall t. f t -> TokenParser tok e g t) ->
  tok ->
  RegexRepr f r ->
  DerivativeResult f g
derivative getParser tok =
  let noMatch r = DerivativeResult r Seq.empty in
  let doFail = noMatch (Some Fail) in
  \case
    Empty -> doFail
    Fail -> doFail
    Lit f ->
      case runTokenParser (getParser f) tok of
        Left _ -> doFail
        Right m -> DerivativeResult (Some Empty) (Seq.singleton (Some m))
    Or l r ->
      case (derivative getParser tok l, derivative getParser tok r) of
        (DerivativeResult (Some Fail) _, r') -> r'
        (l', DerivativeResult (Some Fail) _) -> l'
        (DerivativeResult (Some l') ms, DerivativeResult (Some r') ms') ->
          DerivativeResult (Some (Or l' r')) (ms <> ms')
    Star f ->
      case derivative getParser tok f of
        DerivativeResult (Some f') ms ->
          DerivativeResult (Some (Then f' (Star f))) ms
    Then l r ->
      case (derivative getParser tok l, derivative getParser tok r) of
        (DerivativeResult (Some  l') ms, DerivativeResult (Some r') ms') ->
          DerivativeResult (Some (Or (Then l' r) (Then (nu l) r'))) (ms <> ms')

-- | The result of 'match', in case of success
type Match :: (k -> Type) -> Regex k -> Type
data Match k r where
  MEmpty :: Match f 'TEmpty
  MLit :: f t -> Match f ('TLit t)
  MLeft :: Match f l -> Match f ('TOr l r)
  MRight :: Match f r -> Match f ('TOr l r)
  MThen :: Match f l -> Match f r -> Match f ('TThen l r)
  MStar :: [Match f r] -> Match f ('TStar r)

-- | Failures that may arise during 'match'
data MatchError tok e
  = EFail
  | Eof
  | EOr (MatchError tok e) (MatchError tok e)
  | NotEmpty [tok]
  | Token e
  deriving Show

instance (PP.Pretty e, PP.Pretty tok) => PP.Pretty (MatchError tok e) where
  pretty =
    \case
      EFail -> "This regular expression never matches"
      Eof -> "Unexpected end of input"
      EOr l r ->
        PP.vcat
        [ "Both branches failed to match:"
        , "-" PP.<+> PP.align (PP.pretty l)
        , "-" PP.<+> PP.align (PP.pretty r)
        ]
      NotEmpty toks ->
        "Expected end of input, but found:" PP.<+> PP.hsep (map PP.pretty toks)
      Token e -> PP.pretty e

type TokenParser :: Type -> Type -> (k -> Type) -> k -> Type
newtype TokenParser tok e f t
  = TokenParser { runTokenParser :: tok -> Either e (f t) }

-- | Match a regular expression against a token stream
match ::
  -- | Regex
  RegexRepr (TokenParser tok e g) r ->
  -- | Token stream
  [tok] ->
  -- | Either a 'MatchError', or a 'Match' plus the unconsumed tokens
  Either (MatchError tok e) (Match g r, [tok])
match rgx toks =
  case (rgx, toks) of
    (Fail, _) -> Left EFail
    (Empty, []) -> Right (MEmpty, toks)
    (Empty, _) -> Left (NotEmpty toks)
    (Lit _, []) -> Left Eof
    (Lit ft, t : ts) -> do
      m <- first Token (runTokenParser ft t)
      pure (MLit m, ts)
    (Then l r, ts) -> do
      (ml, ts') <- match l ts
      (mr, ts'') <- match r ts'
      pure (MThen ml mr, ts'')
    (Or l r, ts) ->
      case match l ts of
        Right (m, ts') -> Right (MLeft m, ts')
        Left ef ->
          case match r ts of
            Right (m, ts') -> pure (MRight m, ts')
            Left eg -> Left (EOr ef eg)
    (Star f, ts) ->
      case match f ts of
        Left _ -> Right (MStar [], ts)
        Right (m, ts') ->
          first (\(MStar ms) -> MStar (m : ms)) <$> match (Star f) ts'

-- | List the literals that could be matched next
nextLits :: RegexRepr f r -> Seq (Some f)
nextLits =
  \case
    Empty -> Seq.empty
    Fail -> Seq.empty
    Lit x -> Seq.singleton (Some x)
    Or l r -> nextLits l <> nextLits r
    Star r -> nextLits r
    Then l r ->
      case acceptsEmpty l of
        TrueRepr -> nextLits l <> nextLits r
        FalseRepr -> nextLits l

-- | Syntactic sugar for displaying 'RegexRepr's, especially for quantification
type Sugar :: (k -> Type) -> Regex k -> Type
data Sugar f r where
  SEmpty :: Sugar f 'TEmpty
  SFail :: Sugar f 'TFail
  SLit :: f t -> Sugar f ('TLit t)
  SOptL :: Sugar f l -> Sugar f ('TOr l Empty)
  SOptR :: Sugar f r -> Sugar f ('TOr Empty r)
  SOr :: Sugar f l -> Sugar f r -> Sugar f ('TOr l r)
  SSomeL :: Sugar f l -> Sugar f ('TOr ('TStar r) r)
  SSomeR :: Sugar f r -> Sugar f ('TOr r ('TStar r))
  SStar :: Sugar f r -> Sugar f ('TStar r)
  SThen :: Sugar f l -> Sugar f r -> Sugar f ('TThen l r)

sugar :: TestEquality f => RegexRepr f r -> Sugar f r
sugar =
  \case
    Empty -> SEmpty
    Fail -> SFail
    Lit l -> SLit l
    Or l Empty -> SOptL (sugar l)
    Or Empty r -> SOptR (sugar r)
    Or (Star l) r | Just Refl <- testEquality l r -> SSomeL (sugar l)
    Or l (Star r) | Just Refl <- testEquality l r -> SSomeR (sugar l)
    Or l r -> SOr (sugar l) (sugar r)
    Star r -> SStar (sugar r)
    Then l r -> SThen (sugar l) (sugar r)

-- | Lift top-level 'Or's (i.e., those not under quantifiers)
liftOrs :: Sugar f r -> Seq (Some (Sugar f))
liftOrs =
  \case
    SEmpty -> Seq.singleton (Some SEmpty)
    SFail -> Seq.empty
    SLit x -> Seq.singleton (Some (SLit x))
    r@(SOptL {}) -> Seq.singleton (Some r)
    r@(SOptR {}) -> Seq.singleton (Some r)
    SOr l r -> liftOrs l <> liftOrs r
    r@(SSomeL {}) -> Seq.singleton (Some r)
    r@(SSomeR {}) -> Seq.singleton (Some r)
    SThen l r ->
      Seq.fromList
        [ Some (SThen x y)
        | Some x <- Foldable.toList (liftOrs l)
        , Some y <- Foldable.toList (liftOrs r)
        ]
    SStar r -> Seq.singleton (Some (SStar r))

prettySugar ::
  -- | Separator for 'SThen'
  PP.Doc ann ->
  (forall t. f t -> PP.Doc ann) ->
  Sugar f r ->
  PP.Doc ann
prettySugar sep f =
  \case
    SEmpty -> ""
    SFail -> "∅"
    SLit l -> f l
    SOptL (SLit l) -> f l PP.<> "?"
    SOptL l -> PP.parens (prettySugar sep f l) PP.<> "?"
    SOptR (SLit r) -> f r PP.<> "?"
    SOptR r -> PP.parens (prettySugar sep f r) PP.<> "?"
    SOr l r -> PP.parens (prettySugar sep f l PP.<> "|" PP.<> prettySugar sep f r)
    SSomeL (SLit l) -> f l PP.<> "+"
    SSomeL l -> PP.parens (prettySugar sep f l) PP.<> "+"
    SSomeR (SLit r) -> f r PP.<> "+"
    SSomeR r -> PP.parens (prettySugar sep f r) PP.<> "+"
    SStar (SLit l) -> f l PP.<> "*"
    SStar r -> PP.parens (prettySugar sep f r) PP.<> "*"
    SThen l r -> prettySugar sep f l PP.<> sep PP.<> prettySugar sep f r
