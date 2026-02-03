-----------------------------------------------------------------------
-- |
-- Module           : Lang.Crucible.LLVM.Translation.Aliases
-- Description      : Resolution of global and function aliases
-- Copyright        : (c) Galois, Inc 2018
-- License          : BSD3
-- Maintainer       : Rob Dockins <rdockins@galois.com>
-- Stability        : provisional
-----------------------------------------------------------------------
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeFamilies #-}

module Lang.Crucible.LLVM.Translation.Aliases
 ( globalAliases
 , functionAliases
 , reverseAliases
 ) where

import           Control.Monad
import           Control.Monad.Trans.State

import qualified Data.List as List
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import qualified Text.LLVM.AST as L

import           Lang.Crucible.Panic (panic)
import           Lang.Crucible.LLVM.Types
import           Lang.Crucible.LLVM.TypeContext (TypeContext)
import           Lang.Crucible.LLVM.Translation.Constant

-- | Reverse a set of alias/aliasee relationships
--
-- Given a list of values @l : List A@ and a function @aliasOf : A -> A@,
-- compute a map @Map A (Set A)@ which records the set of things that are
-- transitive aliases of a given @a : A@.
--
-- The keys in the resulting map should be only terminals, e.g. those @a@
-- which aren't aliases of another @a'@ in @l@.
--
-- Requires that the elements of the input sequence are unique.
--
-- Outline:
-- * Initialize the empty map @M : Map A (Set A)@
-- * Initialize an auxilary map @N : Map A A@ which records the final aliasee
--   of each key (the last one in the chain of aliases).
-- * For each @a : A@ in l,
--   1. If @aliasOf a@ is in @N@ as @aliasee@,
--       a. insert @aliasee@ at key @a@ in @N@ (memoize the result)
--       b. insert @a@ into the set at key @aliasee@ in @M@ (record the result)
--       c. recurse on @s@ minus @aliasee@ and @a@.
--   2. If @aliasOf a@ is in @s@, recurse on @l ++ [a]@
--   3. Otherwise,
--       a. insert @a@ at key @a@ in @N@ (memoize the result)
--       b. return the map as-is
--
-- For the sake of practical concerns, the implementation uses \"labels\" for
-- comparison and @aliasOf@, and uses sequences rather than lists.
reverseAliases :: (Ord a, Ord l, Show a, Show l)
               => (a -> l)         -- ^ \"Label of\"
               -> (a -> Maybe l)   -- ^ \"Alias of\"
               -> Seq a
               -> Map a (Set a)
reverseAliases lab aliasOf_ seq_ =
   evalState (go Map.empty seq_) (Map.empty :: Map l a)

  where go map_ Seq.Empty      = pure map_
        go map_ (a Seq.:<| as) =
          case aliasOf_ a of
            Nothing ->
              do -- Don't overwrite it if it's already in the map
                 modify (Map.insert (lab a) a)
                 go (Map.insertWith (\_ old -> old) a Set.empty map_) as
            Just l ->
              do when (lab a == l) $
                   panic "reverseAliases" [ "Self-alias:", show a ]
                 st <- get
                 case Map.lookup l st of
                   Just aliasee ->
                     modify (Map.insert (lab a) aliasee) >>                        -- 1a
                     go (mapSetInsert aliasee a map_)                              -- 1b
                        (Seq.filter (\b -> lab b /= lab aliasee && lab b /= l) as) -- 1c
                   Nothing      ->
                     if isJust (List.find ((l ==) . lab) as)
                     then go map_ (as <> Seq.singleton a)                          -- 2
                     else modify (Map.insert (lab a) a) >>                         -- 3a
                          go map_ as                                               -- 3b
                 where mapSetInsert k v m  = Map.update (pure . Set.insert v) k m

-- | This is one step closer to the application of 'reverseAliases':
-- There are two \"sorts\" of objects:
-- Objects in sort @a@ are never aliases (think global variables).
-- Objects in sort @b@ are usually aliases, to things of either sort
-- (think aliases to global variables).
reverseAliasesTwoSorted :: (Ord a, Ord b, Ord l, Show a, Show b, Show l)
                        => (a -> l)       -- ^ \"Label of\" for type @a@
                        -> (b -> l)       -- ^ \"Label of\" for type @b@
                        -> (b -> Maybe l) -- ^ \"Alias of\"
                        -> Seq a
                        -> Seq b
                        -> Map a (Set b)
reverseAliasesTwoSorted laba labb aliasOf_ seqa seqb =
  Map.fromList . mapMaybe go . Map.toList $
    reverseAliases (either laba labb)
                   (either (const Nothing) aliasOf_)
                   (fmap Left seqa <> fmap Right seqb)
  where -- Drop the b's which have been added as keys and
        go (Right _, _) = Nothing
        -- Call "error" if an a has been tagged as an alias
        go (Left k, s) = Just (k, Set.map errLeft s)
        -- TODO: Should this throw an exception?
        errLeft (Left _)  = panic "reverseAliasesTwoSorted" ["unexpected Left value"]
        errLeft (Right v) = v

-- | What does this alias point to?
aliasOf :: (?lc :: TypeContext, HasPtrWidth wptr)
        => L.GlobalAlias
        -> Maybe L.Symbol
aliasOf alias =
  case L.aliasTarget alias of
    L.ValSymbol    symb      -> Just symb
    L.ValConstExpr constExpr ->
      case transConstantExpr constExpr of
        Right (SymbolConst symb 0) -> Just symb
        _ -> Nothing
    -- All other things silently get dropped; it's invalid LLVM code to not have
    -- a symbol or constexpr.
    _ -> Nothing

-- | Get all the aliases that alias (transitively) to a certain global.
globalAliases :: (?lc :: TypeContext, HasPtrWidth wptr)
              => L.Module
              -> Map L.Symbol (Set L.GlobalAlias)
globalAliases mod_ = Map.mapKeys L.globalSym $
  reverseAliasesTwoSorted L.globalSym L.aliasName aliasOf
    (Seq.fromList (L.modGlobals mod_)) (Seq.fromList (L.modAliases mod_))

-- | Get all the aliases that alias (transitively) to a certain function.
functionAliases :: (?lc :: TypeContext, HasPtrWidth wptr)
                => L.Module
                -> Map L.Symbol (Set L.GlobalAlias)
functionAliases mod_ = Map.mapKeys L.defName $
  reverseAliasesTwoSorted L.defName L.aliasName aliasOf
    (Seq.fromList (L.modDefines mod_)) (Seq.fromList (L.modAliases mod_))
