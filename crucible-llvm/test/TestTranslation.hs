module TestTranslation
  (
    translationTests
  )
where

import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import qualified Test.Tasty as T
import           Test.Tasty.HUnit ( testCase, (@=?) )
import           Test.Tasty.QuickCheck ( testProperty )

import           Lang.Crucible.LLVM.Translation.Aliases ( reverseAliases )


translationTests :: T.TestTree
translationTests =
  T.testGroup "Translation"
  [
    T.testGroup "Aliases" $

     ------------- Tests for reverseAliases

      let evenAlias xs x =
            let s = Set.fromList (F.toList xs)
            in if even x && Set.member x s
               then Just (x `div` 2)
               else Nothing
          addTargets xs = xs <> fmap (`div` 2) (Seq.filter even xs)
      in
        [ testCase "reverseAliases: empty" $
            Map.empty @=?
              reverseAliases id (const Nothing) (Seq.empty :: Seq.Seq Int)

        , testProperty "reverseAliases: singleton" $ \x ->
            Map.singleton (x :: Int) Set.empty ==
              reverseAliases id (const Nothing) (Seq.singleton x)

        , -- The result should not depend on ordering
          testProperty "reverseAliases: reverse" $ \xs ->
            let -- no self-aliasing allowed
                xs' = addTargets (Seq.filter (/= 0) xs)
            in reverseAliases id (evenAlias xs) (xs' :: Seq.Seq Int) ==
                 reverseAliases id (evenAlias xs) (Seq.reverse xs')

        , -- Every item should appear exactly once
          testProperty "reverseAliases: xor" $ \xs ->
            let xs'    = addTargets (Seq.filter (/= 0) xs)
                result = reverseAliases id (evenAlias xs) (xs' :: Seq.Seq Int)
                keys   = Map.keysSet result
                values = Set.unions (Map.elems result)
                --
                xor True a = not a
                xor False a = a
                --
            in all (\x -> Set.member x keys `xor` Set.member x values) xs'
        ]

  ]
