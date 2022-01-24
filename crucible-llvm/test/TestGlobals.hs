module TestGlobals
  (
    globalTests
  )
  where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Test.Tasty as T
import           Test.Tasty.HUnit ( testCase, (@=?) )

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem
import           Lang.Crucible.LLVM.Translation.Aliases

import           MemSetup ( withInitializedMemory )


globalTests :: T.TestTree
globalTests =
  T.testGroup "Global Aliases" $ concat
  [
    ------------- Handling of global aliases

    -- It would be nice to have access to the Arbitrary instances for L.AST from
    -- llvm-pretty-bc-parser here.
    let mkGlobal name = L.Global (L.Symbol name) L.emptyGlobalAttrs L.Opaque Nothing Nothing Map.empty
        mkAlias  name global = L.GlobalAlias { L.aliasLinkage    = Nothing
                                             , L.aliasVisibility = Nothing
                                             , L.aliasName       = L.Symbol name
                                             , L.aliasType       = L.Opaque
                                             , L.aliasTarget     = L.ValSymbol (L.Symbol global)
                                             }
        mkModule as   gs     = L.emptyModule { L.modGlobals = gs
                                             , L.modAliases = as
                                             }
    in
      [ testCase "globalAliases: empty module" $
        withInitializedMemory (mkModule [] []) $ \_ ->
          Map.empty @=? globalAliases L.emptyModule

      , testCase "globalAliases: singletons, aliased" $
        let g = mkGlobal "g"
            a = mkAlias  "a" "g"
        in withInitializedMemory (mkModule [] []) $ \_ ->
          Map.singleton (L.globalSym g) (Set.singleton a) @=? globalAliases (mkModule [a] [g])

      , testCase "globalAliases: two aliases" $
        let g  = mkGlobal "g"
            a1 = mkAlias  "a1" "g"
            a2 = mkAlias  "a2" "g"
        in withInitializedMemory (mkModule [] []) $ \_ ->
          Map.singleton (L.globalSym g) (Set.fromList [a1, a2]) @=? globalAliases (mkModule [a1, a2] [g])
      ]

  , -- The following test ensures that SAW treats global aliases properly in that
    -- they are present in the @Map@ of globals after initializing the memory.

    let t = L.PrimType (L.Integer 2)
        mkGlobal name = L.Global (L.Symbol name) L.emptyGlobalAttrs t Nothing Nothing Map.empty
        mkAlias  name global = L.GlobalAlias { L.aliasLinkage    = Nothing
                                             , L.aliasVisibility = Nothing
                                             , L.aliasName       = L.Symbol name
                                             , L.aliasType       = t
                                             , L.aliasTarget     = L.ValSymbol (L.Symbol global)
                                             }
        mkModule as   gs     = L.emptyModule { L.modGlobals = gs
                                             , L.modAliases = as
                                             }
    in [ testCase "initializeMemory" $
         let mod'    = mkModule [mkAlias  "a" "g"] [mkGlobal "g"]
             inMap k = (Just () @=?) . fmap (const ()) . Map.lookup k
         in withInitializedMemory mod' $ \result ->
           inMap (L.Symbol "a") (LLVMMem.memImplGlobalMap result)
       ]

  ]
