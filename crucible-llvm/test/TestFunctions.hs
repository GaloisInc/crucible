module TestFunctions
  (
    functionTests
  )
where

import qualified Data.Map.Strict as Map

import qualified Test.Tasty as T
import           Test.Tasty.HUnit ( testCase, (@=?) )

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.LLVM.MemModel as LLVMMem

import MemSetup ( withInitializedMemory )


functionTests :: T.TestTree
functionTests =
  T.testGroup "Functions" $

  -- The following ensures that Crucible treats aliases to functions properly

  let alias = L.GlobalAlias
              { L.aliasLinkage = Nothing
              , L.aliasVisibility = Nothing
              , L.aliasName = L.Symbol "aliasName"
              , L.aliasType =
                  L.FunTy
                  (L.PrimType L.Void)
                  [ L.PtrTo (L.Alias (L.Ident "class.std::cls")) ]
                  False
              , L.aliasTarget =
                  L.ValSymbol (L.Symbol "defName")
              }

      def = L.Define
            { L.defLinkage = Just L.WeakODR
            , L.defVisibility = Nothing
            , L.defRetType = L.PrimType L.Void
            , L.defName = L.Symbol "defName"
            , L.defArgs =
                [ L.Typed
                  { L.typedType = L.PtrTo (L.Alias (L.Ident "class.std::cls"))
                  , L.typedValue = L.Ident "0"
                  }
                ]
            , L.defVarArgs = False
            , L.defAttrs = []
            , L.defSection = Nothing
            , L.defGC = Nothing
            , L.defBody =
                [ L.BasicBlock
                  { L.bbLabel = Just (L.Anon 1)
                  , L.bbStmts =
                      [ L.Result
                        (L.Ident "2")
                        (L.Alloca
                          (L.PtrTo
                            (L.Alias (L.Ident "class.std::cls"))) Nothing (Just 8))
                        []
                      , L.Effect L.RetVoid []
                      ]
                  }
                ]
            , L.defMetadata = mempty
            , L.defComdat = Nothing
            }
  in [ testCase "initializeMemory (functions)" $
       let mod'    = L.emptyModule { L.modDefines = [def]
                                   , L.modAliases = [alias]
                                   }
           inMap k = (Just () @=?) . fmap (const ()) . Map.lookup k
       in withInitializedMemory mod' $ \memImpl ->
         inMap
         (L.Symbol "aliasName")
         (LLVMMem.memImplGlobalMap memImpl)
     ]
