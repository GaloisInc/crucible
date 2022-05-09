module Callgraph (callgraphTests) where

import qualified Data.Set as Set

import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TH

import qualified UCCrux.LLVM.Callgraph as CG

callgraphTests :: TT.TestTree
callgraphTests = TT.testGroup "callgraph"
  [ TH.testCase "insert one edge" $
      let cg = CG.insertEdge (CG.Edge () () ()) CG.empty
      in TH.assertEqual "insert one edge" 1 (length (CG.edges cg))
  , TH.testCase "callees" $
      let cg = CG.singleton (CG.Edge "callee" "caller" ())
      in TH.assertEqual "callees" (Set.singleton "callee") (CG.callees cg "caller")
  , TH.testCase "outgoing" $
      let cg = CG.fromList [ CG.Edge "callee1" "caller" ()
                           , CG.Edge "callee2" "caller" ()
                           ]
      in TH.assertEqual
           "outgoing"
           (Set.fromList ["callee1", "callee2"])
           (Set.map CG.peEndpoint (CG.outgoing cg "caller"))
  ]
