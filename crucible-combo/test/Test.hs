import Test.Tasty
import Test.Tasty.Hspec

import Lang.Crucible.Combo


main :: IO ()
main = do tests <- mkTests
          defaultMain $ testGroup "Combo tests" tests

mkTests :: IO [TestTree]
mkTests =
  sequence [
    testSpec "existence" $ do
        describe "can instantiate" $ do
          it "exists" $ do
            c <- return ComboPointerType
            putStrLn "ok"
            return ()
  ]
