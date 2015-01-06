(cd deps/abcBridge && rm -rf abc-build)
(cd deps/abcBridge && cabal clean)
(cd deps/aig && cabal clean)
(cd deps/cryptol && cabal clean)
(cd deps/jvm-parser && cabal clean)
(cd deps/llvm-pretty && cabal clean)
(cd deps/llvm-pretty-bc-parser && cabal clean)
(cd ../Cryptol && cabal clean)
(cd ../Java && cabal clean)
(cd ../LLVM && cabal clean)
(cd ../SAWCore && cabal clean)
cabal clean
rm -rf build
rm -rf build-test
