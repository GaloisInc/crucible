(cd deps/abcBridge && rm -rf abc-build)
(cd deps/abcBridge && cabal clean)
(cd deps/aig && cabal clean)
(cd deps/saw-core && cabal clean)
(cd deps/cryptol && cabal clean)
(cd deps/cryptol-verifier && cabal clean)
(cd deps/jvm-parser && cabal clean)
(cd deps/jvm-verifier && cabal clean)
(cd deps/llvm-pretty && cabal clean)
(cd deps/llvm-pretty-bc-parser && cabal clean)
(cd deps/llvm-verifier && cabal clean)
cabal clean
rm -rf build
rm -rf build-test
