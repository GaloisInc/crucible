git submodule init
git submodule update --recursive
export STACK_YAML=../stack-ghc-8.6.5.yaml
stack build crux-llvm
# Link bin directory to a more convenient location
rm -f bin
ln -s `stack path --local-install-root`/bin
set +x +v
echo
echo "COPIED EXECUTABLES TO `pwd`/bin."
