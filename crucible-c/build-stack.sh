(cd .. && GITHUB_URL="https://github.com/" NO_GIT_PULL="true" ./scripts/build-sandbox.sh)
STACK_YAML=stack-ghc-8.2.yaml stack build
# Link bin directory to a more convenient location
rm -f bin
ln -s `stack path --local-install-root`/bin
set +x +v
echo
echo "COPIED EXECUTABLES TO `pwd`/bin."
