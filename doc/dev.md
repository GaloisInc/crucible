# Developer documentation

## GHC versions

We support the three most recent versions of GHC.
We try to support new versions as soon as they are supported by the libraries that we depend on.

### Adding a new version

Crucible has several Galois-developed dependencies that are pinned as Git submodules, in `dependencies/`.
These dependencies need to support new GHC versions before Crucible itself can.
First, create GitHub issues on each of these dependencies requesting support for the new GHC version.
Then, create an issue on the Crucible repo that includes:

1. A link to the GHC release notes for the new version
2. Links to the issues on the dependencies
3. A link to this section of this document

Then, wait for the issues on the dependencies to be resolved.
When adding support for the new GHC version to Crucible itself, complete the following steps:

- [ ] Allow the [new version of `base`][base] in the Cabal `build-depends`
- [ ] Run `cabal {build,test,haddock}`, bumping dependency bounds and submodules as needed
- [ ] Fix any new warnings from [`-Wdefault`][wdefault]
- [ ] Run [`cabal freeze`][freeze] and rename `cabal.freeze` to `cabal.GHC-X.Y.Z.config`
- [ ] Add the new GHC version to the matrix in the GitHub Actions workflows
- [ ] Add the new version to the code that sets `GHC_NIXPKGS` in the CI config
- [ ] Bump the GHC version in the Dockerfiles in `.github/` to the oldest supported version
- [ ] Follow the below steps to remove the oldest GHC version

[base]: https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/libraries/version-history
[freeze]: https://cabal.readthedocs.io/en/stable/cabal-commands.html#cabal-freeze
[wdefault]: https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html#ghc-flag-Wdefault

### Removing an old version

- [ ] Remove the old version from the matrix in the GitHub Actions configuration
- [ ] Remove the old version's `cabal.GHC-X.Y.Z.config` file
- [ ] Remove outdated CPP `ifdef`s that refer to the dropped version
- [ ] Remove outdated `if` stanzas in the Cabal files

## LLVM versions

The `crux-llvm` CI currently runs the against one fixed, recent version of
LLVM. We should aim to update this LLVM version from time to time as new
versions of LLVM are released.

When updating the version of LLVM that the `crux-llvm` CI uses, complete the
following steps:

- [ ] Bump the `llvm-pretty` and `llvm-pretty-bc-parser` submodule commits to
      versions that support the desired version of LLVM.
- [ ] Ensure that the `crucible-llvm-*` and `crux-llvm` packages build against
      the new versions of `llvm-pretty` and `llvm-pretty-bc-parser`. If not,
      update the code as needed.
- [ ] Ensure that the `crucible-llvm` test suite passes with the desired
      version of LLVM. If not, investigate why specific test cases fail.
      There is no one-size-fits-all-formula for fixing these sorts of test
      failures, but often times this will require changes to `llvm-pretty`,
      `llvm-pretty-bc-parser`, `crucible-llvm`, or a combination thereof.
- [ ] Ensure that the `crux-llvm` test suite passes with the desired version of
      LLVM. If not, investigate why specific test cases fail.
- [ ] Update `crux-llvm/README.md` to mention that a newer LLVM version is now
      supported (near the sentence "... LLVMs versions from X to Y are likely
      to work well ...").
- [ ] Go to the vendored-in `.github/llvm.sh` script and check to see if there
      have been any changes to the script upstream (follow the URL in the
      comments near the top of the script). If there have been changes, then
      copy over the changes to the vendored-in script and commit them.
- [ ] In `.github/ci.sh`, update `LINUX_LLVM_VER` and `MACOS_LLVM_VER` to the
      desired LLVM version.
- [ ] In `.github/Dockerfile-crux-llvm`, update `LLVM_VER` to the desired LLVM
      version.
