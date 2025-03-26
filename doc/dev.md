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
- [ ] Remove outdated CPP `ifdef`s that refer to the dropped version
- [ ] Remove outdated `if` stanzas in the Cabal files
