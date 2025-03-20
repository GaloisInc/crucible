# Developer documentation

## GHC versions

We support the three most recent versions of GHC.
We try to support new versions as soon as they are supported by the libraries that we depend on.

### Adding a new version

The following checklist enumerates the steps needed to support a new version of GHC.
When performing such an upgrade, it can be helpful to copy/paste this list into the MR description and check off what has been done, so as to not forget anything.

- [ ] Allow the [new version of `base`][base] in the Cabal `build-depends`
- [ ] Run `cabal {build,test,haddock}`, bumping dependency bounds as needed
- [ ] Fix any new warnings from [`-Wdefault`][wdefault]
- [ ] Run [`cabal freeze`][freeze] and rename `cabal.freeze` to `cabal.GHC-X.Y.Z.config`
- [ ] Add the new GHC version to the matrix in the GitHub Actions workflows
- [ ] Add the new version to the code that sets `GHC_NIXPKGS` in the CI config
- [ ] Use the new GHC version in the Dockerfiles in `.github/`
- [ ] Follow the below steps to remove the oldest GHC version

[base]: https://www.snoyman.com/base/
[freeze]: https://cabal.readthedocs.io/en/stable/cabal-commands.html#cabal-freeze
[wdefault]: https://downloads.haskell.org/ghc/latest/docs/users_guide/using-warnings.html#ghc-flag-Wdefault

### Removing an old version

- [ ] Remove the old version from the matrix in the GitHub Actions configuration
- [ ] Remove outdated CPP `ifdef`s that refer to the dropped version
- [ ] Remove outdated `if` stanzas in the Cabal files
