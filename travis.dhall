-- nix-shell -p 'with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-unstable.tar.gz) { }; travis' -p dhall -p dhall-json --pure --run 'cat travis.dhall | dhall-to-yaml --omitNull |& tee log | sed "s/! //g" > .travis.yml && travis lint .travis.yml'

    let map =
          https://raw.githubusercontent.com/dhall-lang/dhall-lang/64e1ff6b6e27eb5633e2e803fe8f9d2c6e7c624b/Prelude/List/map

in  let OperatingSystem = < Linux : {} | OSX : {} >

in  let operatingSystem = constructors OperatingSystem

in  let Addon = { apt : { packages : List Text, sources : List Text } }

in  let Include =
          { env :
              Text
          , compiler :
              Optional Text
          , addons :
              Optional Addon
          , os :
              Optional Text
          }

in  let makeInclude =
            λ(args : { ghc : Text, cabal : Text, os : OperatingSystem })
          →   { env =
                  "CABALVER=${args.cabal} GHCVER=${args.ghc}"
              , compiler =
                  [] : Optional Text
              , addons =
                  merge
                  { Linux =
                        λ(_ : {})
                      → [ { apt =
                              { packages =
                                  [ "cabal-install-${args.cabal}"
                                  , "ghc-${args.ghc}"
                                  , "libglpk-dev"
                                  , "libntl-dev"
                                  , "libboost-all-dev"
                                  ]
                              , sources =
                                  [ "hvr-ghc" ]
                              }
                          }
                        ] : Optional Addon
                  , OSX =
                      λ(_ : {}) → [] : Optional Addon
                  }
                  args.os
              , os =
                  merge
                  { Linux =
                      λ(_ : {}) → [] : Optional Text
                  , OSX =
                      λ(_ : {}) → [ "osx" ] : Optional Text
                  }
                  args.os
              }
            : Include

in  { language =
        "c"
	, dist = "xenial"
    , sudo =
        False
    , cache =
        { directories =
            [ "\$HOME/.cabsnap", "\$HOME/.cabal/packages", "\$HOME/.ghc" ]
        }
    , git =
        { submodules = True }
    , before_cache =
        [ "rm -fv \$HOME/.cabal/packages/hackage.haskell.org/build-reports.log"
        , "rm -fv \$HOME/.cabal/packages/hackage.haskell.org/00-index.tar"
        ]
    , matrix =
        { include =
            [ makeInclude
              { ghc = "8.6.3", cabal = "2.4", os = operatingSystem.Linux {=} }
            , makeInclude
              { ghc = "8.4.3", cabal = "2.4", os = operatingSystem.Linux {=} }
            , makeInclude
              { ghc = "8.6.3", cabal = "2.4", os = operatingSystem.OSX {=} }
            ]
        }
    , before_install =
        [ "unset CC"
        , "export PATH=/opt/ghc/\$GHCVER/bin:/opt/cabal/\$CABALVER/bin:\$PATH"
        , "if [ \$TRAVIS_OS_NAME = osx ]; then brew update; brew install ghc; brew install ntl glpk cabal-install; fi"
        ]
    , script =
        [ "cabal update"
		-- We don't build crucible-server, it requires hpb
        , "cabal new-build crucible{,-jvm,-llvm,-saw,-syntax} crux{,-llvm} what4{,-abc,-blt} -j --disable-optimization --allow-newer"
        ]
    }
