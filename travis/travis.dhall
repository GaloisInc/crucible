    let schema = ./schema.dhall

in  let map =
          https://raw.githubusercontent.com/dhall-lang/dhall-lang/64e1ff6b6e27eb5633e2e803fe8f9d2c6e7c624b/Prelude/List/map

in  let OperatingSystem = < Linux : {} | OSX : {} >

in  let operatingSystem = constructors OperatingSystem

in  let Include =
          { env :
              Text
          , compiler :
              Optional Text
          , addons :
              Optional schema.Addon
          , os :
              Optional Text
          }

in  let MakeIncludeArgs = { ghc : Text, cabal : Text, os : OperatingSystem }

in  let makeInclude =
            λ(args : MakeIncludeArgs)
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
                        ] : Optional schema.Addon
                  , OSX =
                      λ(_ : {}) → [] : Optional schema.Addon
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

in    { language =
          "c"
      , dist =
          [ "xenial" ] : Optional Text
      , sudo =
          False
      , cache =
          [ { directories =
                [ "\$HOME/.cabsnap", "\$HOME/.cabal/packages", "\$HOME/.ghc" ]
            }
          ] : Optional { directories : List Text }
      , git =
          [ { submodules = True } ] : Optional { submodules : Bool }
      , before_cache =
          [ [ "rm -fv \$HOME/.cabal/packages/hackage.haskell.org/build-reports.log"
            , "rm -fv \$HOME/.cabal/packages/hackage.haskell.org/00-index.tar"
            ]
          ] : Optional (List Text)
      , matrix =
          [ { include =
                  map
                  MakeIncludeArgs
                  Include
                  makeInclude
                  [ { ghc =
                        "8.6.3"
                    , cabal =
                        "2.4"
                    , os =
                        operatingSystem.Linux {=}
                    }
                  , { ghc =
                        "8.4.3"
                    , cabal =
                        "2.4"
                    , os =
                        operatingSystem.Linux {=}
                    }
                  , { ghc =
                        "8.6.3"
                    , cabal =
                        "2.4"
                    , os =
                        operatingSystem.OSX {=}
                    }
                  ]
                : List Include
            , fast_finish =
                [ True ] : Optional Bool
            }
          ] : Optional schema.Matrix
      , before_install =
          [ [ "unset CC"
            , "export PATH=/opt/ghc/\$GHCVER/bin:/opt/cabal/\$CABALVER/bin:\$PATH"
            , "if [ \$TRAVIS_OS_NAME = osx ]; then brew update; brew install ghc; brew install ntl glpk cabal-install; fi"
            ]
          ] : Optional (List Text)
      , script =
          [ [ "cabal update"
            , "cabal new-build crucible{,-jvm,-llvm,-saw,-syntax} crux{,-llvm} what4{,-abc,-blt} -j --disable-optimization --allow-newer"
            ]
          ] : Optional (List Text)
      }
    : schema.Travis