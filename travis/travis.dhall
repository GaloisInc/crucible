    let schema = ./schema.dhall

in  let map =
          https://raw.githubusercontent.com/dhall-lang/dhall-lang/v5.0.0/Prelude/List/map

in  let concatSep =
          https://raw.githubusercontent.com/dhall-lang/dhall-lang/v5.0.0/Prelude/Text/concatSep

in  let bShow =
          https://raw.githubusercontent.com/dhall-lang/dhall-lang/v5.0.0/Prelude/Bool/show

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

in  let MakeIncludeArgs =
          { ghc :
              Text
          , cabal :
              Text
          , os :
              OperatingSystem
          , buildArg :
              Text
          , doLint :
              Bool
          }

in  let makeEnv =
            λ(args : MakeIncludeArgs)
          →   concatSep
              " "
              [ "CABALVER=${args.cabal}"
              , "GHCVER=${args.ghc}"
              , "BUILD_ARG=${args.buildArg}"
              , "DO_LINT=${bShow args.doLint}"
              ]
            : Text

in  let makeInclude =
            λ(args : MakeIncludeArgs)
          →   { env =
                  makeEnv args
              , compiler =
                  [] : Optional Text
              , addons =
                        if args.doLint
                  
                  then  [] : Optional schema.Addon
                  
                  else  merge
                        { Linux =
                              λ(_ : {})
                            → [ { apt =
                                    [ { packages =
                                          [ "cabal-install-${args.cabal}"
                                          , "ghc-${args.ghc}"
                                          , "libglpk-dev"
                                          , "libntl-dev"
                                          , "libboost-all-dev"
                                          ]
                                      , sources =
                                          [ "hvr-ghc" ]
                                      }
                                    ] : Optional schema.AddonApt
                                , homebrew =
                                    [] : Optional schema.AddonBrew
                                }
                              ] : Optional schema.Addon
                        , OSX =
                              λ(_ : {})
                            → [ { apt =
                                    [] : Optional schema.AddonApt
                                , homebrew =
                                    [ { packages =
                                          [ "ghc"
                                          , "ntl"
                                          , "glpk"
                                          , "cabal-install"
                                          ]
                                      , update =
                                          True
                                      }
                                    ] : Optional schema.AddonBrew
                                }
                              ] : Optional schema.Addon
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

in  let allowNewer =
            { ghc =
                "8.6.3"
            , cabal =
                "2.4"
            , os =
                operatingSystem.Linux {=}
            , buildArg =
                "--allow-newer"
            , doLint =
                False
            }
          : MakeIncludeArgs

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
                    , buildArg =
                        ""
                    , doLint =
                        False
                    }
                  , { ghc =
                        "8.4.3"
                    , cabal =
                        "2.4"
                    , os =
                        operatingSystem.Linux {=}
                    , buildArg =
                        ""
                    , doLint =
                        False
                    }
                  , { ghc =
                        "8.6.3"
                    , cabal =
                        "2.4"
                    , os =
                        operatingSystem.OSX {=}
                    , buildArg =
                        ""
                    , doLint =
                        False
                    }
                  , { ghc =
                        "8.6.3"
                    , cabal =
                        "2.4"
                    , os =
                        operatingSystem.Linux {=}
                    , buildArg =
                        ""
                    , doLint =
                        True
                    }
                  , allowNewer
                  ]
                : List Include
            , allow_failures =
                [ [ { env =
                        makeEnv allowNewer : Text
                    , compiler =
                        [] : Optional Text
                    , addons =
                        [] : Optional schema.Addon
                    , os =
                        [] : Optional Text
                    }
                  ]
                ] : Optional (List Include)
            , fast_finish =
                [ True ] : Optional Bool
            }
          ] : Optional schema.Matrix
      , before_install =
          [ [ "unset CC"
            , "export PATH=/opt/ghc/\$GHCVER/bin:/opt/cabal/\$CABALVER/bin:\$PATH"
            ]
          ] : Optional (List Text)
      , script =
          [     let cond =
                        λ(cond : Text)
                      → λ(step : Text)
                      →   concatSep " " [ "if ${cond}; then", step, ";", "fi" ]
                        : Text
            
            in  let doLint = cond "[[ \$DO_LINT == True ]]"
            
            in  let noLint = cond "[[ \$DO_LINT != True ]]"
            
            in  [ noLint
                  "cabal new-update"
                ,     let hlintURL =
                            "https://raw.github.com/ndmitchell/neil/master/misc/travis.sh"
                  
                  in  let pkgs =
                            "crucible{,-jvm,-llvm,-saw,-server,-syntax} crux{,-llvm} what4{,-abc,-blt}"
                  
                  in  doLint "curl -sSL ${hlintURL} | sh -s -- hlint ${pkgs}"
                , noLint
                  "cabal new-build crucible{,-jvm,-llvm,-saw,-syntax} crux{,-llvm} what4{,-abc,-blt} -j --disable-optimization \$BUILD_ARG"
                ]
          ] : Optional (List Text)
      }
    : schema.Travis