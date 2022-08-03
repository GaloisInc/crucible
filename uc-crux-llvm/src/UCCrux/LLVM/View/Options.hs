{-
Module           : UCCrux.LLVM.View.Options
Description      : 'Data.Aeson.Options' used to derive JSON instances
Copyright        : (c) Galois, Inc 2022
License          : BSD3
Maintainer       : Langston Barrett <langston@galois.com>
Stability        : provisional

These modules export the 'Data.Aeson.Options' passed to
'Data.Aeson.TH.deriveJSON' for each "view" type. Since these influence the
serialized representation, these details are necessarily public. Also, they are
useful to library clients such as those using the aeson-typescript package,
which requires that its @TypeScript@ instances be generated using the same
'Data.Aeson.Options' as the corresponding JSON instances.

These must be in separate modules from the corresponding types due to staging
restrictions from the use of Template Haskell to generate the JSON instances.

For details on how these options are constructed, see
"UCCrux.LLVM.View.Options.Idioms".
-}

module UCCrux.LLVM.View.Options () where
