# Travis CI

Our Travis configuration is generated from the
[Dhall](https://github.com/dhall-lang/dhall-lang) configurations in this
directory.

 - [`schema.dhall`](./schema.dhall) describes the structure (type) of a Travis
   configuration
 - [`travis.dhall`](./travis.dhall) describes our particular Travis
   configuration.

Generate `../.travis.yml` with `./gen.sh`.
