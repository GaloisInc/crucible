# SAWScript

This repository contains the code for SAWScript, the scripting
language that forms the primary user interface to the Software
Analysis Workbench (SAW). It provides the ability to reason about
formal models describing the denotation of programs written in
languages such as C, Java, and Cryptol.

## Documentation

The SAWScript tutorial, [doc/tutorial/]
(https://github.com/GaloisInc/saw-script/raw/master/doc/tutorial),
gives an introduction to using the SAWScript interpreter.

## Precompiled Binaries

Precompiled SAWScript binaries for a variety of platforms are available on the [releases page](https://github.com/GaloisInc/saw-script/releases).

## Manual Installation

To build SAWScript and related utilities (CSS, LSS, JSS) from source:

  * Ensure that you have the
    [Stack](https://github.com/commercialhaskell/stack) program on your
    `PATH`. If you don't already have Stack, then `cabal install stack`,
    or download a precompiled binary from
    https://github.com/commercialhaskell/stack/releases.

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms.

  * Ensure that you have the programs `javac` and `z3` on your
    `PATH`. Z3 binaries are available at
    https://github.com/Z3Prover/z3/releases

  * **Developers**:
    optionally, create a `build-sandbox-version-pins.txt` and pin the
    revisions of dependencies as necessary by adding lines like

        <dependency name> <committish>

    See the `pin` function in `build-sandbox.sh` for more details. The release
    branches already include a known-to-work `build-sandbox-versions-pins.txt`,
    so you can get a stable build by checking out a release branch (e.g.
    `git checkout release-0.1-dev`).

    To create a `build-sandbox-versions-pins.txt` for the current
    state of the dependencies, do

        for d in deps/*; \
          do (cd $d && echo -n "$(basename "$d") "; git rev-parse HEAD); \
        done > build-sandbox-version-pins.txt

    and then

        git add --force build-sandbox-version-pins.txt

    if you are in a new release branch.

  * Setup a `stack.yaml` for your OS and preferred GHC.

    Choose one of the Stack YAML config files and link it to
    `stack.yaml`:

        ln -s stack.<ghc version and os>.yaml stack.yaml

    The `stack-<ghc version>-unix.yaml` files are for both Linux and
    OS X.

    (Alternatively, you can

        export STACK_YAML=stack.<ghc version and os>.yaml

    instead of creating a symlink.

    **Developers**: defining a `STACK_YAML` env var also overrides the
    `stack.yaml` file, if any, and so is useful for testing a
    alternative build without permanently changing your default. You
    can even define `STACK_YAML` only for the current command: e.g.

        STACK_YAML=stack.<ghc version and os>.yaml stack build

    will build SAWScript using the given Stack YAML.)

  * Build SAWScript by running

        ./build-sandbox.sh -p

    The `-p` flag tells it to pull the latest updates from any
    dependency repositories. You can omit `-p`, and speed up the
    build slightly, if you know that they haven't changed.

    The SAWScript executables will be created in

        echo `stack path --local-install-root`/bin

    a path under the SAWScript repo. You can install SAWScript into
    a more predictable location by running

        stack install

    which installs into

        stack path --local-bin-path

    which is `$HOME/.local/bin` by default.

  * Optionally, run ./stage.sh to create a binary tarball.

## Related Packages

Many dependencies are automatically downloaded into `deps/` when you
build using `build-sandbox.sh`; see
[Manual Installation](#manual-installation) above. Key automatically
downloaded dependencies include:

* `deps/cryptol-verifier/`: [Cryptol Symbolic Simulator (CSS)](https://github.com/GaloisInc/cryptol-verifier)
* `deps/jvm-verifier/`:     [Java Symbolic Simulator (JSS)](https://github.com/GaloisInc/jvm-verifier)
* `deps/llvm-verifier/`:    [LLVM Symbolic Simulator (LSS)](https://github.com/GaloisInc/llvm-verifier)
* `deps/saw-core/`:         [SAWCore intermediate language](https://github.com/GaloisInc/saw-core), used by CSS, JSS, LSS and SAWScript
* `deps/cryptol/`:          [Cryptol](https://github.com/GaloisInc/cryptol)
* `deps/abcBridge/`:        [Haskell bindings for ABC](https://github.com/GaloisInc/abcBridge)
