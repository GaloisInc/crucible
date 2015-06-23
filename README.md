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

  * Ensure you have the programs `alex`, `happy`, and `c2hs`. All of
    them can be installed with `cabal install`. If you do that, make
    sure `$HOME/.cabal/bin` is in your `PATH`.

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms.

  * Ensure that you have the programs `javac` and `cvc4` on your
    `PATH`. CVC4 binaries are available at http://cvc4.cs.nyu.edu/downloads/.

  * Optionally, create a `build-sandbox-version-pins.txt` and pin the
    revisions of dependencies as necessary by adding lines like
    
        <dependency name> <committish>
    
    See the `pin` function in `build-sandbox.sh` for more details. The release
    branches already include a known-to-work `build-sandboxy-versions-pins.txt`,
    so you can get a stable build by checking out a release branch (e.g.
    `git checkout release-0.1-dev`).

  * Build SAWScript by running
    
        ./build-sandbox.sh -p
    
    The executables will be created in `./build/bin`; you can now
    start the SAWScript interpreter by running `./build/bin/saw`.

    The `-p` flag tells it to pull the latest updates from any
    dependency repositories. You can omit `-p`, and speed up the
    build slightly, if you know that they haven't changed.

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
