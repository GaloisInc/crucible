This repo holds code for SAWScript. Many dependencies are checked out
into `deps/` when you build using `build-sandbox.sh`; see below.

Dependencies include:

* `deps/cryptol-verifier/`: Cryptol Symbolic Simulator (CSS)
* `deps/jvm-verifier/`:     Java Symbolic Simulator (JSS)
* `deps/llvm-verifier/`:    LLVM Symbolic Simulator (LSS)
* `deps/saw-core/`:         SAWCore intermediate language, used by LSS, JSS, and SAWScript

To build SAWScript, CSS, LSS, and JSS together:

  * Ensure you have the programs `alex`, `happy`, and `c2hs`. All of
    them can be installed with `cabal install`. If you do that, make
    sure `$HOME/.cabal/bin` is in your `PATH`.

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms.

  * Ensure that you have the programs `javac` and `cvc4` on your
    PATH. CVC4 binaries are available at http://cvc4.cs.nyu.edu/downloads/.

  * Optionally, create a `build-sandbox-version-pins.txt` and pin the
    revisions of dependencies as necessary by adding lines like
    
        <dependency name> <committish>
    
    See the `pin` function in `build-sandbox.sh` for more details.

  * Build SAWScript by running
    
        ./build-sandbox.sh -p
    
    The executables will be created in `./build/bin`; you can now
    start the SAWScript interpreter by running `./build/bin/saw`.

    The `-p` flag tells it to pull the latest updates from any
    dependency repositories. You can omit `-p`, and speed up the
    build slightly, if you know that they haven't changed.

  * Optionally, run ./stage.sh to create a binary tarball.

The SAWScript tutorial, [doc/tutorial/sawScriptTutorial.pdf]
(https://github.com/GaloisInc/saw-script/raw/master/doc/tutorial/sawScriptTutorial.pdf),
will give you an introduction to using the SAWScript interpreter.
