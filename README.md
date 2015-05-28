This repo holds code for SAWScript. Many dependencies are checked out
into `deps/` when you build using `build-sandbox.sh`; see below.

Dependencies include:

`deps/cryptol-verifier/` : Cryptol Symbolic Simulator (CSS)
`deps/jvm-verifier/`     : Java Symbolic Simulator (JSS)
`deps/llvm-verifier/`    : LLVM Symbolic Simulator (LSS)
`deps/saw-core/`         : SAWCore intermediate language, used
                           by LSS, JSS, and SAWScript

To build SAWScript, CSS, LSS, and JSS together:

  * Ensure you have the programs `alex`, `happy`, and `c2hs`. All of
    them can be installed with `cabal install`. If you do that, make
    sure $HOME/.cabal/bin is in your PATH.

  * Ensure that you have the C libraries and header files for
    `terminfo`, which generally comes as part of `ncurses` on most
    platforms.

  * Ensure that you have the programs `javac` and `cvc4` on your
    PATH. CVC4 binaries are available here:
    http://cvc4.cs.nyu.edu/downloads/

  * Optionally, create a `build-sandbox-version-pins.txt` and pin the
    revisions of dependencies as necessary by adding lines like

      <dependency name> <committish>

    See the `pin` function in `build-sandbox.sh` for more details.

  * Run the following command:

      ./build-sandbox.sh -p

    where the -p flag tells it to pull the latest updates from any
    dependency repositories. You can leave it out, and speed up the
    build slightly, if you know that they haven't changed.

  * Optionally, run ./stage.sh to create a binary tarball

Once the build is complete, the SAWScript tutorial will give you an
introduction to using the SAWScript interpreter.

    doc/tutorial/sawScriptTutorial.pdf
