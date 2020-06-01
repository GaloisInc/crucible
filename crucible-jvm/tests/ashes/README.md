How to run the ashes test suite.

1. Use `get_ashes.sh` to download the suite

2. compile crucible-jvm   (`cabal new-build` in `saw-script/deps/crucible/crucible-jvm/`)

3. make sure that `runcrucible.sh` includes correct reference to `rt.jar` for your
   system (and the correct reference to the crucible-jvm executable)

4. `./runAshes.hs`

5. To run a single test, ghci runAshes.hs and then edit `wip` to that test name.

These instructions assume that you are using cabal new-build to
compile crucible-jvm. If using stack, need to edit `runcrucible.sh` to
the correct way to invoke the crucible-jvm executable.