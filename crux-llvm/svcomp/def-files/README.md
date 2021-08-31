This directory contains two files which define Crux as used in SV-COMP's
benchmark harness:

* `crux.xml`: This is the benchmark definition that states which run
  definitions and tasks Crux should participate in. The benchmark definition is
  also a convenient place to configure `crux-llvm-svcomp` options that should
  only be used for specific run definitions or tasks (e.g., Crux configuration
  files).

  This is ultimately destined to be placed in the
  https://gitlab.com/sosy-lab/sv-comp/bench-defs repo under the
  `benchmark-defs` directory.
* `crux.py`: This is a Python module that informs `benchexec` (SV-COMP's benchmark
  executor) how to invoke `crux-llvm-svcomp` and how to interpret its results.
  This is responsible for converting the information in a benchmark program's
  `.yml` file to Crux-appropriate command-line arguments
  (e.g., `--svcomp-arch`). It is also responsible for parsing the output of
  `crux-llvm-svcomp` to determine which `RESULT_*` string to return.

  This is ultimately destined to be placed in the
  https://github.com/sosy-lab/benchexec repo under the `benchexec/tools`
  directory.
