# `crux-llvm-svcomp`

This is an alternative to `crux-llvm` that is specifically tailored to the
needs of the
[Competition on Software Verification (SV-COMP)](https://sv-comp.sosy-lab.org).
This document describes various workflows that are useful in creating and using
`crux-llvm-svcomp`.

## Create a bindist for SV-COMP

SV-COMP has very particular requirements for participant bindist, so for this
reason, we have curated a separate script for producing a `crux-llvm-svcomp`
bindist for SV-COMP purposes. To run the script, perform the following steps on
a Linux machine:

1. Download a Clang tarball from
   [here](https://releases.llvm.org/download.html). This is done with the aim
   of including certain LLVM binaries in the `crux-llvm-svcomp` bindist so that
   we can be absolutely sure that we are using a specific LLVM version instead
   of relying on the version of LLVM used on a competition machine.

   We most recently tested this with Clang 10.0.0, so we recommend downloading
   that version.
2. Extract the downloaded Clang tarball to the following location:

   ```
   $ mkdir -p <path-to-crucible-repo>/crux-llvm/svcomp/clang
   $ tar -xvf clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz -C <path-to-crucible-repo>/crux-llvm/svcomp/clang
   ```
3. Run the following script, which will build the necessary executables and
   produce a bindist:

   ```
   $ ./mk-svcomp-bindist.sh
   ```

If everything goes as expected, you should now have a file named something like
`crux-llvm-svcomp-2021-08-24-Linux-x86_64.zip`.

## Recreating the SV-COMP competition environment

We have had moderate success recreating the environment under which the SV-COMP
benchmark harness should run by performing the following steps:

1. [Install Docker](https://docs.docker.com/engine/install/).
2. Clone the [`bench-defs`](https://gitlab.com/sosy-lab/sv-comp/bench-defs)
   repo and initialize it with the following commands:

   ```
   $ git clone https://gitlab.com/sosy-lab/sv-comp/bench-defs && cd bench-defs/
   $ git checkout svcomp21 # Or whichever year you want to target
   $ make init
   ```

   Beware that the `sv-benchmarks` repo in particular is quite massive.
   Moreover, many of the files in that repo are especially long (sometimes
   over 150 characters in length), which may pose an issue if you are using an
   encrypted file system that limits the length of file names.
3. Make a note of where you cloned `bench-defs`. Navigate to the `docker`
   subdirectory, open the `Makefile`, and replace the value of `BENCH_DEFS_DIR`
   with the location of where you cloned `bench-defs`.
4. From within the `docker` directory, run `make`. This will build a Docker
   image suitable for running the SV-COMP benchmark harness and start a
   container from within `bench-defs`.

## Preparing the necessary files for SV-COMP benchmark runs

Before you can actually run Crux in an SV-COMP competition environment, you
will need to prepare three files:

1. A `.zip` file containing the `crux-llvm-svcomp` bindist and friends. For
   instructions on how to do this, refer to the "Create a bindist for SV-COMP"
   section.
2. A `crux.xml` benchmark definition file containing the metadata for the
   `crux-llvm-svcomp` tool and which benchmarks programs it will run.
   TODO: Add a link to `crux.xml` once it has been upstreamed.
3. A `crux.py` tool module that informs `benchexec` (SV-COMP's benchmark
   harness) how to invoke `crux-llvm-svcomp` and how to interpret its results.
   TODO: Add a link to `crux.py` once it has been upstreamed.

You will need to put each of these files in particular locations under your
checkout of `bench-defs` (see the "Recreating the SV-COMP competition environment"
section):

1. Put the `.zip` file in `bench-defs/archives/2021/crux.zip`.
2. Put the `crux.xml` file in `bench-defs/benchmark-defs/crux.xml`.
3. Put the `crux.py` file in `bench-defs/benchexec/benchexec/tools/crux.py`.

## Executing an SV-COMP benchmark run

From within an SV-COMP competition Docker container (see the
"Recreating the SV-COMP competition environment" section), run the following
command:

```
$ ./scripts/execute-runs/mkInstall.sh crux crux-path
```

For whatever reason, the secon argument (ostensibly the path to extract to)
doesn't seem to actually get used in practice, and the directory it will
_actually_ be extracted to is the basename of the Crux `.zip` file itself.
Navigate into this newly extracted directory and run the following:

```
$ PYTHONPATH=../benchexec python3 -m benchexec.benchexec -r SV-COMP21_unreach-call ../benchmark-defs/crux.xml
```

This will start a run of the `SV-COMP21_unreach-call` benchmark definition as
defined in `../benchmark-defs/crux.xml`. (See the "Preparing the necessary
files for SV-COMP benchmark runs" section.) To execute a different benchmark
definition, change the argument to `-r`.
