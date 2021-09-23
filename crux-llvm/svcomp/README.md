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
   `crux-llvm-svcomp` tool and which benchmarks programs it will run. This is
   located under `<path-to-crucible-repo>/crux-llvm/svcomp/def-files`.
3. A `crux.py` tool module that informs `benchexec` (SV-COMP's benchmark
   executor) how to invoke `crux-llvm-svcomp` and how to interpret its results.
   This is located under `<path-to-crucible-repo>/crux-llvm/svcomp/def-files`.

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
definition, change the argument to `-r`. When the run is complete, it will
place various files under the `results/` directory, including:

* `crux.<date>.results.<benchmark-definition>.txt`, a human-readable summary
  of the run which contains the status of each individual benchmark and a
  total score at the bottom.
* `crux.<date>.results.<benchmark-definition>.xml.bz2`, an archive file
  containing an XML file which much more information about the run. If you
  want to perform analysis over the run results, this is the file you want.
* `crux.<date>.files/`, a directory containing the witness automaton files that
  `crux-llvm-svcomp` produced for each individual benchmark.
* `crux.<date>.logfiles.zip`, an archive file containing the logs that were
  recorded for each individual benchmark. This information can be useful after
  the run to figure out why certain benchmark programs produce unexpected
  results.

## Scoring an SV-COMP benchmark run

`benchexec` will compute a total score for each run that awards points for
correct verdicts and deducts points for incorrect verdicts. The most convenient
place to find this score is at the bottom of the
`results/crux.<date>.results.<benchmark-definition>.txt` file, which will look
something like this:

```
Statistics:            631 Files
  correct:             277
    correct true:       67
    correct false:     210
  incorrect:             2
    incorrect true:      0
    incorrect false:     2
  unknown:             352
  Score:               312 (max: 998)
```

There is one major caveat here: these scores do _not_ take witness automaton
files into account. As a result, the score reported in this file is more like
an upper bound on what the total score will be. In order to compute the score
after taking witnesses into account, you will need to do the following:

1. Use the `./scripts/execute-runs/mkInstall.sh` script to check out the
   witness validator programs. They are:

   * `val_cpa-seq`
   * `val_cpa-witness2test`
   * `val_fshell-witness2test`
   * `val_metaval`
   * `val_nitwit`
   * `val_uautomizer`
   * `val_witnesslint`

   `val_witnesslint` is a bit special in that it only checks to see if a
   witness automaton is syntactically well formed and adheres to the
   requirements listed [here](https://github.com/sosy-lab/sv-witnesses/blob/20414d976d9e46da6a93be38c34237f71a01033f/README.md#data-elements).
   It's a good idea to make sure that `val_witnesslint` accepts a witness
   automaton that Crux produces, but if it accepts one, it will almost
   assuredly accept them all.
2. Witness validators are invoked by way of `benchexec` much like verifiers
   are. To that end, each validator has its own `.xml` definition file inside
   `bench-defs/benchmark-defs/`. These `.xml` files specify where a validator
   should look for witness automaton files.

   In order to point the validators at the right locations to find these files,
   you will need to go into each `.xml` files and edit them accordingly. (Yes,
   this is an extremely tedious process. It would be nice if we could find a
   way to automate this.) For example, inside of
   `cpa-seq-validate-correctness-witnesses.xml` you will find
   [these lines](https://gitlab.com/sosy-lab/sv-comp/bench-defs/-/blob/a9bfd363f1c222165e09708585c5fdcfa1d47495/benchmark-defs/cpa-seq-validate-correctness-witnesses.xml#L87-89):

   ```xml
   <rundefinition name="SV-COMP21_no-overflow">
     <requiredfiles>../results-verified/LOGDIR/${rundefinition_name}.${taskdef_name}/witness.graphml</requiredfiles>
     <option name="-witness">../../results-verified/LOGDIR/${rundefinition_name}.${taskdef_name}/witness.graphml</option>
     ...
   </rundefinition>
   ```

   You will need to change the `<requiredfiles>` and `<option name="-witness">`
   bits to point to where your witness automaton files live. In my case, I was
   used something like:

   ```xml
   <rundefinition name="SV-COMP21_no-overflow">
     <requiredfiles>../crux-llvm-svcomp-2021-09-15-Linux-x86_64/results/crux.2021-09-16_02-25-33.files/${rundefinition_name}/${taskdef_name}/witness.graphml</requiredfiles>
     <option name="-witness">../crux-llvm-svcomp-2021-09-15-Linux-x86_64/results/crux.2021-09-16_02-25-33.files/${rundefinition_name}/${taskdef_name}/witness.graphml</option>
     ...
   </rundefinition>
   ```

   You will need to repeat this process for each `<rundefinition>` for which
   you have results for in each of these files:

   * `cpa-seq-validate-correctness-witnesses.xml`
   * `cpa-seq-validate-violation-witnesses.xml`
   * `cpa-witness2test-validate-violation-witnesses.xml`
   * `fshell-witness2test-validate-violation-witnesses.xml`
   * `metaval-validate-correctness-witnesses.xml`
   * `metaval-validate-violation-witnesses.xml`
   * `nitwit-validate-violation-witnesses.xml`
   * `uautomizer-validate-correctness-witnesses.xml`
   * `uautomizer-validate-violation-witnesses.xml`
3. Use `benchexec` to run each of the witness validators. I have checked in a
   `benchexec-util-scripts/validate-witnesses.sh` script that I use to automate
   this process.
4. Each validators' `results/` directories will now have information about
   witness validity that needs to be pieced together. The `benchexec` repo has
   a [`mergeBenchmarkSets.py`](https://github.com/sosy-lab/benchexec/blob/344eb314bad07142a8ff0cebc2eae9502470ef60/contrib/mergeBenchmarkSets.py)
   script that does this for you. This script takes the original run's
   `.xml.bz2` file (containing the results of the run) as its first argument,
   and each subsequent argument is an `.xml.bz2` file containing results from
   a witness validator. Here is one example of how to invoke it:

   ```bash
   PYTHONPATH=benchexec-master python3 -m contrib.mergeBenchmarkSets /home/bench-defs/crux-llvm-svcomp-2021-09-15-Linux-x86_64/results/crux.2021-09-16_02-25-33.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_cpa-seq/results/cpa-seq-validate-correctness-witnesses.2021-09-21_19-28-15.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_cpa-seq/results/cpa-seq-validate-violation-witnesses.2021-09-21_20-48-27.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_cpa-witness2test/results/cpa-witness2test-validate-violation-witnesses.2021-09-21_21-36-02.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_fshell-witness2test/results/fshell-witness2test-validate-violation-witnesses.2021-09-21_21-50-30.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_metaval/results/metaval-validate-correctness-witnesses.2021-09-21_21-59-19.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_metaval/results/metaval-validate-violation-witnesses.2021-09-22_01-25-21.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_uautomizer/results/uautomizer-validate-correctness-witnesses.2021-09-22_02-20-16.results.SV-COMP21_no-overflow.xml.bz2 /home/bench-defs/val_uautomizer/results/uautomizer-validate-violation-witnesses.2021-09-22_09-45-00.results.SV-COMP21_no-overflow.xml.bz2
   ```

   This produce a `crux.<date>.results.<benchmark-definition>.xml.bz2.merged.xml.bz2`
   file in the same `results/` directory as the original
   `crux.<date>.results.<benchmark-definition>.xml.bz2`. This can be used to
   compute a revised total score in one of two ways. The first way is to use
   the `benchexec-util-scripts/CountScore.hs` script, which will output the
   total score in a textual format:

   ```bash
   $ ./CountScore.hs /home/rscott/bench-defs/crux-llvm-svcomp-2021-09-15-Linux-x86_64/results/crux.2021-09-16_02-25-33.results.SV-COMP21_no-overflow.xml.bz2.merged.xml.bz2
   Statistics:                     631 Files
     correct:                      249
       correct true:               61
       correct false:              188
     correct-unconfirmed:          28
       correct-unconfirmed true:   6
       correct-unconfirmed false:  22
     incorrect:                    2
       incorrect true:             0
       incorrect false:            2
     unknown:                      352
   Score:                          278 (max: 998)
   ```

   Note the new `correct-unconfirmed` category, which corresponds to benchmark
   programs where Crux was able to compute an answer, but no witness validator
   was able to validate the corresponding witness automaton. Each
   `correct-unconfirmed` result is worth zero points, so the total score is
   slightly lower here.

   The second way is to use the `benchexec/bin/table-generator` script. If you
   invoke this script with the `.merged.xml.bz2` file as the argument, it will
   produce an `.html` file that will contain the information above when opened
   in a web browser, among other statistics.
