# GitHub Actions workflows

We currently build and test a subset of the packages in the `crucible` repo
on CI, whose CI configurations are located here. We use the following
conventions when picking with operating systems to test:

* For each project, we test the latest LTS release of Ubuntu on the three most
  recent stable releases of GHC.
* In addition, we also test the previous LTS release of Ubuntu on the
  `crux-llvm-build.yml` and `crux-mir-build.yml` workflows, but only using a
  single version of GHC.
* For each project, we test macOS and Windows only using a single version of
  GHC. This is because the turnaround time for macOS and Windows builders on
  GitHub Actions is longer, so we try to avoid bottlenecking CI workflows on
  these operating systems.

  Note that:

  * We do not currently run LLVM-related tests on Windows, as it is not
    straightforward to obtain Windows builds of LLVM that include all of the
    developer tools that we need, such as `llvm-link` and `llvm-as`.
  * We do not currently run MIR-related tests on Windows, as it is not
    straightforward to install `mir-json` on Windows.
