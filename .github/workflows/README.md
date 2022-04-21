# GitHub Actions workflows

We currently build and test a subset of the packages in the `crucible` repo
on CI, whose CI configurations are located here. We use the following
conventions when picking with operating systems to test:

* For each project, we test the latest LTS release of Ubuntu on all supported
  versions of GHC.
* In addition, we also test the previous LTS release of Ubuntu on the
  `crux-llvm-build.yml` workflow, but only using the latest supported version
  of GHC.
* For each project, we test macOS only using the latest
  supported version of GHC. This is because the turnaround time for macOS
  builders on GitHub Actions is longer, so we try to avoid
  bottlenecking CI workflows on macOS builds.

  In the future, we wish to test Windows using the latest supported version
  of GHC as well.
