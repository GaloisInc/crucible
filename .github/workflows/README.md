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

Other notes:

* Workflow steps that depend on secrets (signing keys, access tokens,
  etc.) or that do things that only make sense in the context of the
  main repository need to be restricted so they aren't run in other
  contexts.

  It is apparently impossible to restrict scheduled workflows to the
  original/parent repository; they will always also run in forks. See
  [this discussion](https://github.com/orgs/community/discussions/16109).

  Therefore while it's sometimes necessary/desirable to skip steps
  when working on a pull request, it's not sufficient for scheduled
  workflows. In particular, the condition
  ```github.event.pull_request.head.repo.fork == false``` isn't
  sufficient.

  Steps that require secrets should check the repository owner
  (```github.repository_owner == 'GaloisInc'```). Checking the
  repository identity (```github.repository == 'GaloisInc/crucible'```)
  is also possible but less maintainable/robust/etc.

  It isn't absolutely clear whether it's necessary to _also_ check the
  pull request fork flag. For the time being we do so, partly to avoid
  unforeseen complications and partly because this is what some other
  projects apparently do.
