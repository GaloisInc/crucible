#!/bin/bash

# This script runs the test suites for everything in the stack.yaml
# file, then generates a coverage report for all the sub-projects
# together. Testing on a small project shows that this does indeed
# take one sub-project's invocation by another sub-project's test
# suite into account when determining coverage; thus, it is fair with
# respect to the division of responsibility between e.g. crucible and
# crucible-syntax.

stack test --coverage
stack hpc report \
      crucible crucible-syntax crux-llvm \
      crucible-jvm crucible-llvm crucible-saw \
      crux what4 \
      what4-abc what4-blt
