#!/bin/env bash

PATH=/home/rscott/Software/clang+llvm-10.0.0-x86_64-linux-gnu-ubuntu-18.04/bin:$PATH RUNNER_OS=Linux OS_TAG=ubuntu-20.04 .github/ci.sh bundle_crux_llvm_files
