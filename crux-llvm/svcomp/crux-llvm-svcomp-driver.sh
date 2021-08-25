#!/bin/env bash

TOOL_NAME=crux-llvm-svcomp
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

PATH=${SCRIPT_DIR}/bin:$PATH ${TOOL_NAME} ${1+"$@"}
