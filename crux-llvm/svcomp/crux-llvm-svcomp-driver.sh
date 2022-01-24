#!/bin/env bash

TOOL_NAME=crux-llvm-svcomp
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

ARGUMENTS=()
while [[ $# -gt 0 ]]; do
  OPTION="$1"

  case $OPTION in
    --svcomp-spec)
      SPEC="$2"
      ARGUMENTS+=("$1")
      ARGUMENTS+=("$2")
      shift
      shift
      ;;
    *)
      ARGUMENTS+=("$1")
      shift
      ;;
  esac
done

set -- "${ARGUMENTS[@]}"

if [ -n "${SPEC}" ]; then
  if [ ! -f "${SPEC}" ]; then
    echo "SV-COMP specification file not found: ${SPEC}"
    exit 1
  fi

  # The regexes used below are taken from CPAChecker:
  #
  #   https://github.com/sosy-lab/cpachecker/blob/2cfbe22b515fe9fedbd7629c62e9b93ddeda0a9a/scripts/cpa_witness2test.py
  #
  # Licensed under the Apache License 2.0:
  #
  #   https://github.com/sosy-lab/cpachecker/blob/5201be95111567d8cd577e6d2edbc13f04cf99f8/LICENSE
  SPEC_REGEX_MAIN="CHECK\(\s*init\(.*\),\s*LTL\(\s*(.+)\s*\)"
  SPEC_REGEX_OVERFLOW="G\s*!\s*overflow"
  SPEC_REGEX_REACH="G\s*!\s*call\(\s*([a-zA-Z0-9_]+)\s*\(\)\s*\)"
  SPEC_CONTENTS=$(cat "${SPEC}")
  if [[ "${SPEC_CONTENTS}" =~ ${SPEC_REGEX_MAIN} ]]; then
    if [[ "${SPEC_CONTENTS}" =~ ${SPEC_REGEX_OVERFLOW} ]]; then
      CONFIG_ARG="${SCRIPT_DIR}/no-overflow.config"
    elif [[ "${SPEC_CONTENTS}" =~ ${SPEC_REGEX_REACH} ]]; then
      CONFIG_ARG="${SCRIPT_DIR}/unreach-call.config"
    else
      echo "SV-COMP specification in ${SPEC} not currently supported"
      exit 1
    fi
  else
    echo "No SV-COMP specification found in ${SPEC}"
    exit 1
  fi
fi

PATH=${SCRIPT_DIR}/bin:$PATH ${TOOL_NAME} ${1+"$@"} --config "${CONFIG_ARG}"
