#!/bin/bash
set -e
DIRS="galois-matlab/src crucible/src galois-mss/src galois-mss/mss"
DIRS="crucible/src"

# make sure graphmod and dot are in the PATH
if ! type -p graphmod || ! type -p dot; then
    echo "Error: cannot find 'graphmod' and/or 'dot' in PATH" 1>&2
    exit 1
fi

run_graphmod()
{
    local dir="$1"
    local name="$2"
    local FILES="$(find $dir -name '*.hs')"
    echo "Writing graphmod file to $2.svg"
    graphmod -i $dir -p --no-cluster $FILES -q | dot -Tsvg > $2.svg
}

run_graphmod "galois-matlab/src" "galois-matlab"
run_graphmod "crucible/src" "crucible"
