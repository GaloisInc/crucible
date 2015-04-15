set -e
. ../sat.sh
mkdir -p tmp

$LSS test.bc
unsat "tmp/exp.cnf"

$LSS --backend=saw test.bc
unsat "tmp/exp.cnf"

rm -rf tmp
