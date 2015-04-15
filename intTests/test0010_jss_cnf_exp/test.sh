set -e
. ../sat.sh
mkdir -p tmp

$JSS Test
unsat "tmp/exp.cnf"

$JSS --usesaw Test
unsat "tmp/exp.cnf"

rm -rf tmp
