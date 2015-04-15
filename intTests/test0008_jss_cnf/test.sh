set -e
. ../sat.sh
mkdir -p tmp

$JSS Test
sat "tmp/x__x.cnf"
unsat "tmp/x__x1.cnf"
sat "tmp/x__y.cnf"
sat "tmp/x_not_y.cnf"
unsat "tmp/xx_not_2x.cnf"

$JSS --usesaw Test
sat "tmp/x__x.cnf"
unsat "tmp/x__x1.cnf"
sat "tmp/x__y.cnf"
sat "tmp/x_not_y.cnf"
unsat "tmp/xx_not_2x.cnf"

rm -rf tmp
