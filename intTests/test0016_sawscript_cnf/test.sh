set -e
. ../sat.sh
mkdir -p tmp

$SAW test.saw
sat "tmp/x__x.cnf"
unsat "tmp/x__x1.cnf"
sat "tmp/x__y.cnf"
sat "tmp/x_not_y.cnf"
unsat "tmp/xx_not_2x.cnf"

rm -rf tmp
