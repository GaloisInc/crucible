set -e
. ../sat.sh
mkdir -p tmp

$LSS --backend=saw test.bc
$SAW test.saw

rm -rf tmp
