set -e
. ../sat.sh
mkdir -p tmp

$SAW test.saw

rm -rf tmp
