set -e
. ../sat.sh
mkdir -p tmp

$JSS --usesaw Test
$SAW test.saw

rm -rf tmp
