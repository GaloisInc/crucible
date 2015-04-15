set -e
. ../sat.sh
mkdir -p tmp

$LSS --backend=saw lss_saw_backend_test.bc
$LSS               lss_default_backend_test.bc
$SAW test.saw

rm -rf tmp
