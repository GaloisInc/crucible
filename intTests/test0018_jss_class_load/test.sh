set -e

$JSS -c a:b org/example/Test
$JSS -c a:b com/example/Test

# These should timeout for JSS where
# https://github.com/GaloisInc/jvm-verifier/issues/3 is not fixed.
cp=$(pwd)/a:$(pwd)/b:/
(cd / && $JSS -c "$cp" org/example/Test)
(cd / && $JSS -c "$cp" com/example/Test)
(cd / && $SAW -c "$cp" /dev/null)
