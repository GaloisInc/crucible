set -e

$JSS -c a${CPSEP}b org/example/Test
$JSS -c a${CPSEP}b com/example/Test

# These should timeout for JSS where
# https://github.com/GaloisInc/jvm-verifier/issues/3 is not fixed,
# since JSS will attempt to load all '.class' files it can find at or
# below the root directory.
cp=$(pwd)${DIRSEP}a${CPSEP}$(pwd)${DIRSEP}b${CPSEP}.
(cd / && $JSS -c "$cp" org/example/Test)
(cd / && $JSS -c "$cp" com/example/Test)
(cd / && $SAW -c "$cp" /dev/null)
