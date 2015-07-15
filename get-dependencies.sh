#!/bin/bash
set -x
set -v
set -e

PKGS="saw-core cryptol-verifier jvm-verifier llvm-verifier"
PUBLIC_GITHUB_REPOS="cryptol aig abcBridge jvm-parser llvm-pretty llvm-pretty-bc-parser saw-core cryptol-verifier jvm-verifier llvm-verifier"
PRIVATE_GITHUB_REPOS=""
PROGRAMS="alex happy c2hs"
TESTABLE="saw-core jvm-verifier llvm-verifier"

dotests="false"
dopull="false"
sandbox_dir=build

while getopts "tpfj:" opt; do
    case $opt in
        t)
            dotests="true"
            ;;
        f)
            force_utils="true"
            ;;
        p)
            dopull="true"
            ;;
        j)
            jobs="-j$OPTARG"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done

if [ ! -e ./deps ] ; then
  mkdir deps
fi

if [ "${OS}" == "Windows_NT" ] ; then
    HERE=$(cygpath -w $(pwd))

    # Force abcBridge to be built without pthreads
    EXTRA_CONSTRAINTS=--constraint=abcBridge\ -enable-pthreads
else
    HERE=$(pwd)

    # NB the flag '-v1' sets the cabal verbosity to 1, which is its
    # default value. This should be a no-op, and is only added here
    # because it is the easiest way I could think of to deal with the
    # stupid issues that arise with string interpolation.  In
    # particular, if this string is empty, later cabal invocations
    # look like:
    #      cabal install '' --force-reinstalls
    # and the empty string is interpreted as a file name, which fails :-(
    EXTRA_CONSTRAINTS=-v1
fi

PATH=${HERE}/${sandbox_dir}/bin:$PATH
CABAL="cabal"

# Pin a repo *if* a corresponding pin is defined in
# './build-sandbox-version-pins.txt'. Assumes the CWD is in the
# argument repo.
#
# The format of the pins file entries is '<repo> <committish>'. Lines
# starting with '#' are treated as comments (because they aren't valid
# repo names).
pin () {
  repo="$1"
  echo Searching for pins for $repo ...
  if [ -e "$HERE"/build-sandbox-version-pins.txt ] && \
     grep "^$repo .\+\$" "$HERE"/build-sandbox-version-pins.txt &>/dev/null; then
    echo Found pins\!
    committish=$(sed -ne "s/^$repo \(.*\)\$/\1/p" < \
      "$HERE"/build-sandbox-version-pins.txt)
    echo Namely: $committish
    git reset --hard "$committish"
  fi
}

for repo in ${PUBLIC_GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone https://github.com/GaloisInc/${repo}.git ./deps/${repo}
  fi
  if [ "${dopull}" == "true" ] ; then
    (cd ./deps/${repo} && git checkout master && git pull && pin "$repo")
  fi
done

for repo in ${PRIVATE_GITHUB_REPOS} ; do
  if [ ! -e ./deps/${repo} ] ; then
    git clone git@github.com:GaloisInc/${repo}.git ./deps/${repo}
  fi
  if [ "${dopull}" == "true" ] ; then
    (cd ./deps/${repo} && git checkout master && git pull && pin "$repo")
  fi
done

for pkg in ${PKGS} ; do
  (cd deps/$pkg && ${CABAL} sandbox --sandbox="${HERE}/${sandbox_dir}" init)
done
${CABAL} sandbox --sandbox="${HERE}/${sandbox_dir}" init

if [ "${dotests}" == "true" ] ; then
  for pkg in saw-script llvm-verifier jvm-verifier cryptol-verifier saw-core ; do
    ${CABAL} sandbox hc-pkg unregister $pkg || true
  done
fi

# use cabal to install the build-time depencencies we need
# always build them if the '-f' option was given
for prog in ${PROGRAMS} ; do
  if [ "${force_utils}" == "true" ]; then
    ${CABAL} install "${EXTRA_CONSTRAINTS}" $jobs $prog
  else
    (which $prog && $prog --version) || ${CABAL} install "${EXTRA_CONSTRAINTS}" $jobs $prog
  fi
done

for repo in ${PUBLIC_GITHUB_REPOS} ${PRIVATE_GITHUB_REPOS} ${GALOIS_REPOS}; do
  ${CABAL} sandbox add-source deps/${repo}

  # We should be able to skip this step by using EXTRA_CONSTRAINTS now instead
  # Be sure abcBridge builds with pthreads diabled on Windows
  #if [ "${OS}" == "Windows_NT" -a "${repo}" == "abcBridge" ]; then
  #  ${CABAL} install $jobs --force abcBridge -f-enable-pthreads
  #fi
done

if [ "${dotests}" == "true" ] ; then
  if [ -z ${TEST_TIMEOUT} ]; then
    TEST_TIMEOUT="60s"
  fi

  for pkg in ${TESTABLE}; do
    test_flags="--test-option=--xml=${HERE}/${pkg}-test-results.xml --test-option=--timeout=${TEST_TIMEOUT}"

    if [ ! "${QC_TESTS}" == "" ]; then
        test_flags="${test_flags} --test-option=--quickcheck-tests=${QC_TESTS}"
    fi

    (cd deps/${pkg} &&
         ${CABAL} sandbox init --sandbox="${HERE}/${sandbox_dir}" &&
         ${CABAL} install "${EXTRA_CONSTRAINTS}" $jobs --enable-tests --only-dependencies &&
         ${CABAL} configure "${EXTRA_CONSTRAINTS}" --enable-tests &&
         ${CABAL} build &&
         (${CABAL} test ${test_flags} || true))

    if [ -e ${pkg}-test-results.xml ]; then
      xsltproc jenkins-junit-munge.xsl ${pkg}-test-results.xml > jenkins-${pkg}-test-results.xml
    else
      echo "Missing test results: ${pkg}-test-results.xml"
      exit 1
    fi
  done

else

  ${CABAL} install "${EXTRA_CONSTRAINTS}" --reinstall --force-reinstalls

fi
