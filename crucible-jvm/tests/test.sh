TESTCASE=Str

make $TESTCASE.class
javap -c $TESTCASE
cabal new-exec crucible-jvm -- -d 3 $TESTCASE.java
