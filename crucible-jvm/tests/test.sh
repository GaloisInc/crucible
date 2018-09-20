TESTCASE=Str

RTJAR=/Library/Java/JavaVirtualMachines/jdk1.8.0_171.jdk/Contents/Home/jre/lib/rt.jar


make $TESTCASE.class
javap -c $TESTCASE
cabal new-exec crucible-jvm -- -d 3 -j $RTJAR $TESTCASE.java
