RTJAR=/Library/Java/JavaVirtualMachines/jdk1.8.0_171.jdk/Contents/Home/jre/lib/rt.jar

make Main.class
cabal new-exec crucible-jvm -- -d 4 -j $RTJAR Main
