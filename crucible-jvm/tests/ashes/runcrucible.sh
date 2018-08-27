#!/bin/bash

RTJAR=/Library/Java/JavaVirtualMachines/jdk1.8.0_171.jdk/Contents/Home/jre/lib/rt.jar

cabal new-exec crucible-jvm -- -j $RTJAR $@
