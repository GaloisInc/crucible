SAW?=../../bin/saw
SAWS=$(wildcard *.saw)
OUTS=$(SAWS:.saw=.out)
JAVA_CLASSES=/System/Library/Java/JavaVirtualMachines/1.6.0.jdk/Contents/Classes/classes.jar

all: FFS.class ffs.bc double.bc Add.class

run: all ${OUTS}

%.bc: %.c
	clang -emit-llvm -c $< -o $@

%.class: %.java
	javac -g $<

%.out: %.saw
	${SAW} -j ${JAVA_CLASSES} $< 2>&1 | tee $@

clean:
	rm -f *.bc *.class *.smt *.aig *.out
