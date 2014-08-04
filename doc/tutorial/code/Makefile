SAW?=../../bin/saw
SAWS=$(wildcard *.saw)
OUTS=$(SAWS:.saw=.out)
JAVA_CLASSES=`(java -verbose 2>&1) | grep Opened | head -1 | cut -d ' ' -f 2 | cut -d ']' -f 1`

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
