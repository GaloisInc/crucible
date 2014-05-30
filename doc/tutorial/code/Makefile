SAW?=../../bin/saw
SAWS=$(wildcard *.saw)
OUTS=$(SAWS:.saw=.out)

all: FFS.class ffs.bc double.bc

run: all ${OUTS}

%.bc: %.c
	clang -emit-llvm -c $< -o $@

%.class: %.java
	javac -g $<

%.out: %.saw
	${SAW} $< 2>&1 | tee $@

clean:
	rm -f *.bc *.class *.smt *.aig *.out
