SAW?=../../bin/saw

all: FFS.class ffs.bc double.bc

%.bc: %.c
	clang -emit-llvm -c $< -o $@

%.class: %.java
	javac -g $<

%.out: %.saw
	${SAW} $< 2>&1 | tee $@

clean:
	rm -f *.bc *.class *.smt *.aig *.out
