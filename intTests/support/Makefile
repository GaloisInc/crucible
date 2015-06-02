SYM_API=../../deps/llvm-verifier/sym-api
CP=.

%.bc: %.c
	clang -emit-llvm -I$(SYM_API) -c $< -o $(shell basename $< .c).bc

%.out: %.c
	clang -I$(SYM_API) $(SYM_API)/sym-api.c $< -o $(shell basename $< .c).out

%.class: %.java
	javac -cp $(CP):../jars/galois.jar $<
