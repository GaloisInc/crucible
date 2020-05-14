CLANG=clang
CFLAGS=-O1 -Wall

.PHONY: all clean

all: diamond.bc example.bc loop-simple-deep-nested.bc

clean:
	-rm *.bc *.ll

%.bc: %.c
	$(CLANG) $(CFLAGS) -emit-llvm -o $@ -c $<
