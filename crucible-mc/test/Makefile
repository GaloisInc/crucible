CLANG=clang
CFLAGS=-O1

.PHONY: all clean

all: example.bc

clean:
	-rm *.bc *.ll

%.bc: %.c
	$(CLANG) $(CFLAGS) -emit-llvm -o $@ -c $<
