CLANG=clang-4.0
INCLUDES=../includes

CFLAGS=-I $(INCLUDES) -c -Wall -emit-llvm

.PHONY: run all clean counter-example

counter-example: byte_add.bc
	$(CLANG) -g -I $(INCLUDES) \
          ../c-src/sv-comp.c ../counter-example.c byte_add.bc

run: example1.bc
	saw crucible-c.saw

all: example1.bc

%.bc: %.c
	$(CLANG) $(CFLAGS) $^ -o $@

%.ll: %.c
	$(CLANG) $(CFLAGS) -S $^ -o $@

clean:
	-rm *.bc *.ll

