CLANG=clang-4.0
INCLUDES=../includes

CFLGASG=-I $(INCLUDES) -c -Wall -emit-llvm

.PHONY: run all clean

run: example1.bc
	saw crucible-c.saw

all: example1.bc

%.bc: %.c
	$(CLANG) $(CFLGASG) $^ -o $@

%.ll: %.c
	$(CLANG) $(CFLGASG) -S $^ -o $@

clean:
	-rm *.bc *.ll

