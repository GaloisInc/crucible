include ../support/Makefile

srcs=$(wildcard *.java)

all: $(srcs:.java=.class) $(srcs:.java=.jvm-asm)

clean:
	-rm -f *.class *.jvm-asm
