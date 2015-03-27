TOP=../../..
LSS?=$(TOP)/SAWScript/build/bin/lss
SAW?=$(TOP)/SAWScript/build/bin/saw

.PHONY: aigs

all: aigs

aigs: aes.bc
	$(LSS) --backend=saw $<
	$(SAW) example.saw

clean:
	rm -f *.aig
