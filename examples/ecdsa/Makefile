SAW?=saw
JDK?=$(shell (java -verbose 2>&1) | grep Opened | head -1 | cut -d ' ' -f 2 | cut -d ']' -f 1)

build :
	mkdir -p build
	javac -g -cp src src/com/galois/ecc/*.java -d build
	javac -g -cp build:tests tests/com/galois/ecc/*.java -d build

# Build java doc documentation.
doc :
	javadoc -classpath src -d doc -public src/com/galois/ecc/*

clean :
	rm -rf doc build

# Run Java with 32bit data.
run32 :
	java -cp build -d32 com.galois.ecc.ECC

# Run Java with 64bit data (much faster).
run64 :
	java -cp build -d64 com.galois.ecc.ECC

verify :
	${SAW} -j "${JDK}" -c build ecdsa.saw

.PHONY : build clean doc run32 run64 verify
