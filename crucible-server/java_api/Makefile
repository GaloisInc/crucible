ifndef JAVA_HOME
export JAVA_HOME=$(shell /usr/libexec/java_home)
endif

all :
	mvn install javadoc:javadoc

build :
	mvn install

doc :
	mvn javadoc:javadoc

clean :
	mvn clean

.PHONY : all clean build doc
