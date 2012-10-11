.PHONY : all clean

all : MyParser.hs

MyLexer.hs : MyLexer.x MyToken.hs AST.hs
	alex -o MyLexer.hs MyLexer.x

MyParser.hs : MyParser.y MyLexer.hs
	happy -o MyParser.hs MyParser.y

clean :
	-rm *.o *.hi MyParser.hs MyLexer.hs