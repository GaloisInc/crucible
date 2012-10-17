.PHONY : all clean

all : Parser.hs

Lexer.hs : Lexer.x Token.hs AST.hs
	alex -o Lexer.hs Lexer.x

Parser.hs : Parser.y Lexer.hs
	happy -o Parser.hs Parser.y

clean :
	-rm *.o *.hi Parser.hs Lexer.hs