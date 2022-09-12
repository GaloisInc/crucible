# Generated from ./sexpression.g4 by ANTLR 4.10.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,8,37,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,1,0,5,0,13,
        8,0,10,0,12,0,16,9,0,1,0,1,0,1,1,1,1,1,2,1,2,3,2,24,8,2,1,3,1,3,
        5,3,28,8,3,10,3,12,3,31,9,3,1,3,1,3,1,4,1,4,1,4,0,0,5,0,2,4,6,8,
        0,1,1,0,2,5,34,0,10,1,0,0,0,2,19,1,0,0,0,4,23,1,0,0,0,6,25,1,0,0,
        0,8,34,1,0,0,0,10,14,3,2,1,0,11,13,3,4,2,0,12,11,1,0,0,0,13,16,1,
        0,0,0,14,12,1,0,0,0,14,15,1,0,0,0,15,17,1,0,0,0,16,14,1,0,0,0,17,
        18,5,0,0,1,18,1,1,0,0,0,19,20,5,8,0,0,20,3,1,0,0,0,21,24,3,8,4,0,
        22,24,3,6,3,0,23,21,1,0,0,0,23,22,1,0,0,0,24,5,1,0,0,0,25,29,5,6,
        0,0,26,28,3,4,2,0,27,26,1,0,0,0,28,31,1,0,0,0,29,27,1,0,0,0,29,30,
        1,0,0,0,30,32,1,0,0,0,31,29,1,0,0,0,32,33,5,7,0,0,33,7,1,0,0,0,34,
        35,7,0,0,0,35,9,1,0,0,0,3,14,23,29
    ]

class sexpressionParser ( Parser ):

    grammarFileName = "sexpression.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                     "<INVALID>", "<INVALID>", "'('", "')'" ]

    symbolicNames = [ "<INVALID>", "WHITESPACE", "NUMBER", "OPERATOR", "BITVECTOR_CONST", 
                      "SYMBOL", "LPAREN", "RPAREN", "COMMENT" ]

    RULE_sexpr = 0
    RULE_comment = 1
    RULE_item = 2
    RULE_list_ = 3
    RULE_atom = 4

    ruleNames =  [ "sexpr", "comment", "item", "list_", "atom" ]

    EOF = Token.EOF
    WHITESPACE=1
    NUMBER=2
    OPERATOR=3
    BITVECTOR_CONST=4
    SYMBOL=5
    LPAREN=6
    RPAREN=7
    COMMENT=8

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.10.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class SexprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def comment(self):
            return self.getTypedRuleContext(sexpressionParser.CommentContext,0)


        def EOF(self):
            return self.getToken(sexpressionParser.EOF, 0)

        def item(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(sexpressionParser.ItemContext)
            else:
                return self.getTypedRuleContext(sexpressionParser.ItemContext,i)


        def getRuleIndex(self):
            return sexpressionParser.RULE_sexpr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSexpr" ):
                listener.enterSexpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSexpr" ):
                listener.exitSexpr(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitSexpr" ):
                return visitor.visitSexpr(self)
            else:
                return visitor.visitChildren(self)




    def sexpr(self):

        localctx = sexpressionParser.SexprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_sexpr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 10
            self.comment()
            self.state = 14
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << sexpressionParser.NUMBER) | (1 << sexpressionParser.OPERATOR) | (1 << sexpressionParser.BITVECTOR_CONST) | (1 << sexpressionParser.SYMBOL) | (1 << sexpressionParser.LPAREN))) != 0):
                self.state = 11
                self.item()
                self.state = 16
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 17
            self.match(sexpressionParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class CommentContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def COMMENT(self):
            return self.getToken(sexpressionParser.COMMENT, 0)

        def getRuleIndex(self):
            return sexpressionParser.RULE_comment

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterComment" ):
                listener.enterComment(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitComment" ):
                listener.exitComment(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitComment" ):
                return visitor.visitComment(self)
            else:
                return visitor.visitChildren(self)




    def comment(self):

        localctx = sexpressionParser.CommentContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_comment)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 19
            self.match(sexpressionParser.COMMENT)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ItemContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def atom(self):
            return self.getTypedRuleContext(sexpressionParser.AtomContext,0)


        def list_(self):
            return self.getTypedRuleContext(sexpressionParser.List_Context,0)


        def getRuleIndex(self):
            return sexpressionParser.RULE_item

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterItem" ):
                listener.enterItem(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitItem" ):
                listener.exitItem(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitItem" ):
                return visitor.visitItem(self)
            else:
                return visitor.visitChildren(self)




    def item(self):

        localctx = sexpressionParser.ItemContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_item)
        try:
            self.state = 23
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [sexpressionParser.NUMBER, sexpressionParser.OPERATOR, sexpressionParser.BITVECTOR_CONST, sexpressionParser.SYMBOL]:
                self.enterOuterAlt(localctx, 1)
                self.state = 21
                self.atom()
                pass
            elif token in [sexpressionParser.LPAREN]:
                self.enterOuterAlt(localctx, 2)
                self.state = 22
                self.list_()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class List_Context(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def LPAREN(self):
            return self.getToken(sexpressionParser.LPAREN, 0)

        def RPAREN(self):
            return self.getToken(sexpressionParser.RPAREN, 0)

        def item(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(sexpressionParser.ItemContext)
            else:
                return self.getTypedRuleContext(sexpressionParser.ItemContext,i)


        def getRuleIndex(self):
            return sexpressionParser.RULE_list_

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterList_" ):
                listener.enterList_(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitList_" ):
                listener.exitList_(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitList_" ):
                return visitor.visitList_(self)
            else:
                return visitor.visitChildren(self)




    def list_(self):

        localctx = sexpressionParser.List_Context(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_list_)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 25
            self.match(sexpressionParser.LPAREN)
            self.state = 29
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while (((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << sexpressionParser.NUMBER) | (1 << sexpressionParser.OPERATOR) | (1 << sexpressionParser.BITVECTOR_CONST) | (1 << sexpressionParser.SYMBOL) | (1 << sexpressionParser.LPAREN))) != 0):
                self.state = 26
                self.item()
                self.state = 31
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 32
            self.match(sexpressionParser.RPAREN)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class AtomContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def OPERATOR(self):
            return self.getToken(sexpressionParser.OPERATOR, 0)

        def SYMBOL(self):
            return self.getToken(sexpressionParser.SYMBOL, 0)

        def NUMBER(self):
            return self.getToken(sexpressionParser.NUMBER, 0)

        def BITVECTOR_CONST(self):
            return self.getToken(sexpressionParser.BITVECTOR_CONST, 0)

        def getRuleIndex(self):
            return sexpressionParser.RULE_atom

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAtom" ):
                listener.enterAtom(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAtom" ):
                listener.exitAtom(self)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAtom" ):
                return visitor.visitAtom(self)
            else:
                return visitor.visitChildren(self)




    def atom(self):

        localctx = sexpressionParser.AtomContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_atom)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 34
            _la = self._input.LA(1)
            if not((((_la) & ~0x3f) == 0 and ((1 << _la) & ((1 << sexpressionParser.NUMBER) | (1 << sexpressionParser.OPERATOR) | (1 << sexpressionParser.BITVECTOR_CONST) | (1 << sexpressionParser.SYMBOL))) != 0)):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





