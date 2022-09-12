from .antlr.sexpressionLexer import sexpressionLexer
from .antlr.sexpressionParser import sexpressionParser
from .antlr.sexpressionListener import sexpressionListener
from .antlr.sexpressionVisitor import sexpressionVisitor
from .visitors.what4_deserialize_backends import Z3Backend, Backend
from .visitors.what4_lists_deserializer import What4ListsDeserializer
from .visitors.what4_to_lists_visitor import What4ToListsVisitor

from antlr4 import FileStream, InputStream, CommonTokenStream
from antlr4.error.ErrorListener import ErrorListener


def deserialize_what4_input(input_stream, backend):
    lexer = sexpressionLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = sexpressionParser(stream)
    tree = parser.sexpr()

    metadata, exprs = What4ToListsVisitor().visit(tree)
    deserialized_expr = What4ListsDeserializer(
        backend=backend
    ).parse_full_what4_expr(metadata, exprs)
    return deserialized_expr()

def deserialize_what4_from_file(path, backend):
    input = FileStream(path)
    return deserialize_what4_input(input, backend)

def deserialize_what4_from_string(data: str, backend):
    input = InputStream(data)
    return deserialize_what4_input(input, backend)
