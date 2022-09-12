import functools
import os
import sys
from tkinter.messagebox import NO
from typing import Any, List
from antlr4 import *
from ..antlr import sexpressionListener, sexpressionParser, sexpressionLexer, sexpressionVisitor
from abc import ABC
from .what4_deserialize_backends import Backend
import abc
import json
import z3

import sys

class What4ListsDeserializer:
    def __init__(self, backend):
        super().__init__()
        self.backend: Backend = backend

    @staticmethod
    def identity(x):
        return x

    def parse_let_binding(self, binding):
        name, value = binding
        value = self.parse_expr(value)
        self.backend.add_scope_var(name, value)

    def parse_full_what4_expr(self, metadata, exprs):
        assert not self.backend.free_variable_exprs

        for binding in metadata['free_vars']:
            self.backend.add_fresh_variable(binding['orig_name'], binding['type_repr'], binding['new_name'])

        assert not metadata['free_funcs']

        assert len(exprs) == 1
        expr, = exprs
        return self.parse_expr(expr)

    def parse_expr(self, expr):
        if type(expr) is str:
            if expr[:2] in {'#x', '#b'}:
                intval = int(expr[2:], 16 if expr[1] == 'x' else 2)
                size = len(expr[2:]) * (4 if expr[1] == 'x' else 1)
                return functools.partial(self.identity, self.backend.make_bv_const(intval, size))
            elif expr[0] in '0123456789':
                intval = int(expr)
                return functools.partial(self.identity, intval)
            else:
                return self.backend.resolve_name_scoped(expr)
        elif type(expr) is list:
            return self.parse_expr_list(expr)
        else:
            assert False, f"Unknown expr type {type(expr)}: {expr}"

    def parse_expr_list(self, expr: List[Any]):
        car, *cdr = expr

        if type(car) is not str:
            func = self.parse_expr(car)
            args = [self.parse_expr(v) for v in cdr]
            args = [arg() for arg in args] # eval args for the function
            return functools.partial(func, *args)

        if car == 'let':
            bindings, body = cdr
            self.backend.push_scope()
            for binding in bindings:
                self.parse_let_binding(binding)
            res = self.parse_expr(body)
            self.backend.pop_scope()
            return res

        elif car == '_':
            return self.parse_expr(cdr)

        elif self.backend.supports_op(car):
            args = [self.parse_expr(v) for v in cdr]
            args = [arg() for arg in args] # eval args for the function
            return functools.partial(self.backend._handle_op, car, *args)

        else:
            assert False, f"Unknown op {car}, don't know how to handle!"