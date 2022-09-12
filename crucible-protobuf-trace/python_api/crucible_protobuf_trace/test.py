# coding: utf-8

import os
from antlr_sexprparse_py import deserialize_what4_from_file
from antlr_sexprparse_py.visitors.what4_deserialize_backends.deserialize_backend_z3 import Z3Backend
from operation_trace_pb2 import OperationTrace

class Trace:
    def __init__(self, proto_path, expressions_dir):
        super().__init__()
        self.proto_path : str = proto_path
        self.expressions_dir : str = expressions_dir
        self.expressions_cache = {}
        self.trace = OperationTrace()

        with open(proto_path, 'rb') as f:
            self.trace.ParseFromString(f.read())

    def __repr__(self) -> str:
        return super().__repr__()

    def __str__(self) -> str:
        return super().__str__()

    def expr_by_id_cached(self, id):
        if id not in self.expressions_cache:
            backend = Z3Backend()
            deserialized = deserialize_what4_from_file(os.path.join(self.expressions_dir, f'expr_{id}'), backend)
            self.expressions_cache[id] = deserialized
        return self.expressions_cache[id]


if __name__ == '__main__':
    res = Trace('../../../../results/test/trace.proto', '../../../../expressions')
    print(res)