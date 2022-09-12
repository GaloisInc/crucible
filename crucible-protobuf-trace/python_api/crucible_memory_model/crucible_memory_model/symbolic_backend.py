import z3
from os.path import join, abspath, dirname
from what4_deserialize import Z3Backend, deserialize_what4_from_file

class SymbolicBackend:
    def __init__(self, expressions_dir, path_ids_dir):
        self.expressions_by_id = {}
        self.expressions_dir = expressions_dir
        self.path_ids_dir = path_ids_dir

    def const_bool(self, value):
        raise NotImplementedError

    def const_int(self, value):
        raise NotImplementedError

    def const_bv(self, value, width):
        raise NotImplementedError

    def bv_size(self, value):
        raise NotImplementedError

    def const_float(self, value):
        raise NotImplementedError

    def conjunction(self, *exprs):
        raise NotImplementedError

    def ite(self, cond, true_expr, false_expr):
        raise NotImplementedError

    def deserialize_what4_expr(self, what4_path):
        raise NotImplementedError

    def load_serialized_what4_expression(self, serialized_id):
        if serialized_id not in self.expressions_by_id:
            path = join(self.expressions_dir, f'expr_{serialized_id}')
            self.expressions_by_id[serialized_id] = self.deserialize_what4_expr(path)
        return self.expressions_by_id[serialized_id]

    @property
    def solver(self):
        raise NotImplementedError


class SymbolicBackendZ3(SymbolicBackend):
    def __init__(self, expressions_dir, path_ids_dir):
        super().__init__(expressions_dir, path_ids_dir)
        self._solver = z3.Solver()

    def const_bool(self, value):
        return z3.BoolVal(value)

    def const_int(self, value):
        return z3.IntVal(value)

    def const_bv(self, value, width):
        return z3.BitVecVal(value, width)

    def bv_size(self, value):
        assert isinstance(value, z3.BitVecRef)
        return value.size()

    def const_float(self, value):
        return z3.RealVal(value)

    def as_constant_int(self, value: z3.ArithRef):
        assert isinstance(value, z3.ArithRef) and value.sort().is_int()
        return value.as_long()

    def conjunction(self, *exprs):
        return z3.And(*exprs)

    def negate(self, expr):
        return z3.Not(expr)

    def ite(self, cond, true_expr, false_expr):
        return z3.If(cond, true_expr, false_expr)

    def deserialize_what4_expr(self, what4_path):
        bak = Z3Backend()
        return deserialize_what4_from_file(what4_path, bak)

    @property
    def solver(self):
        return self._solver