import z3
from . import Backend

Z3_BINOP_MAPPING = {
    '=': lambda a, b: a == b,
    'ite': z3.If,
    'notp': z3.Not,
    'andp': z3.And,
    'orp': z3.Or,
    'bvor': z3.BitVecRef.__or__,
    'bvand': z3.BitVecRef.__and__,
    'bvadd': z3.BitVecRef.__add__,
    'bvsub': z3.BitVecRef.__sub__,
    'bvmul': z3.BitVecRef.__mul__,
    'bvshl': z3.BitVecRef.__lshift__,
    'bvlshr': z3.BitVecRef.__rshift__,
    'bvslt': z3.BitVecRef.__lt__,
    'bvsle': z3.BitVecRef.__le__,
    'bvsgt': z3.BitVecRef.__gt__,
    'bvsge': z3.BitVecRef.__ge__,
    'bvule': z3.ULT,
    'bvuge': z3.UGE,
    'bvult': z3.ULE,
    'bvugt': z3.UGT,
    'bvsdiv': z3.BitVecRef.__div__,
    'bvudiv': z3.UDiv,
    'bvsmod': z3.BitVecRef.__mod__,
    'bvurem': z3.URem,
    'bvsrem': z3.SRem,
    'zero_extend': z3.ZeroExt,
    'sign_extend': z3.SignExt,
    'extract': z3.Extract,
    'concat': z3.Concat,
}

class Z3Backend(Backend):
    def __init__(self):
        super().__init__('z3')

    def supports_op(self, name):
        return name in Z3_BINOP_MAPPING or hasattr(self, '_handle_op_' + name)

    def get_fresh_variable(self, name, type_id, *args):
        if type_id == 'bv':
            size, = args
            return z3.BitVec(name, size)
        else:
            assert False, "Unknown type: " + str(type_id)

    def make_bv_const(self, value, size):
        return z3.BitVecVal(value, size)

    def make_bool_const(self, value: bool):
        return z3.BoolVal(value)

    def make_int_const(self, value):
        return z3.IntVal(value)

    def _handle_op(self, op, *args):
        if op in Z3_BINOP_MAPPING:
            return Z3_BINOP_MAPPING[op](*args)

        try:
            return getattr(self, '_handle_op_' + op)(*args)
        except AttributeError:
            assert False, f"Unknown op: {op}(*{args})"