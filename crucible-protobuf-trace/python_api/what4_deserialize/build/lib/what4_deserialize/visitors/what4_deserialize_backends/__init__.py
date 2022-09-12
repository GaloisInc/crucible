import abc
import functools

class Backend(abc.ABC):
    def __init__(self, name):
        self.name = name
        self.old_to_new_name = {}
        self.free_variable_types = {}
        self.free_variable_exprs = {}
        self.val_scopes = []

    @staticmethod
    def parse_type_repr(s):
        if s.startswith("BaseBVRepr"):
            return 'bv', int(s.split()[1])
        else:
            assert False, "Unknown type repr: " + s

    @staticmethod
    def identity(x):
        return x

    def push_scope(self, scope=None):
        if scope is None:
            scope = {}
        self.val_scopes.append(scope)

    def pop_scope(self):
        return self.val_scopes.pop()

    def add_fresh_variable(self, old_name, type_repr, new_name):
        assert old_name not in self.old_to_new_name
        assert new_name not in self.free_variable_types
        assert new_name not in self.free_variable_exprs

        # import ipdb; ipdb.set_trace()
        typ = self.parse_type_repr(type_repr)

        self.old_to_new_name[old_name] = new_name
        self.free_variable_types[new_name] = typ
        self.free_variable_exprs[new_name] = self.get_fresh_variable(old_name, *typ)

    def add_scope_var(self, name, value):
        self.val_scopes[-1][name] = value

    def resolve_name_scoped(self, name):
        for scope in reversed(self.val_scopes):
            if name in scope:
                return scope[name]
        if name in self.free_variable_exprs:
            return functools.partial(self.identity, self.free_variable_exprs[name])
        # assert False, f"Could not retrieve expression {name}"
        return None


    # def from_expr_file(self, path):
    #     with open(path) as f:
    #         return self.parse_expr_file_content(f.read())

    # def parse_expr_file_content(self, content):
    #     self.push_scope()
    #     res = self.parse_expr_file_content_impl(content)
    #     self.pop_scope()
    #     return res

    # def parse_expr_file_content_impl(self, content):
    #     meta_comment, data = content.split('\n', 1)
    #     assert meta_comment.startswith(';; ')
    #     meta = meta_comment[3:]
    #     meta = json.loads(meta)
    #     for free_var in meta['free_vars']:
    #         self.add_fresh_variable(free_var['orig_name'], free_var['type_repr'], free_var['new_name'])

    #     res = parse(data, ParserConfig(prefix_symbols={}, dots_are_cons=False))
    #     assert len(res) == 1, f"Too many s-expressions in file: Found {len(res)}"
    #     # import ipdb; ipdb.set_trace()
    #     return self.parse_expr(res[0])

    # def parse_expr_scoped(self, scoped_bindings: Pair, body: Pair):
    #     new_bindings = {}

    #     # print("bindings: " + Renderer().render(scoped_bindings))
    #     # print("body: " + Renderer().render(body))
    #     self.push_scope()
    #     for var_binding in self.to_list(scoped_bindings):
    #         new_var_name = var_binding.car
    #         var_expr_pair = var_binding.cdr

    #         # print(f"var_binding: {new_var_name!r} = " + Renderer().render(var_expr_pair))
    #         result = self.parse_expr(var_expr_pair)
    #         self.add_scope_var(new_var_name, result)

    #     res = self.parse_expr(body)
    #     self.pop_scope()
    #     return res

    # @staticmethod
    # def to_iter(pair: Pair):
    #     cur = pair
    #     while cur != nil:
    #         yield cur.car
    #         cur = cur.cdr

    # @staticmethod
    # def to_list(pair: Pair):
    #     x = []
    #     while pair != nil:
    #         x.append(pair.car)
    #         pair = pair.cdr
    #     return x

    # @staticmethod
    # def identity(x):
    #     return x

    # def parse_expr(self, pair: Pair):
    #     if type(pair) is str:
    #         if pair[0] in '0123456789':
    #             return functools.partial(self.identity, int(pair))
    #         elif pair[:2] == '#x':
    #             return functools.partial(self.identity, self.make_bv_const(int(pair[2:], base=16), len(pair[2:]) * 4))
    #         elif pair[:2] == '#b':
    #             return functools.partial(self.identity, self.make_bv_const(int(pair[2:], base=2), len(pair[2:])))
    #         else:
    #             return self.resolve_name_scoped(pair)

    #     if type(pair.car) is str:
    #         if pair.car == 'let':
    #             bindings, body = self.to_list(pair.cdr)
    #             return self.parse_expr_scoped(bindings, body)
    #         elif pair.car == '_':
    #             return self.parse_expr(pair.cdr)
    #         else:
    #             args = [self.parse_expr(v) for v in self.to_list(pair.cdr)]
    #             # the backend should never ever deal with partial args anymore
    #             evaled_args = [arg() for arg in args]
    #             return functools.partial(self._handle_op, pair.car, *evaled_args)

    #     else:
    #         func = self.parse_expr(pair.car)
    #         args = [self.parse_expr(v)() for v in self.to_list(pair.cdr)]
    #         return functools.partial(func, *args)

    @abc.abstractmethod
    def supports_op(self, name):
        raise NotImplementedError

    @abc.abstractmethod
    def get_fresh_variable(self, name, type_id, *args):
        raise NotImplementedError

    @abc.abstractmethod
    def make_bv_const(self, value, size):
        raise NotImplementedError

    @abc.abstractmethod
    def _handle_op(self, op, *args):
        raise NotImplementedError

from .deserialize_backend_z3 import Z3Backend