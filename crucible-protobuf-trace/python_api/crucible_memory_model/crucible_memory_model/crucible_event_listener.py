from .symbolic_backend import SymbolicBackend
from collections import namedtuple

from crucible_protobuf_trace.operation_trace_pb2 import TraceEvent, BranchSwitch, PathSplit, PathID
from crucible_protobuf_trace.llvm_val_pb2 import LLVMPointer, LLVMVal, StorageType, StorageTypeF, LLVMValStructField, StorageTypeStructField, PartialLLVMVal
from crucible_protobuf_trace.memory_state_pb2 import WriteSource
from crucible_protobuf_trace.memory_events_pb2 import MemoryEventAlloc, MemoryEventFree, MemoryEventRead, MemoryEventWrite
from crucible_protobuf_trace.common_pb2 import MaybeProgramLoc, Position, ProgramLoc
from crucible_protobuf_trace.sym_expr_pb2 import ExpressionID, BVExpression, BoolExpression, IntExpression, FloatSize
from crucible_protobuf_trace.assumptions_pb2 import Assumption, Assumptions_Many, Assumptions_Merged, Assumptions

LoadedLLVMPointer = namedtuple('LLVMPointer', ['alloc_id', 'offset'])
LoadedBranchSwitch = namedtuple("BranchSwitch", ["id_from", "id_to", "condition", "location"])
LoadedBranchSplit = namedtuple("BranchSplit", ["id_from", "id_to", "condition"])
LoadedWriteSourceStore = namedtuple("WriteSourceStore", ["value", "type", "alignment"])
LoadedWriteSourceCopy = namedtuple("WriteSourceCopy", ["addr", "size", "require_disjoint"])
LoadedWriteSourceMemset = namedtuple("WriteSourceMemset", ["val", "size"])

LoadedStorageType = namedtuple('StorageType', 'size_in_bytes storage_type')
LoadedStorageTypeStructField = namedtuple('StorageTypeStructField', 'offset typ padding')
LoadedLLVMValStructField = namedtuple('LLVMValStructField', 'storage_type value')
LoadedPartialLLVMVal = namedtuple('PartialLLVMVal', 'predicate errored result_value')
class CrucibleEventListener:
    def __init__(self, backend: SymbolicBackend):
        self.backend = backend

    def load_Position(self, msg):
        assert isinstance(msg, Position)
        pos = msg
        kind = pos.WhichOneof('by')
        data = getattr(pos, kind)
        if kind == 'source':
            file = data.file if data.file else '<unknown>'
            return ('source', f'{file}:{data.line}:{data.column}')
        elif kind == 'binary':
            return ('binary', data.file, hex(data.address))
        elif kind == 'other':
            return ('other', data.descriptor)
        elif kind == 'internal':
            return ('internal',)
        else:
            assert False, f"unknown position kind: {pos}"

    def load_ProgramLoc(self, loc: ProgramLoc):
        assert isinstance(loc, ProgramLoc)
        return (loc.function_name, self.load_Position(loc.position))

    def load_MaybeProgramLoc(self, location: MaybeProgramLoc):
        assert isinstance(location, MaybeProgramLoc)

        if location.HasField('missing'):
            return None

        return self.load_ProgramLoc(location.program_loc)

    def load_ExpressionID(self, msg):
        assert isinstance(msg, ExpressionID)
        expr_kind = msg.WhichOneof('id_kind')
        if expr_kind == 'serialized_id':
            res = self.backend.load_serialized_what4_expression(msg.serialized_id)
            return res

        elif expr_kind == 'bool_const':
            return self.backend.const_bool(msg.bool_const.value)

        elif expr_kind == 'int_const':
            return self.backend.const_int(msg.int_const.value)

        elif expr_kind == 'bv_const':
            return self.backend.const_bv(int(msg.bv_const.hex_value, base=16), msg.bv_const.width)

        elif expr_kind == 'float_const':
            v = msg.float_const.value
            assert v.startswith('0x')
            return self.backend.const_float(float.fromhex(v))

    def load_IntExpression(self, msg):
        assert isinstance(msg, IntExpression)
        return self.load_ExpressionID(msg.id)

    def load_BVExpression(self, msg):
        assert isinstance(msg, BVExpression)
        return self.load_ExpressionID(msg.id)

    def load_BoolExpression(self, msg):
        assert isinstance(msg, BoolExpression)
        return self.load_ExpressionID(msg.id)

    def load_LLVMPointer(self, ptr) -> LoadedLLVMPointer:
        assert isinstance(ptr, LLVMPointer)
        alloc_id = self.load_IntExpression(ptr.allocation_id)
        offset = self.load_BVExpression(ptr.offset)

        return LoadedLLVMPointer(alloc_id, offset)

    def load_LLVMValStructField(self, msg) -> LoadedLLVMValStructField:
        assert isinstance(msg, LLVMValStructField)
        st = self.load_StorageTypeStructField(msg.field_type)
        val = self.load_LLVMVal(msg.field_value)
        return LoadedLLVMValStructField(st, val)

    def load_FloatSize(self, msg) -> str:
        assert isinstance(msg, int)
        return FloatSize.Name(msg)

    def load_LLVMVal(self, msg):
        assert isinstance(msg, LLVMVal)
        kind = msg.WhichOneof('value')
        data = getattr(msg, kind)
        res = ('LLVMVal',)
        if kind == 'int_value':
            alloc_id = self.load_IntExpression(data.allocation_id)
            offset = self.load_BVExpression(data.offset)
            res += ('int_value', alloc_id, offset)
        elif kind == 'array_value':
            st = self.load_StorageType(data.value_type)
            vals = [self.load_LLVMVal(v) for v in data.array_values]
            res += ('array_value', st, vals)
        elif kind == 'string_value':
            res += ('string_value', data.bytes)
        elif kind == 'struct_value':
            vals = [self.load_LLVMValStructField(v) for v in data.fields]
            res += ('struct_value', vals)
        elif kind == 'zero_value':
            st = self.load_StorageType(data.storage_type)
            res += ('zero_value', st)
        elif kind == 'float_value':
            # import ipdb; ipdb.set_trace()
            size_name = self.load_FloatSize(data.float_size)
            res += ('float_value', size_name, self.load_ExpressionID(data.value))
        else:
            print(kind, msg)
            import ipdb; ipdb.set_trace()
            raise NotImplementedError(kind)
        return res

    def load_StorageTypeF(self, msg):
        assert isinstance(msg, StorageTypeF)
        tp = msg.WhichOneof('type')
        data = getattr(msg, tp)
        res = 'StorageTypeF',
        if tp == 'bit_vector':
            res += 'BitVector', data.num_bytes * 8
        elif tp == 'array':
            elem_type = self.load_StorageType(data.element_type)
            num_elems = data.num_elements
            res += 'Array', elem_type, num_elems
        elif tp == 'struct_':
            fields = [self.load_StorageTypeStructField(v) for v in data.fields]
            res += 'Struct', fields
        elif tp == 'float_':
            sz_name = self.load_FloatSize(data.size)
            res += 'float', sz_name
        else:
            raise NotImplementedError(tp)
        return res

    def load_StorageTypeStructField(self, msg):
        assert isinstance(msg, StorageTypeStructField)
        st = self.load_StorageType(msg.val_type)
        return LoadedStorageTypeStructField(msg.offset, st, msg.num_bytes_padding)

    def load_StorageType(self, msg):
        assert isinstance(msg, StorageType)
        tp_repr = self.load_StorageTypeF(msg.storage_type)
        return LoadedStorageType(msg.size_in_bytes, tp_repr)

    def load_WriteSource(self, msg):
        assert isinstance(msg, WriteSource)
        kind = msg.WhichOneof('src')
        data = getattr(msg, kind)
        if kind == 'src_mem_copy':
            addr = self.load_LLVMPointer(data.addr)
            sz = self.load_BVExpression(data.size)
            return LoadedWriteSourceCopy(addr, sz, data.require_disjoint)
        elif kind == 'src_mem_set':
            val = self.load_BVExpression(data.val)
            sz = self.load_BVExpression(data.size)
            return LoadedWriteSourceMemset(val, sz)
        elif kind == 'src_mem_store':
            val = self.load_LLVMVal(data.value)
            tp = self.load_StorageType(data.storage_type)
            return LoadedWriteSourceStore(val, tp, data.byte_alignment)
        else:
            raise NotImplementedError


    def load_PathID(self, msg):
        assert isinstance(msg, PathID)
        return msg.text

    def load_BranchSwitch(self, msg):
        assert isinstance(msg, BranchSwitch)
        return LoadedBranchSwitch(
            self.load_PathID(msg.id_suspended),
            self.load_PathID(msg.id_resumed),
            self.load_ExpressionID(msg.branch_condition),
            self.load_MaybeProgramLoc(msg.branch_location)
        )

    def load_Assumption(self, msg: Assumption):
        assert isinstance(msg, Assumption)
        return self.load_ExpressionID(msg.assumed_expr)

    def load_Assumptions_Many(self, msg: Assumptions_Many):
        assert isinstance(msg, Assumptions_Many)
        return self.backend.conjunction(*[self.load_Assumptions(a) for a in msg.assumptions])

    def load_Assumptions_Merged(self, msg: Assumptions_Merged):
        assert isinstance(msg, Assumptions_Merged)
        cond = self.load_ExpressionID(msg.predicate)
        assumptions_true = self.load_Assumptions(msg.assumptions_then)
        assumptions_false = self.load_Assumptions(msg.assumptions_else)
        return self.backend.ite(cond, assumptions_true, assumptions_false)

    def load_Assumptions(self, msg: Assumptions):
        assert isinstance(msg, Assumptions)
        kind = msg.WhichOneof('kind')
        data = getattr(msg, kind)
        if kind == 'single_assumption':
            return self.load_Assumption(data)
        elif kind == 'merged_assumptions':
            return self.load_Assumptions_Merged(data)
        elif kind == 'many_assumptions':
            return self.load_Assumptions_Many(data)
        else:
            raise NotImplementedError(kind)

    def load_PartialLLVMVal(self, msg: PartialLLVMVal):
        pred = self.load_BoolExpression(msg.predicate)
        if msg.WhichOneof('value') == 'error':
            return LoadedPartialLLVMVal(pred, True, None)
        else:
            return LoadedPartialLLVMVal(
                pred, False,
                self.load_LLVMVal(msg.value.result)
            )

    def load_MemoryEventRead(self, msg: MemoryEventRead):
        assert isinstance(msg, MemoryEventRead)
        addr = self.load_LLVMPointer(msg.addr)
        value_type = self.load_StorageType(msg.value_type)
        alignment = msg.byte_alignment
        read_value = self.load_PartialLLVMVal(msg.read_value)
        return LoadedMemoryEventRead(
            addr,
            value_type,
            alignment,
            read_value,
        )

    def handle_crucible_event(self, i: int, event: TraceEvent):
        print("#" * 10 + f" {i:4d}: {event.path_id.text} " + "#" * 10)
        event_kind = event.WhichOneof("event_kind")
        if event_kind is None:
            return self.handle_unknown_event(event)
        handler = getattr(self, 'on_' + event_kind)
        event_data = getattr(event, event_kind)
        return handler(
            event_data,
            path_id=event.path_id,
            location=event.location
        )


    def handle_unknown_event(self, event):
        import ipdb; ipdb.set_trace()
        print(f"UNKNOWN UNKNOWN UNKNOWN EVENT!!!! {event}")
        raise NotImplementedError
