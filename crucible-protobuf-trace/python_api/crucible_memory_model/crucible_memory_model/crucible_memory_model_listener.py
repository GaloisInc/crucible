
import z3

from .crucible_event_listener import CrucibleEventListener
from .printing_listener import PrintingListener
from .symbolic_backend import SymbolicBackend, SymbolicBackendZ3

from crucible_protobuf_trace.operation_trace_pb2 import TraceEvent
from crucible_protobuf_trace.memory_events_pb2 import MemoryEventAlloc, MemoryEventFree, MemoryEventRead, MemoryEventWrite
from crucible_protobuf_trace.memory_state_pb2 import AllocationType


class CrucibleMemoryModelTail:
    def __init__(self) -> None:
        self.proof_goals = []

class CrucibleMemoryModel(PrintingListener):
    def __init__(self, backend, parent=None, solver=None):
        # for now, we only support Z3
        super().__init__(backend)
        self.current_path_id = None

        self.parent = parent

        self.constraints = []
        self.memory_model = LLVMMemory()

        self.proof_goals = []
        self.solver: z3.Solver = solver or z3.Solver()


    def push(self):
        self.solver.push()
        return CrucibleMemoryModel(self.backend, parent=self, solver=self.solver)

    def pop(self):
        self.solver.pop()
        head = self
        tail = self.parent
        head.parent = None
        tail.proof_goals += self.proof_goals
        return head, tail

    def handle_crucible_event(self, i: int, event: TraceEvent):
        if self.current_path_id is None:
            self.current_path_id = event.path_id
        assert event.path_id == self.current_path_id

        res = super().handle_crucible_event(i, event)
        return self if res is None else res

    def on_memory_event(self, memory_event_data, path_id=(), location=()):
        # import ipdb; ipdb.set_trace()
        loaded_loc = self.load_MaybeProgramLoc(location)
        print(f"{path_id.text}: {loaded_loc}: Memory event")
        kind = memory_event_data.WhichOneof("event")
        data = getattr(memory_event_data, kind)

        # if kind == 'write':
        #     dst = self.load_LLVMPointer(data.dst)
        #     src = self.load_WriteSource(data.src)
        #     print(f"Write to {dst}: {src}")
        # elif kind == 'read':
        #     # import ipdb; ipdb.set_trace()
        #     addr = self.load_LLVMPointer(data.addr)
        #     value_type = self.load_StorageType(data.value_type)
        #     byte_alignment = data.byte_alignment
        #     print(f"Read: {value_type=} from {addr=} with {byte_alignment=}")
        if kind == 'alloc':
            data: MemoryEventAlloc
            size = self.load_BVExpression(data.size) if data.HasField('size') else None
            desc = data.location_description
            alloc_type = AllocationType.Name(data.allocation_type)
            alignment = data.byte_alignment
            blkid = data.allocation_id_concrete

            self.allocations[blkid] = (blkid, alloc_type, alignment, desc, size)
            print("Alloc: ", self.allocations[blkid])
        elif kind ==
        elif kind == 'free':
            assert False, f"TODO: implement free {data=}"
        #     import ipdb; ipdb.set_trace()
        #     data: MemoryEventFree
        #     ptr_free = self.load_LLVMPointer(data.ptr)
        #     self.backend.as_constant_int(ptr_free)
        #     self.constraints.append(ptr_free.offset == 0)
            # blkid = data.allocation_id_concrete
            # print("Free: ", self.allocations[blkid])

        else:
            return super().on_memory_event(memory_event_data, path_id=path_id, location=location)

    def on_path_split(self, data, **kwargs):
        # import ipdb; ipdb.set_trace()
        self = self.push()
        self.current_path_id = data.continuing_path_id

        self.constraints.append(
            self.load_ExpressionID(data.split_condition)
        )
        return self

    def on_branch_switch(self, data, path_id=(), **kwargs):
        id_susp = data.id_suspended
        assert id_susp == self.current_path_id
        id_resumed = data.id_resumed
        condition_switched = self.load_ExpressionID(data.branch_condition)
        branch_location = self.load_MaybeProgramLoc(data.branch_location)
        suspended_assumptions = self.load_Assumptions(data.suspended_assumptions)

        head, tail = self.pop()

        # TODO: check suspended assumptions vs. popped assumptions
        new = tail.push()
        new.constraints.append(self.backend.negate(condition_switched))
        # z3 specific
        assert head.constraints[0].get_id() == condition_switched.get_id()
        new.current_path_id = id_resumed
        return new


    def on_path_merge(self, data, path_id=(), **kwargs):
        # import ipdb; ipdb.set_trace()
        assert data.merging_path_id == path_id
        assert data.merging_path_id == self.current_path_id
        popped_path_assumptions = self.load_Assumptions(data.path_assumptions)
        merging_assumptions = self.load_Assumptions(data.other_assumptions)
        condition = self.load_ExpressionID(data.merge_condition)
        merged_assumptions = self.backend.ite(condition, popped_path_assumptions, merging_assumptions)

        popped, parent_state = self.pop()
        assert popped.constraints[0].get_id() == condition.get_id()
        parent_state.constraints.append(merged_assumptions)
        parent_state.current_path_id = data.path_id_after
        return parent_state

    # def on_branch_abort(self, data, path_id=(), **kwargs):



class CrucibleMemoryModelListener(CrucibleEventListener):
    def __init__(self, backend: SymbolicBackend):
        super().__init__(backend)
        self.memory = CrucibleMemoryModel(backend, parent=CrucibleMemoryModelTail())

    def handle_crucible_event(self, i: int, event: TraceEvent):
        self.memory = self.memory.handle_crucible_event(i, event)

    def handle_unknown_event(self, event):
        self.memory = self.memory.handle_unknown_event(event)
