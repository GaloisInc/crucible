from collections import namedtuple
from .solver_backend import SolverBackend
import z3
from abc import ABC, abstractmethod
from typing import List, Literal, Union
from .crucible_event_listener import LoadedLLVMPointer, Load, LoadedPartialLLVMVal, LoadedStorageType, LoadedWriteSourceMemset
AllocationType = Union[Literal['STACK'], Literal['HEAP'], Literal['GLOBAL']]

class MemoryModelReadInterface(ABC):
    @abstractmethod
    def read(self,
             solver: SolverBackend,
             addr: LoadedLLVMPointer,
             value_type,
             byte_alignment: int,
             read_value):
        raise NotImplementedError

class MemoryModelFullInterface(MemoryModelReadInterface):
    @abstractmethod
    def store(self, solver: SolverBackend, dst_ptr, write_source, condition, is_const_write):
        raise NotImplementedError

    @abstractmethod
    def alloc(self, solver: SolverBackend, blkId: int, location: str, alloc_type: AllocationType, byte_alignment, size=None):
        raise NotImplementedError

class MergedMemoryModelBase(MemoryModelReadInterface):
    def __init__(self, cond, mem_if_true, mem_if_false):
        self.cond = cond
        self.mem_if_true = mem_if_true
        self.mem_if_false = mem_if_false

    def read(
        self,
        solver: SolverBackend,
        addr: LoadedLLVMPointer,
        value_type,
        byte_alignment: int,
        read_value
        ):
        assert solver.satisfiable()
        can_be_true = solver.satisfiable(self.cond)
        can_be_false = solver.satisfiable(z3.Not(self.cond))
        if can_be_true:
            val_read_true = self.mem_if_true.read(solver, addr, value_type, byte_alignment, read_value)
        if can_be_false:
            val_read_false = self.mem_if_false.read(solver, addr, value_type, byte_alignment, read_value)

        if can_be_true and can_be_false:
            return z3.If(self.cond, val_read_true, val_read_false)
        elif can_be_true:
            return val_read_true
        elif can_be_false:
            return val_read_false
        else:
            assert not solver.check()
            assert False, "what the hellllll?"



class EmptyMemoryModelBase:
    def __init__(self):
        pass

    def read(
        self,
        solver: SolverBackend,
        addr: LoadedLLVMPointer,
        value_type,
        byte_alignment: int,
        read_value
        ):
        solver.add(z3.BoolVal(False))
        return None


MemWrite = namedtuple('MemWrite', ['dst_ptr', 'write_source', 'condition', 'is_const_write'])
MemAlloc = namedtuple('MemAlloc', ['blkId', 'location', 'alloc_type', 'byte_alignment', 'size', 'array_expr'])
MemFree = namedtuple('MemFree', ['blkIdFreed'])

class MemLogFrame(MemoryModelFullInterface):
    def __init__(self, parent):
        self.base = parent
        self.writes: List[MemWrite] = []
        self.allocations: List[MemAlloc] = []
        self.frees: List[MemFree] = []
        self.proof_goals = []

    def store(self, solver, dst_ptr, write_source, condition, is_const_write):
        self.writes.append(MemWrite(dst_ptr, write_source, condition, is_const_write))

    def alloc(self, solver: SolverBackend, blkId: int, location: str,
              alloc_type: AllocationType, byte_alignment, size=None):
        expr = z3.Array('mem_{}'.format(blkId), z3.BitVecSort(64), z3.BitVecSort(8))
        self.allocations.append(MemAlloc(blkId, location, alloc_type, byte_alignment, size, expr))

    def free(self, solver: SolverBackend, ptr_freed: LoadedLLVMPointer):
        self.proof_goals.append(ptr_freed.offset == 0)
        solver.add(ptr_freed.offset == 0)
        assert solver.check() == z3.sat

        self.frees.append(ptr_freed.alloc_id)

    def read(
        self,
        solver: SolverBackend,
        addr: LoadedLLVMPointer,
        value_type: LoadedStorageType,
        byte_alignment: int,
        read_value: LoadedPartialLLVMVal
        ):

        read_size = value_type.size_in_bytes

        data_read = [None for _ in range(read_size)]

        parent_value, parent_is_freed, parent_is_allocated = self.base.read(solver, addr, value_type, byte_alignment, read_value)

        cur_pointer_is_freed = z3.Or(*[
            freed_alloc_id == addr.alloc_id
            for freed_alloc_id in self.frees
        ])
        cur_pointer_is_allocated = z3.Or(*[
            alloc.blkId == addr.alloc_id
            for alloc in self.allocations
        ])

        # pointer must not have been freed
        solver.add_proof_goal(z3.Not(cur_pointer_is_freed))
        # pointer must have been allocated
        solver.add_proof_goal(cur_pointer_is_allocated)

        value = parent_value
        for write in self.writes:
            if not solver.satisfiable(write.dst_ptr.alloc_id == addr.alloc_id):
                continue # can't be the write serving our data
            src = write.write_source
            if isinstance(src, LoadedWriteSourceMemset):
                byte_val = src.fill_byte_val
                memset_size = src.size








        return value, parent_is_freed, parent_is_allocated