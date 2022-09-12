import sys
import os
from os.path import dirname, join, abspath, exists, isdir, isfile
import networkx as nx
from collections import defaultdict
from symbolic_backend import SymbolicBackendZ3, SymbolicBackend
from what4_deserialize import Backend, Z3Backend, deserialize_what4_from_file
from crucible_protobuf_trace.operation_trace_pb2 import OperationTrace

from collections import namedtuple

from crucible_memory_model.crucible_event_listener import CrucibleEventListener
from crucible_memory_model.printing_listener import PrintingListener
from crucible_memory_model.graphing_listener import GraphingEventListener
from crucible_memory_model.crucible_memory_model_listener import CrucibleMemoryModelListener
def process_trace(trace_path: str, event_listener: CrucibleEventListener) -> OperationTrace:
    trace = OperationTrace()
    event_listener = event_listener

    with open(trace_path, 'rb') as f:
        trace.ParseFromString(f.read())

    for i, event in enumerate(trace.events):
        event_listener.handle_crucible_event(i, event)

if __name__ == '__main__':
    results_dir = dirname(sys.argv[1])
    expressions_dir = join(results_dir, 'expressions')
    path_ids_dir = join(results_dir, 'path_ids')

    listener = CrucibleMemoryModelListener(SymbolicBackendZ3(expressions_dir, path_ids_dir))

    process_trace(sys.argv[1], listener)

    for i in range(max(listener.memory.allocations.keys()) + 1):
        print(f"Allocation {i}: {listener.memory.allocations.get(i, 'MISSING')}")
    # print(f'{listener.memory.allocations.keys()}')
    # listener.dump_dot_file('graph.dot')



