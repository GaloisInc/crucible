from .printing_listener import PrintingListener
from .symbolic_backend import SymbolicBackend
import networkx as nx
from crucible_protobuf_trace.operation_trace_pb2 import TraceEvent

class GraphingEventListener(PrintingListener):
    def __init__(self, backend: SymbolicBackend) -> None:
        super().__init__(backend)
        self.graph = nx.MultiDiGraph()
        self.last_loc = "Location:Start"
        self.last_seen_step = {self.last_loc: -1}

    def dump_dot_file(self, path):
        nx.drawing.nx_agraph.write_dot(self.graph, path)

    def handle_crucible_event(self, i: int, event: TraceEvent):
        if event.WhichOneof('event_kind') != 'memory_event':
            return super().handle_crucible_event(i, event)
        # id = event.path_id.text
        loc = self.load_MaybeProgramLoc(event.location)
        node_id_last = (self.last_loc)
        node_id_now = (loc)
        self.graph.add_node(node_id_now, label=f'{node_id_now}')
        self.graph.add_edge(node_id_last, node_id_now, data=str(event), label=str(i))

        # if loc in self.last_seen_step:
        #     node_id_last_seen_cur = (self.last_seen_step[loc], loc)
        #     self.graph.add_edge(node_id_last_seen_cur, node_id_now, label='last: ' + str(node_id_last_seen_cur[0]))
        # self.graph.nodes[id]['locs'] = self.graph.nodes[id].get('locs', '') + self.render_location(loc)+'\n'
        self.last_loc = loc
        self.last_seen_step[loc] = i
        return super().handle_crucible_event(i, event)