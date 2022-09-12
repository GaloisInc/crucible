from .crucible_event_listener import CrucibleEventListener, LoadedBranchSplit

class PrintingListener(CrucibleEventListener):
    def on_path_split(self, path_split_data, path_id=(), **kwargs):
        splt = LoadedBranchSplit(
            self.load_PathID(path_id),
            self.load_PathID(path_split_data.continuing_path_id),
            self.load_ExpressionID(path_split_data.split_condition)
        )
        print("Path split: ", splt)

    def on_path_merge(self, path_merge_data):
        # print("Path merge: ", path_merge_data)
        pass

    def on_branch_switch(self, branch_switch_data, path_id=(), **kwargs):
        assert path_id == branch_switch_data.id_suspended
        print("Branch switch: ", self.load_BranchSwitch(branch_switch_data))

    def on_return_from_function(self, return_to_data, **kwargs):
        print("Return from: ", return_to_data)

    def on_call_function(self, call_function_data, **kwargs):
        print("Call function: (", repr(call_function_data), ")")

    def on_memory_event(self, memory_event_data, path_id=(), location=()):
        # import ipdb; ipdb.set_trace()
        location = self.load_MaybeProgramLoc(location)
        print(f"{path_id.text}: {location}: Memory event")
        kind = memory_event_data.WhichOneof("event")
        data = getattr(memory_event_data, kind)

        if kind == 'write':
            dst = self.load_LLVMPointer(data.dst)
            src = self.load_WriteSource(data.src)
            print(f"Write to {dst}: {src}")
        elif kind == 'read':
            # import ipdb; ipdb.set_trace()
            addr = self.load_LLVMPointer(data.addr)
            value_type = self.load_StorageType(data.value_type)
            byte_alignment = data.byte_alignment
            print(f"Read: {value_type=} from {addr=} with {byte_alignment=}")
        elif kind == 'alloc':
            print("Alloc: ", memory_event_data.alloc)
        elif kind == 'free':
            print("Free: ", memory_event_data.free)
        else:
            assert False, f"unknown memory event kind: {kind}"