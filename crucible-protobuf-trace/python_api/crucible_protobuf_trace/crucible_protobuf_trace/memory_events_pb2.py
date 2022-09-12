# -*- coding: utf-8 -*-
# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: crucible_protobuf_trace/memory_events.proto
"""Generated protocol buffer code."""
from google.protobuf.internal import builder as _builder
from google.protobuf import descriptor as _descriptor
from google.protobuf import descriptor_pool as _descriptor_pool
from google.protobuf import symbol_database as _symbol_database
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()


from crucible_protobuf_trace import sym_expr_pb2 as crucible__protobuf__trace_dot_sym__expr__pb2
from crucible_protobuf_trace import llvm_val_pb2 as crucible__protobuf__trace_dot_llvm__val__pb2
from crucible_protobuf_trace import memory_state_pb2 as crucible__protobuf__trace_dot_memory__state__pb2


DESCRIPTOR = _descriptor_pool.Default().AddSerializedFile(b'\n+crucible_protobuf_trace/memory_events.proto\x1a&crucible_protobuf_trace/sym_expr.proto\x1a&crucible_protobuf_trace/llvm_val.proto\x1a*crucible_protobuf_trace/memory_state.proto\"\x8c\x01\n\x0fMemoryEventRead\x12\x1a\n\x04\x61\x64\x64r\x18\x01 \x01(\x0b\x32\x0c.LLVMPointer\x12 \n\nvalue_type\x18\x02 \x01(\x0b\x32\x0c.StorageType\x12\x16\n\x0e\x62yte_alignment\x18\x03 \x01(\x04\x12#\n\nread_value\x18\x04 \x01(\x0b\x32\x0f.PartialLLVMVal\"\x84\x01\n\x10MemoryEventWrite\x12\x19\n\x03\x64st\x18\x01 \x01(\x0b\x32\x0c.LLVMPointer\x12\x19\n\x03src\x18\x02 \x01(\x0b\x32\x0c.WriteSource\x12\"\n\tcondition\x18\x03 \x01(\x0b\x32\x0f.BoolExpression\x12\x16\n\x0eis_const_write\x18\x04 \x01(\x08\"\xbd\x01\n\x10MemoryEventAlloc\x12 \n\x04size\x18\x01 \x01(\x0b\x32\r.BVExpressionH\x00\x88\x01\x01\x12\x1e\n\x16\x61llocation_id_concrete\x18\x02 \x01(\x03\x12\x1c\n\x14location_description\x18\x03 \x01(\t\x12(\n\x0f\x61llocation_type\x18\x04 \x01(\x0e\x32\x0f.AllocationType\x12\x16\n\x0e\x62yte_alignment\x18\x05 \x01(\x04\x42\x07\n\x05_size\"P\n\x0fMemoryEventFree\x12\x1f\n\tptr_freed\x18\x01 \x01(\x0b\x32\x0c.LLVMPointer\x12\x1c\n\x14location_description\x18\x02 \x01(\t\"\xa2\x01\n\x0bMemoryEvent\x12 \n\x04read\x18\x01 \x01(\x0b\x32\x10.MemoryEventReadH\x00\x12\"\n\x05write\x18\x02 \x01(\x0b\x32\x11.MemoryEventWriteH\x00\x12\"\n\x05\x61lloc\x18\x03 \x01(\x0b\x32\x11.MemoryEventAllocH\x00\x12 \n\x04\x66ree\x18\x04 \x01(\x0b\x32\x10.MemoryEventFreeH\x00\x42\x07\n\x05\x65ventb\x06proto3')

_builder.BuildMessageAndEnumDescriptors(DESCRIPTOR, globals())
_builder.BuildTopDescriptorsAndMessages(DESCRIPTOR, 'crucible_protobuf_trace.memory_events_pb2', globals())
if _descriptor._USE_C_DESCRIPTORS == False:

  DESCRIPTOR._options = None
  _MEMORYEVENTREAD._serialized_start=172
  _MEMORYEVENTREAD._serialized_end=312
  _MEMORYEVENTWRITE._serialized_start=315
  _MEMORYEVENTWRITE._serialized_end=447
  _MEMORYEVENTALLOC._serialized_start=450
  _MEMORYEVENTALLOC._serialized_end=639
  _MEMORYEVENTFREE._serialized_start=641
  _MEMORYEVENTFREE._serialized_end=721
  _MEMORYEVENT._serialized_start=724
  _MEMORYEVENT._serialized_end=886
# @@protoc_insertion_point(module_scope)