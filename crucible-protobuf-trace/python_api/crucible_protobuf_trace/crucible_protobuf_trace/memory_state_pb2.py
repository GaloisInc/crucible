# -*- coding: utf-8 -*-
# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: crucible_protobuf_trace/memory_state.proto
"""Generated protocol buffer code."""
from google.protobuf.internal import builder as _builder
from google.protobuf import descriptor as _descriptor
from google.protobuf import descriptor_pool as _descriptor_pool
from google.protobuf import symbol_database as _symbol_database
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()


from crucible_protobuf_trace import sym_expr_pb2 as crucible__protobuf__trace_dot_sym__expr__pb2
from crucible_protobuf_trace import llvm_val_pb2 as crucible__protobuf__trace_dot_llvm__val__pb2


DESCRIPTOR = _descriptor_pool.Default().AddSerializedFile(b'\n*crucible_protobuf_trace/memory_state.proto\x1a&crucible_protobuf_trace/sym_expr.proto\x1a&crucible_protobuf_trace/llvm_val.proto\"\xa6\x01\n\tAllocInfo\x12#\n\nalloc_type\x18\x01 \x01(\x0e\x32\x0f.AllocationType\x12 \n\x04size\x18\x02 \x01(\x0b\x32\r.BVExpressionH\x00\x88\x01\x01\x12\x1f\n\nmutability\x18\x03 \x01(\x0e\x32\x0b.Mutability\x12\x11\n\tAlignment\x18\x04 \x01(\x05\x12\x15\n\rlocation_name\x18\x05 \x01(\tB\x07\n\x05_size\"\x87\x01\n\x0eMemStateAllocs\x12\x35\n\x0b\x61llocations\x18\x01 \x03(\x0b\x32 .MemStateAllocs.AllocationsEntry\x1a>\n\x10\x41llocationsEntry\x12\x0b\n\x03key\x18\x01 \x01(\x03\x12\x19\n\x05value\x18\x02 \x01(\x0b\x32\n.AllocInfo:\x02\x38\x01\"F\n\x0cMemStateFree\x12\x1f\n\x07\x62lockId\x18\x01 \x01(\x0b\x32\x0e.IntExpression\x12\x15\n\rlocation_name\x18\x02 \x01(\t\"e\n\x12MemStateAllocMerge\x12\x1d\n\x04\x63ond\x18\x01 \x01(\x0b\x32\x0f.BoolExpression\x12\x17\n\x03lhs\x18\x02 \x01(\x0b\x32\n.MemAllocs\x12\x17\n\x03rhs\x18\x03 \x01(\x0b\x32\n.MemAllocs\"z\n\x08MemAlloc\x12!\n\x06\x61llocs\x18\x01 \x01(\x0b\x32\x0f.MemStateAllocsH\x00\x12\x1d\n\x04\x66ree\x18\x02 \x01(\x0b\x32\r.MemStateFreeH\x00\x12$\n\x05merge\x18\x03 \x01(\x0b\x32\x13.MemStateAllocMergeH\x00\x42\x06\n\x04kind\"&\n\tMemAllocs\x12\x19\n\x06\x61llocs\x18\x01 \x03(\x0b\x32\t.MemAlloc\"I\n\x0eMemWriteSingle\x12\x19\n\x03ptr\x18\x01 \x01(\x0b\x32\x0c.LLVMPointer\x12\x1c\n\x06source\x18\x02 \x01(\x0b\x32\x0c.WriteSource\"`\n\rMemWriteMerge\x12\x1d\n\x04\x63ond\x18\x01 \x01(\x0b\x32\x0f.BoolExpression\x12\x17\n\x03lhs\x18\x02 \x01(\x0b\x32\n.MemWrites\x12\x17\n\x03rhs\x18\x03 \x01(\x0b\x32\n.MemWrites\"V\n\x08MemWrite\x12!\n\x06single\x18\x01 \x01(\x0b\x32\x0f.MemWriteSingleH\x00\x12\x1f\n\x05merge\x18\x02 \x01(\x0b\x32\x0e.MemWriteMergeH\x00\x42\x06\n\x04kind\"/\n\x12MemWritesChunkFlat\x12\x19\n\x06writes\x18\x01 \x03(\x0b\x32\t.MemWrite\"\x85\x01\n\x15MemWritesChunkIndexed\x12\x32\n\x06writes\x18\x01 \x03(\x0b\x32\".MemWritesChunkIndexed.WritesEntry\x1a\x38\n\x0bWritesEntry\x12\x0b\n\x03key\x18\x01 \x01(\x03\x12\x18\n\x05value\x18\x02 \x01(\x0b\x32\t.MemWrite:\x02\x38\x01\"h\n\x0eMemWritesChunk\x12#\n\x04\x66lat\x18\x01 \x01(\x0b\x32\x13.MemWritesChunkFlatH\x00\x12)\n\x07indexed\x18\x02 \x01(\x0b\x32\x16.MemWritesChunkIndexedH\x00\x42\x06\n\x04kind\",\n\tMemWrites\x12\x1f\n\x06\x63hunks\x18\x01 \x03(\x0b\x32\x0f.MemWritesChunk\"I\n\nMemChanges\x12\x1f\n\x0b\x61llocations\x18\x01 \x01(\x0b\x32\n.MemAllocs\x12\x1a\n\x06writes\x18\x02 \x01(\x0b\x32\n.MemWrites\"P\n\x08MemEmpty\x12\x12\n\nnum_allocs\x18\x01 \x01(\x03\x12\x12\n\nnum_writes\x18\x02 \x01(\x03\x12\x1c\n\x07\x63hanges\x18\x03 \x01(\x0b\x32\x0b.MemChanges\"\x88\x01\n\rMemStackFrame\x12\x12\n\nnum_allocs\x18\x01 \x01(\x03\x12\x12\n\nnum_writes\x18\x02 \x01(\x03\x12\x12\n\nframe_name\x18\x03 \x01(\t\x12\x1c\n\x07\x63hanges\x18\x04 \x01(\x0b\x32\x0b.MemChanges\x12\x1d\n\nbase_state\x18\x05 \x01(\x0b\x32\t.MemState\"u\n\x0eMemBranchFrame\x12\x12\n\nnum_allocs\x18\x01 \x01(\x03\x12\x12\n\nnum_writes\x18\x02 \x01(\x03\x12\x1c\n\x07\x63hanges\x18\x03 \x01(\x0b\x32\x0b.MemChanges\x12\x1d\n\nbase_state\x18\x04 \x01(\x0b\x32\t.MemState\"~\n\x08MemState\x12\x1a\n\x05\x65mpty\x18\x01 \x01(\x0b\x32\t.MemEmptyH\x00\x12%\n\x0bstack_frame\x18\x02 \x01(\x0b\x32\x0e.MemStackFrameH\x00\x12\'\n\x0c\x62ranch_frame\x18\x03 \x01(\x0b\x32\x0f.MemBranchFrameH\x00\x42\x06\n\x04kind\"@\n\x03Mem\x12\x1f\n\nendianness\x18\x01 \x01(\x0e\x32\x0b.Endianness\x12\x18\n\x05state\x18\x02 \x01(\x0b\x32\t.MemState\"g\n\x12WriteSourceMemCopy\x12\x1a\n\x04\x61\x64\x64r\x18\x01 \x01(\x0b\x32\x0c.LLVMPointer\x12\x1b\n\x04size\x18\x02 \x01(\x0b\x32\r.BVExpression\x12\x18\n\x10require_disjoint\x18\x03 \x01(\x08\"L\n\x11WriteSourceMemSet\x12\x1a\n\x03val\x18\x01 \x01(\x0b\x32\r.BVExpression\x12\x1b\n\x04size\x18\x02 \x01(\x0b\x32\r.BVExpression\"j\n\x13WriteSourceMemStore\x12\x17\n\x05value\x18\x01 \x01(\x0b\x32\x08.LLVMVal\x12\"\n\x0cstorage_type\x18\x02 \x01(\x0b\x32\x0c.StorageType\x12\x16\n\x0e\x62yte_alignment\x18\x03 \x01(\x04\"\x1a\n\x18WriteSourceMemArrayStore\"H\n\x18WriteSourceMemInvalidate\x12\x0f\n\x07message\x18\x01 \x01(\t\x12\x1b\n\x04size\x18\x02 \x01(\x0b\x32\r.BVExpression\"\x8a\x02\n\x0bWriteSource\x12+\n\x0csrc_mem_copy\x18\x01 \x01(\x0b\x32\x13.WriteSourceMemCopyH\x00\x12)\n\x0bsrc_mem_set\x18\x02 \x01(\x0b\x32\x12.WriteSourceMemSetH\x00\x12-\n\rsrc_mem_store\x18\x03 \x01(\x0b\x32\x14.WriteSourceMemStoreH\x00\x12\x38\n\x13src_mem_array_store\x18\x04 \x01(\x0b\x32\x19.WriteSourceMemArrayStoreH\x00\x12\x33\n\x0esrc_invalidate\x18\x05 \x01(\x0b\x32\x19.WriteSourceMemInvalidateH\x00\x42\x05\n\x03src*1\n\x0e\x41llocationType\x12\x08\n\x04HEAP\x10\x00\x12\t\n\x05STACK\x10\x01\x12\n\n\x06GLOBAL\x10\x02*(\n\nMutability\x12\x0b\n\x07MUTABLE\x10\x00\x12\r\n\tIMMUTABLE\x10\x01*/\n\nEndianness\x12\x11\n\rLITTLE_ENDIAN\x10\x00\x12\x0e\n\nBIG_ENDIAN\x10\x01\x62\x06proto3')

_builder.BuildMessageAndEnumDescriptors(DESCRIPTOR, globals())
_builder.BuildTopDescriptorsAndMessages(DESCRIPTOR, 'crucible_protobuf_trace.memory_state_pb2', globals())
if _descriptor._USE_C_DESCRIPTORS == False:

  DESCRIPTOR._options = None
  _MEMSTATEALLOCS_ALLOCATIONSENTRY._options = None
  _MEMSTATEALLOCS_ALLOCATIONSENTRY._serialized_options = b'8\001'
  _MEMWRITESCHUNKINDEXED_WRITESENTRY._options = None
  _MEMWRITESCHUNKINDEXED_WRITESENTRY._serialized_options = b'8\001'
  _ALLOCATIONTYPE._serialized_start=2641
  _ALLOCATIONTYPE._serialized_end=2690
  _MUTABILITY._serialized_start=2692
  _MUTABILITY._serialized_end=2732
  _ENDIANNESS._serialized_start=2734
  _ENDIANNESS._serialized_end=2781
  _ALLOCINFO._serialized_start=127
  _ALLOCINFO._serialized_end=293
  _MEMSTATEALLOCS._serialized_start=296
  _MEMSTATEALLOCS._serialized_end=431
  _MEMSTATEALLOCS_ALLOCATIONSENTRY._serialized_start=369
  _MEMSTATEALLOCS_ALLOCATIONSENTRY._serialized_end=431
  _MEMSTATEFREE._serialized_start=433
  _MEMSTATEFREE._serialized_end=503
  _MEMSTATEALLOCMERGE._serialized_start=505
  _MEMSTATEALLOCMERGE._serialized_end=606
  _MEMALLOC._serialized_start=608
  _MEMALLOC._serialized_end=730
  _MEMALLOCS._serialized_start=732
  _MEMALLOCS._serialized_end=770
  _MEMWRITESINGLE._serialized_start=772
  _MEMWRITESINGLE._serialized_end=845
  _MEMWRITEMERGE._serialized_start=847
  _MEMWRITEMERGE._serialized_end=943
  _MEMWRITE._serialized_start=945
  _MEMWRITE._serialized_end=1031
  _MEMWRITESCHUNKFLAT._serialized_start=1033
  _MEMWRITESCHUNKFLAT._serialized_end=1080
  _MEMWRITESCHUNKINDEXED._serialized_start=1083
  _MEMWRITESCHUNKINDEXED._serialized_end=1216
  _MEMWRITESCHUNKINDEXED_WRITESENTRY._serialized_start=1160
  _MEMWRITESCHUNKINDEXED_WRITESENTRY._serialized_end=1216
  _MEMWRITESCHUNK._serialized_start=1218
  _MEMWRITESCHUNK._serialized_end=1322
  _MEMWRITES._serialized_start=1324
  _MEMWRITES._serialized_end=1368
  _MEMCHANGES._serialized_start=1370
  _MEMCHANGES._serialized_end=1443
  _MEMEMPTY._serialized_start=1445
  _MEMEMPTY._serialized_end=1525
  _MEMSTACKFRAME._serialized_start=1528
  _MEMSTACKFRAME._serialized_end=1664
  _MEMBRANCHFRAME._serialized_start=1666
  _MEMBRANCHFRAME._serialized_end=1783
  _MEMSTATE._serialized_start=1785
  _MEMSTATE._serialized_end=1911
  _MEM._serialized_start=1913
  _MEM._serialized_end=1977
  _WRITESOURCEMEMCOPY._serialized_start=1979
  _WRITESOURCEMEMCOPY._serialized_end=2082
  _WRITESOURCEMEMSET._serialized_start=2084
  _WRITESOURCEMEMSET._serialized_end=2160
  _WRITESOURCEMEMSTORE._serialized_start=2162
  _WRITESOURCEMEMSTORE._serialized_end=2268
  _WRITESOURCEMEMARRAYSTORE._serialized_start=2270
  _WRITESOURCEMEMARRAYSTORE._serialized_end=2296
  _WRITESOURCEMEMINVALIDATE._serialized_start=2298
  _WRITESOURCEMEMINVALIDATE._serialized_end=2370
  _WRITESOURCE._serialized_start=2373
  _WRITESOURCE._serialized_end=2639
# @@protoc_insertion_point(module_scope)