# -*- coding: utf-8 -*-
# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: crucible_protobuf_trace/common.proto
"""Generated protocol buffer code."""
from google.protobuf import descriptor as _descriptor
from google.protobuf import descriptor_pool as _descriptor_pool
from google.protobuf import message as _message
from google.protobuf import reflection as _reflection
from google.protobuf import symbol_database as _symbol_database
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()




DESCRIPTOR = _descriptor_pool.Default().AddSerializedFile(b'\n$crucible_protobuf_trace/common.proto\"<\n\x0eSourcePosition\x12\x0c\n\x04\x66ile\x18\x01 \x01(\t\x12\x0c\n\x04line\x18\x02 \x01(\x03\x12\x0e\n\x06\x63olumn\x18\x03 \x01(\x03\"/\n\x0e\x42inaryPosition\x12\x0c\n\x04\x66ile\x18\x01 \x01(\t\x12\x0f\n\x07\x61\x64\x64ress\x18\x02 \x01(\x03\"#\n\rOtherPosition\x12\x12\n\ndescriptor\x18\x01 \x01(\t\"\x15\n\x13UnavailablePosition\"\x12\n\x10InternalPosition\"\x9e\x01\n\x08Position\x12!\n\x06source\x18\x01 \x01(\x0b\x32\x0f.SourcePositionH\x00\x12!\n\x06\x62inary\x18\x02 \x01(\x0b\x32\x0f.BinaryPositionH\x00\x12\x1f\n\x05other\x18\x03 \x01(\x0b\x32\x0e.OtherPositionH\x00\x12%\n\x08internal\x18\x04 \x01(\x0b\x32\x11.InternalPositionH\x00\x42\x04\n\x02\x62y\"@\n\nProgramLoc\x12\x15\n\rfunction_name\x18\x01 \x01(\t\x12\x1b\n\x08position\x18\x02 \x01(\x0b\x32\t.Position\"\x13\n\x11MissingProgramLoc\"b\n\x0fMaybeProgramLoc\x12\"\n\x0bprogram_loc\x18\x01 \x01(\x0b\x32\x0b.ProgramLocH\x00\x12%\n\x07missing\x18\x02 \x01(\x0b\x32\x12.MissingProgramLocH\x00\x42\x04\n\x02\x62yb\x06proto3')



_SOURCEPOSITION = DESCRIPTOR.message_types_by_name['SourcePosition']
_BINARYPOSITION = DESCRIPTOR.message_types_by_name['BinaryPosition']
_OTHERPOSITION = DESCRIPTOR.message_types_by_name['OtherPosition']
_UNAVAILABLEPOSITION = DESCRIPTOR.message_types_by_name['UnavailablePosition']
_INTERNALPOSITION = DESCRIPTOR.message_types_by_name['InternalPosition']
_POSITION = DESCRIPTOR.message_types_by_name['Position']
_PROGRAMLOC = DESCRIPTOR.message_types_by_name['ProgramLoc']
_MISSINGPROGRAMLOC = DESCRIPTOR.message_types_by_name['MissingProgramLoc']
_MAYBEPROGRAMLOC = DESCRIPTOR.message_types_by_name['MaybeProgramLoc']
SourcePosition = _reflection.GeneratedProtocolMessageType('SourcePosition', (_message.Message,), {
  'DESCRIPTOR' : _SOURCEPOSITION,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:SourcePosition)
  })
_sym_db.RegisterMessage(SourcePosition)

BinaryPosition = _reflection.GeneratedProtocolMessageType('BinaryPosition', (_message.Message,), {
  'DESCRIPTOR' : _BINARYPOSITION,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:BinaryPosition)
  })
_sym_db.RegisterMessage(BinaryPosition)

OtherPosition = _reflection.GeneratedProtocolMessageType('OtherPosition', (_message.Message,), {
  'DESCRIPTOR' : _OTHERPOSITION,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:OtherPosition)
  })
_sym_db.RegisterMessage(OtherPosition)

UnavailablePosition = _reflection.GeneratedProtocolMessageType('UnavailablePosition', (_message.Message,), {
  'DESCRIPTOR' : _UNAVAILABLEPOSITION,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:UnavailablePosition)
  })
_sym_db.RegisterMessage(UnavailablePosition)

InternalPosition = _reflection.GeneratedProtocolMessageType('InternalPosition', (_message.Message,), {
  'DESCRIPTOR' : _INTERNALPOSITION,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:InternalPosition)
  })
_sym_db.RegisterMessage(InternalPosition)

Position = _reflection.GeneratedProtocolMessageType('Position', (_message.Message,), {
  'DESCRIPTOR' : _POSITION,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:Position)
  })
_sym_db.RegisterMessage(Position)

ProgramLoc = _reflection.GeneratedProtocolMessageType('ProgramLoc', (_message.Message,), {
  'DESCRIPTOR' : _PROGRAMLOC,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:ProgramLoc)
  })
_sym_db.RegisterMessage(ProgramLoc)

MissingProgramLoc = _reflection.GeneratedProtocolMessageType('MissingProgramLoc', (_message.Message,), {
  'DESCRIPTOR' : _MISSINGPROGRAMLOC,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:MissingProgramLoc)
  })
_sym_db.RegisterMessage(MissingProgramLoc)

MaybeProgramLoc = _reflection.GeneratedProtocolMessageType('MaybeProgramLoc', (_message.Message,), {
  'DESCRIPTOR' : _MAYBEPROGRAMLOC,
  '__module__' : 'crucible_protobuf_trace.common_pb2'
  # @@protoc_insertion_point(class_scope:MaybeProgramLoc)
  })
_sym_db.RegisterMessage(MaybeProgramLoc)

if _descriptor._USE_C_DESCRIPTORS == False:

  DESCRIPTOR._options = None
  _SOURCEPOSITION._serialized_start=40
  _SOURCEPOSITION._serialized_end=100
  _BINARYPOSITION._serialized_start=102
  _BINARYPOSITION._serialized_end=149
  _OTHERPOSITION._serialized_start=151
  _OTHERPOSITION._serialized_end=186
  _UNAVAILABLEPOSITION._serialized_start=188
  _UNAVAILABLEPOSITION._serialized_end=209
  _INTERNALPOSITION._serialized_start=211
  _INTERNALPOSITION._serialized_end=229
  _POSITION._serialized_start=232
  _POSITION._serialized_end=390
  _PROGRAMLOC._serialized_start=392
  _PROGRAMLOC._serialized_end=456
  _MISSINGPROGRAMLOC._serialized_start=458
  _MISSINGPROGRAMLOC._serialized_end=477
  _MAYBEPROGRAMLOC._serialized_start=479
  _MAYBEPROGRAMLOC._serialized_end=577
# @@protoc_insertion_point(module_scope)