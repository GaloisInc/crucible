%struct.S = type { i32, i32, [0 x i8] }

define i32 @main() {
  ; Allocate a ptr large enough to hold a %struct.S value.
  %sp = alloca %struct.S

  ; Write a %struct.S value to the pointer whose fields are all zeroes.
  store %struct.S { i32 0, i32 0, [0 x i8] [] }, ptr %sp

  ; Write 0 to the second field of the struct (at offset 1).
  %sp2 = getelementptr inbounds %struct.S, ptr %sp, i32 0, i32 1
  store i32 0, ptr %sp2, align 4

  ; Load a %struct.S value from the pointer after the write above.
  %x = load %struct.S, ptr %sp, align 4

  ret i32 0
}
