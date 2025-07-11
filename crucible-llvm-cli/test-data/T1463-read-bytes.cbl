; A regression test for #1463, wherein some string-handling functions generated
; imprecise assertions that could spurriously fail because the safety assertions
; for loads of later bytes in strings didn't have access to the assumption that
; earlier bytes were nonzero.
;
; If `read-bytes` were subject to that bug, then this particular test-case
; would cause an assertion failure. In the case that the fresh byte is zero,
; then the first byte of the string is zero and `read-bytes` should immediately
; stop reading without generating further assertions. Otherwise, the byte would
; have been written to both the first and second positions of the string, so an
; uninitialized read should be impossible.

(declare @read-bytes ((x Pointer)) (Vector (Bitvector 8)))

(defun @main () Unit
  (start start:
    (let bv0 (fresh (Bitvector 8)))
    (let byte0 (ptr 8 0 bv0))

    ; create a null-terminated string of length 3
    (let beginning (alloca none (bv 64 3)))
    (let middle (ptr-add-offset beginning (bv 64 1)))
    (let end (ptr-add-offset middle (bv 64 1)))
    (let z (ptr 8 0 (bv 8 0)))
    (store none i8 end z)

    (store none i8 beginning byte0)
    (branch (equal? bv0 (bv 8 0)) end: nonzero:))
  (defblock nonzero:
    (store none i8 middle byte0)
    (jump end:))
  (defblock end:
    (let _ (funcall @read-bytes beginning))
    (return ())))
