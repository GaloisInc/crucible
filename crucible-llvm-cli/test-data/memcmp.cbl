(declare @memcmp ((s1 (Ptr 64)) (s2 (Ptr 64)) (n (Bitvector 64))) (Bitvector 32))
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:
    ;; memcmp of equal strings
    (let hello1 (alloca none (bv 64 6)))
    (let hello2 (alloca none (bv 64 6)))
    (funcall @write-c-string hello1 "Hello")
    (funcall @write-c-string hello2 "Hello")
    (let r1 (funcall @memcmp hello1 hello2 (bv 64 5)))
    (assert! (equal? r1 (bv 32 0)) "memcmp('Hello', 'Hello', 5) == 0")

    ;; memcmp with length 0 should always return 0
    (let abc (alloca none (bv 64 4)))
    (let xyz (alloca none (bv 64 4)))
    (funcall @write-c-string abc "abc")
    (funcall @write-c-string xyz "xyz")
    (let r2 (funcall @memcmp abc xyz (bv 64 0)))
    (assert! (equal? r2 (bv 32 0)) "memcmp with length 0 returns 0")

    ;; memcmp with partial comparison - equal prefix
    (let hello (alloca none (bv 64 7)))
    (let help (alloca none (bv 64 7)))
    (funcall @write-c-string hello "Hello!")
    (funcall @write-c-string help "Help!!")
    ;; Compare only first 3 bytes - should be equal
    (let r3 (funcall @memcmp hello help (bv 64 3)))
    (assert! (equal? r3 (bv 32 0)) "memcmp('Hello!', 'Help!!', 3) == 0")

    ;; memcmp with single byte - equal
    (let a1 (alloca none (bv 64 1)))
    (let a2 (alloca none (bv 64 1)))
    (let a (ptr 8 0 (bv 8 97))) ; 'a'
    (store none i8 a1 a)
    (store none i8 a2 a)
    (let r4 (funcall @memcmp a1 a2 (bv 64 1)))
    (assert! (equal? r4 (bv 32 0)) "memcmp('a', 'a', 1) == 0")

    ;; memcmp with aliased strings (same pointer)
    (let aliased (alloca none (bv 64 6)))
    (funcall @write-c-string aliased "Hello")
    (let r6 (funcall @memcmp aliased aliased (bv 64 5)))
    (assert! (equal? r6 (bv 32 0)) "memcmp(ptr, ptr, n) == 0")

    ;; memcmp('a', 'b') returns negative value
    (let a4 (alloca none (bv 64 1)))
    (let b2 (alloca none (bv 64 1)))
    (let byte-a2 (ptr 8 0 (bv 8 97))) ; 'a'
    (let byte-b2 (ptr 8 0 (bv 8 98))) ; 'b'
    (store none i8 a4 byte-a2)
    (store none i8 b2 byte-b2)
    (let r7 (funcall @memcmp a4 b2 (bv 64 1)))
    (assert! (<$ r7 (bv 32 0)) "memcmp('a', 'b', 1) < 0")

    ;; memcmp('b', 'a') returns positive value
    (let b3 (alloca none (bv 64 1)))
    (let a5 (alloca none (bv 64 1)))
    (let byte-b3 (ptr 8 0 (bv 8 98))) ; 'b'
    (let byte-a3 (ptr 8 0 (bv 8 97))) ; 'a'
    (store none i8 b3 byte-b3)
    (store none i8 a5 byte-a3)
    (let r8 (funcall @memcmp b3 a5 (bv 64 1)))
    (assert! (<$ (bv 32 0) r8) "memcmp('b', 'a', 1) > 0")

    ;; memcmp with null bytes in the middle - equal
    ;; This tests that memcmp compares the full length, not stopping at null
    (let buf1 (alloca none (bv 64 3)))
    (let buf2 (alloca none (bv 64 3)))
    ;; Store "a\0b" in buf1
    (let byte-a (ptr 8 0 (bv 8 97)))   ; 'a'
    (let byte-0 (ptr 8 0 (bv 8 0)))    ; '\0'
    (let byte-b (ptr 8 0 (bv 8 98)))   ; 'b'
    (store none i8 buf1 byte-a)
    (let buf1-plus-1 (ptr-add-offset buf1 (bv 64 1)))
    (store none i8 buf1-plus-1 byte-0)
    (let buf1-plus-2 (ptr-add-offset buf1 (bv 64 2)))
    (store none i8 buf1-plus-2 byte-b)
    ;; Store "a\0b" in buf2
    (store none i8 buf2 byte-a)
    (let buf2-plus-1 (ptr-add-offset buf2 (bv 64 1)))
    (store none i8 buf2-plus-1 byte-0)
    (let buf2-plus-2 (ptr-add-offset buf2 (bv 64 2)))
    (store none i8 buf2-plus-2 byte-b)
    (let r9 (funcall @memcmp buf1 buf2 (bv 64 3)))
    (assert! (equal? r9 (bv 32 0)) "memcmp('a\\0b', 'a\\0b', 3) == 0")

    ;; memcmp with null bytes in the middle - different
    ;; Compare "a\0b" with "a\0c" - should differ at the third byte
    (let buf3 (alloca none (bv 64 3)))
    (let byte-c (ptr 8 0 (bv 8 99)))   ; 'c'
    (store none i8 buf3 byte-a)
    (let buf3-plus-1 (ptr-add-offset buf3 (bv 64 1)))
    (store none i8 buf3-plus-1 byte-0)
    (let buf3-plus-2 (ptr-add-offset buf3 (bv 64 2)))
    (store none i8 buf3-plus-2 byte-c)
    (let r10 (funcall @memcmp buf1 buf3 (bv 64 3)))
    (assert! (<$ r10 (bv 32 0)) "memcmp('a\\0b', 'a\\0c', 3) < 0")

    (return ())))
