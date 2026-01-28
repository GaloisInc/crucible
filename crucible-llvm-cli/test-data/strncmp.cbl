(declare @strncmp ((s1 (Ptr 64)) (s2 (Ptr 64)) (n (Bitvector 64))) (Bitvector 32))
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:
    (let hello1 (alloca none (bv 64 6)))
    (let hello2 (alloca none (bv 64 6)))
    (funcall @write-c-string hello1 "Hello")
    (funcall @write-c-string hello2 "Hello")

    (let abc (alloca none (bv 64 4)))
    (funcall @write-c-string abc "abc")

    (let xyz (alloca none (bv 64 4)))
    (funcall @write-c-string xyz "xyz")

    (let abcdef (alloca none (bv 64 7)))
    (funcall @write-c-string abcdef "abcdef")

    (let abcxyz (alloca none (bv 64 7)))
    (funcall @write-c-string abcxyz "abcxyz")

    (let empty (alloca none (bv 64 1)))
    (funcall @write-c-string empty "")

    ;; strncmp of equal strings
    (let r1 (funcall @strncmp hello1 hello2 (bv 64 5)))
    (assert! (equal? r1 (bv 32 0)) "strncmp('Hello', 'Hello', 5) == 0")

    ;; strncmp with length 0 should always return 0
    (let r2 (funcall @strncmp abc xyz (bv 64 0)))
    (assert! (equal? r2 (bv 32 0)) "strncmp with length 0 returns 0")

    ;; strncmp with partial comparison - equal prefix
    (let r3 (funcall @strncmp abcdef abcxyz (bv 64 3)))
    (assert! (equal? r3 (bv 32 0)) "strncmp('abcdef', 'abcxyz', 3) == 0")

    ;; strncmp with partial comparison - different within range
    (let r4 (funcall @strncmp abcdef abcxyz (bv 64 5)))
    (assert! (<$ r4 (bv 32 0)) "strncmp('abcdef', 'abcxyz', 5) < 0")

    ;; strncmp stops at null terminator even if length is larger
    (let r5 (funcall @strncmp abc abc (bv 64 100)))
    (assert! (equal? r5 (bv 32 0)) "strncmp('abc', 'abc', 100) == 0")

    ;; strncmp with aliased strings
    (let r6 (funcall @strncmp hello1 hello1 (bv 64 5)))
    (assert! (equal? r6 (bv 32 0)) "strncmp(ptr, ptr, n) == 0")

    ;; strncmp with empty strings
    (let empty2 (alloca none (bv 64 1)))
    (funcall @write-c-string empty2 "")
    (let r7 (funcall @strncmp empty empty2 (bv 64 10)))
    (assert! (equal? r7 (bv 32 0)) "strncmp('', '', 10) == 0")

    ;; strncmp stops at null in first string
    (let r8 (funcall @strncmp abc abcdef (bv 64 10)))
    (assert! (<$ r8 (bv 32 0)) "strncmp('abc', 'abcdef', 10) < 0")

    ;; strncmp stops at null in second string
    (let r9 (funcall @strncmp abcdef abc (bv 64 10)))
    (assert! (<$ (bv 32 0) r9) "strncmp('abcdef', 'abc', 10) > 0")

    ;; strncmp compares exactly n characters when no null
    (let hel (alloca none (bv 64 4)))
    (funcall @write-c-string hel "Hel")
    (let r10 (funcall @strncmp hello1 hel (bv 64 3)))
    (assert! (equal? r10 (bv 32 0)) "strncmp('Hello', 'Hel', 3) == 0")

    (return ())))
