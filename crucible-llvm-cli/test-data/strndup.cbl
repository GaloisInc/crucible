(declare @strndup ((src (Ptr 64)) (n (Bitvector 64))) (Ptr 64))
(declare @free ((ptr (Ptr 64))) Unit)
(declare @read-c-string ((x Pointer)) (String Unicode))
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:
    ;; Test 1: strndup("", 0)
    (let src0 (alloca none (bv 64 1)))
    (funcall @write-c-string src0 "")
    (let dup0 (funcall @strndup src0 (bv 64 0)))
    (let d0 (funcall @read-c-string dup0))
    (assert! (equal? d0 "") "strndup('', 0) produces ''")
    (funcall @free dup0)

    ;; Test 2: strndup("hello", 2)
    (let hello (alloca none (bv 64 6)))
    (funcall @write-c-string hello "hello")
    (let dup1 (funcall @strndup hello (bv 64 2)))
    (let d1 (funcall @read-c-string dup1))
    (assert! (equal? d1 "he") "strndup('hello', 2) produces 'he'")
    (funcall @free dup1)

    ;; Test 3: strndup("hello", 5)
    (let dup2 (funcall @strndup hello (bv 64 5)))
    (let d2 (funcall @read-c-string dup2))
    (assert! (equal? d2 "hello") "strndup('hello', 5) produces 'hello'")
    (funcall @free dup2)

    ;; Test 4: strndup("hello", 10) - n larger than string length
    (let dup3 (funcall @strndup hello (bv 64 10)))
    (let d3 (funcall @read-c-string dup3))
    (assert! (equal? d3 "hello") "strndup('hello', 10) produces 'hello'")
    (funcall @free dup3)

    ;; Test 5: strndup("abc", 1)
    (let src4 (alloca none (bv 64 4)))
    (funcall @write-c-string src4 "abc")
    (let dup4 (funcall @strndup src4 (bv 64 1)))
    (let d4 (funcall @read-c-string dup4))
    (assert! (equal? d4 "a") "strndup('abc', 1) produces 'a'")
    (funcall @free dup4)

    (return ())))
