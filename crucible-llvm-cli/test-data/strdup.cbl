(declare @strdup ((src (Ptr 64))) (Ptr 64))
(declare @free ((ptr (Ptr 64))) Unit)
(declare @read-c-string ((x Pointer)) (String Unicode))
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:
    ;; Test 1: strdup("")
    (let src0 (alloca none (bv 64 1)))
    (funcall @write-c-string src0 "")
    (let dup0 (funcall @strdup src0))
    (let d0 (funcall @read-c-string dup0))
    (assert! (equal? d0 "") "strdup('') produces ''")
    (funcall @free dup0)

    ;; Test 2: strdup("a")
    (let src1 (alloca none (bv 64 2)))
    (funcall @write-c-string src1 "a")
    (let dup1 (funcall @strdup src1))
    (let d1 (funcall @read-c-string dup1))
    (assert! (equal? d1 "a") "strdup('a') produces 'a'")
    (funcall @free dup1)

    ;; Test 3: strdup("hello")
    (let src2 (alloca none (bv 64 6)))
    (funcall @write-c-string src2 "hello")
    (let dup2 (funcall @strdup src2))
    (let d2 (funcall @read-c-string dup2))
    (assert! (equal? d2 "hello") "strdup('hello') produces 'hello'")
    (funcall @free dup2)

    (return ())))
