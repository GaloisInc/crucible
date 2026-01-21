(declare @strcpy ((dst (Ptr 64)) (src (Ptr 64))) (Ptr 64))
(declare @read-c-string ((x Pointer)) (String Unicode))
(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @main () Unit
  (start start:
    (let z (ptr 8 0 (bv 8 0)))
    (let a (ptr 8 0 (bv 8 97))) ; 'a'

    ;; src -> ""
    ;; dst -> ['a'] (no null terminator)
    (let src0 (alloca none (bv 64 1)))
    (store none i8 src0 z)
    (let dst0 (alloca none (bv 64 1)))
    (store none i8 dst0 a)
    (let r0 (funcall @strcpy dst0 src0))
    (let d0 (load none i8 dst0))
    (let d0-off (ptr-offset 8 d0))
    (assert! (equal? d0-off (bv 8 0)) "dst[0] == 0 after strcpy(dst, '')")

    ;; src -> "a"
    ;; dst -> "b"
    (let src1 (alloca none (bv 64 2)))
    (funcall @write-c-string src1 "a")
    (let dst1 (alloca none (bv 64 2)))
    (funcall @write-c-string dst1 "b")
    (let r1 (funcall @strcpy dst1 src1))
    (let d1 (funcall @read-c-string dst1))
    (assert! (equal? d1 "a") "dst == 'a' after strcpy")

    ;; src -> "a"
    ;; dst = src
    ;; (undefined behavior)
    (funcall @strcpy src1 src1)

    (return ())))
