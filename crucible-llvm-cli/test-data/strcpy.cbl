(declare @strcpy ((dst (Ptr 64)) (src (Ptr 64))) (Ptr 64))

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
    (store none i8 src1 a)
    (let src1-1 (ptr-add-offset src1 (bv 64 1)))
    (store none i8 src1-1 z)
    (let dst1 (alloca none (bv 64 2)))
    (let b (ptr 8 0 (bv 8 98))) ; 'b'
    (store none i8 dst1 b)
    (let dst1-1 (ptr-add-offset dst1 (bv 64 1)))
    (store none i8 dst1-1 b)
    (let r1 (funcall @strcpy dst1 src1))
    (let d1-0 (load none i8 dst1))
    (let d1-1 (load none i8 dst1-1))
    (let d1-0-off (ptr-offset 8 d1-0))
    (let d1-1-off (ptr-offset 8 d1-1))
    (assert! (equal? d1-0-off (bv 8 97)) "dst[0] == 'a' after strcpy")
    (assert! (equal? d1-1-off (bv 8 0)) "dst[1] == 0 after strcpy")

    ;; src -> "a"
    ;; dst = src
    ;; (undefined behavior)
    (funcall @strcpy src1 src1)

    (return ())))
