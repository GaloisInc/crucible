;; exercise sequence operations

(defun @seq-test ((x Integer)) (Sequence Integer)
  (start go:
    (let s0 (seq-nil Integer))
    (let s1 (seq-cons x s0))
    (let s2 (seq-cons x s1))
    (let s3 (seq-append s1 s2))
    (let e  (seq-nil? s0))
    (let n  (seq-length s3))
    (let h  (seq-head s3))
    (let t  (seq-tail s3))
    (let u  (seq-uncons s3))
    (return s3)))
