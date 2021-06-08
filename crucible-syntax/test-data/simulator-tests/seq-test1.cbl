(defun @main () Unit
  (start start:
    (let n (the (Sequence Nat) seq-nil))
    (assert! (seq-nil? n) "nil test")
    (assert! (equal? 0 (seq-length n)) "nil length test")

    (let s1 (seq-cons 5 n))

    (assert! (not (seq-nil? s1)) "cons test")
    (assert! (equal? 1 (seq-length s1)) "cons length test")

    (let v (from-just (seq-head s1) "head s1"))
    (let t (from-just (seq-tail s1) "tail s1"))
    (let u (from-just (seq-uncons s1) "uncons s1"))

    (let v2 (get-field 0 u))
    (let t2 (get-field 1 u))

    (assert! (equal? 5 v) "head value test")
    (assert! (equal? v v2) "head equal test")
    (assert! (seq-nil? t) "tail nil test")
    (assert! (seq-nil? t2) "uncons tail nil test")

    (let s2 (seq-append s1 (seq-cons 42 (seq-nil Nat))))
    (assert! (equal? 2 (seq-length s2)) "append length")
    (assert! (not (seq-nil? s2)) "append non-nil")

    (let v3 (from-just (seq-head (from-just (seq-tail s2) "cdr s2")) "cadr s2"))
    (assert! (equal? 42 v3) "cadr s2 test")

    (return ()))
)
