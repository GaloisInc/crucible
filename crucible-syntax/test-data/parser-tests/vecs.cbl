(defun @vec-test ((n Nat) (x Integer)) (Vector (String Unicode))
  (registers
    ($res (Vector (String Unicode))))
  (start first:
    (set-register! $res
        (vector "hello" "this" "is" "a" "vector"))
    (let foo (the (Vector (String Unicode)) (vector-replicate n (show x))))
    (let a (vector-empty? (the (Vector Integer) (vector))))
    (let b (vector-empty? (vector #t #f #f #t)))
    (let done $res)
    (let c (vector-size done))
    (let d (vector-size foo))
    (let e (vector-get done 3))
    (let f (vector-set done 3 "isn't"))
    (let g (vector-cons "well" f))
    (let h (vector-replicate 132 "."))
    (let i (vector-cons 12 (vector (vector-size done) 9)))
    (return $res)))
