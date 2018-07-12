(defun @vec-test ((n Nat) (x Integer)) (Vector String)
  (registers
    ($res (Vector String)))
  (start first:
    (set-register! $res (the (Vector String) (vector "hello" "this" "is" "a" "vector")))
    (let foo (the (Vector String) (vector-replicate n (show x))))
    (let a (vector-empty? (the (Vector Bool) (vector))))
    (let b (vector-empty? (the (Vector Bool) (vector #t #f #f #t))))
    (let c (vector-size $res))
    (let d (vector-size foo))
    (let e (vector-get $res 3))
    (let f (vector-set $res 3 "isn't"))
    (let done $res)
    (return done)))
    
