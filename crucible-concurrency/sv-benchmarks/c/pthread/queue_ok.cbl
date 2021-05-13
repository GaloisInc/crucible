(defglobal $$queue (Vector Nat))
(defglobal $$stored (Vector Nat))
(defglobal $$head Nat)
(defglobal $$tail Nat)
(defglobal $$amount Nat)


(defglobal $$enqueue Bool)
(defglobal $$dequeue Bool)

(defglobal $$SIZE Nat)

(defun @initQ () Unit
  (registers ($i Integer))
  (start start:
    ;; "Create mutex"
    (set-global! $$head 0)
    (set-global! $$tail 0)
    (set-global! $$amount 0)
    (set-global! $$queue (vector-replicate $$SIZE 0))
    (set-global! $$stored (vector-replicate $$SIZE 0))
    (return ())))

(defun @empty ((head Nat) (tail Nat)) Bool
  (start start:
    (return (equal? head tail))))

(defun @full ((amt Nat)) Bool
  (start start:
    (return (equal? amt $$SIZE))))

;; Assuming the lock is held
(defun @enqueue ((val Nat)) Integer
  (start start:
    (set-global! $$queue (vector-set $$queue $$tail val))
    (set-global! $$amount (+ 1 $$amount))
    (set-global! $$tail (if (equal? $$tail $$SIZE)
                            1
                            (+ 1 $$tail)))
    (return 0)))

;; Assuming the lock is held
(defun @dequeue () Nat
  (start start:
    (let x (vector-get $$queue $$head))
    (set-global! $$amount (- $$amount 1))
    (set-global! $$head (if (equal? $$head $$SIZE)
                            1
                            (+ 1 $$head)))
    (return x)))


(defun @t1 ((_ Any)) Unit
  (registers ($i Nat))

  (start start:
    (set-register! $i 0)
    ;; In rust, we would acquire the mutex and then run the entire loop, hence:
    (funcall @write_effect "q")
    (jump loop:))

  (defblock loop:
    (branch (< $i $$SIZE) loop_body: done:))

  (defblock loop_body:
    (branch $$enqueue enqueue: loop:))

  (defblock enqueue:
    (let v (fresh Nat))
    (funcall @enqueue v)
    (set-global! $$stored (vector-set $$stored $i v))
    (set-register! $i (+ 1 $i))
    (jump loop:))

  (defblock done:
    (set-global! $$enqueue #f)
    (set-global! $$dequeue #t)
    (return ())))

(defun @t2 ((_ Any)) Unit
  (registers ($i Nat))

  (start start:
    (set-register! $i 0)
    (funcall @write_effect "q")
    (branch $$dequeue loop: done:))

  (defblock loop:
    (branch (< $i $$SIZE) loop_body: done:))

  (defblock loop_body:
    (set-register! $i (+ 1 $i))
    (branch $$dequeue dequeue: loop:))

  (defblock dequeue:
    (let res (funcall @dequeue))
    (assert! (equal? res (vector-get $$stored (- $i 1))) "I think this succeeds")
    (jump loop:))

  (defblock done:
    (set-global! $$enqueue (if $$dequeue #t $$enqueue))
    (set-global! $$dequeue #f)
    (return ())))

(defun @main () Unit
  (start start:
    (set-global! $$SIZE 100)
    (set-global! $$enqueue #t)
    (set-global! $$dequeue #f)
    (funcall @initQ)
    (let emp (funcall @empty $$head $$tail))
    (assert! emp "should be empty")

    (let t1 (funcall @spawn @t1 (to-any ())))
    (let t2 (funcall @spawn @t2 (to-any ())))

    (funcall @join t1)
    (funcall @join t2)

    (return ())))
